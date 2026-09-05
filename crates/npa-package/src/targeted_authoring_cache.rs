//! Content-addressed support-cache keys for targeted package authoring.
//!
//! The key and closure formats in this module contain semantic artifact and
//! toolchain identity only. Selection seeds, graph indices, paths, timestamps,
//! diagnostics, and host observations are deliberately absent.

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    fmt,
};

use npa_cert::Name;

use crate::{
    artifacts::{hash_json, json_array, json_object_in_order, json_string},
    build_check_cache::TARGETED_AUTHORING_CACHE_LIMITS_V1,
    graph::{ResolvedModuleImport, ResolvedModuleImportKind},
    hash::{format_package_hash, package_file_hash, PackageHash},
    manifest::{PackageManifest, PackageModule, PackageModuleIdentity, PackageVersion},
    name::PackageId,
    validate::ValidatedPackageManifest,
};

mod context;
pub use context::*;

/// Canonical schema for the support-cache key preimage.
pub const PACKAGE_TARGETED_AUTHORING_SUPPORT_KEY_SCHEMA: &str =
    "npa.package.targeted_authoring_support_key.v0.1";
/// Canonical schema for the cached reconstructed authoring context payload.
pub const PACKAGE_TARGETED_AUTHORING_SUPPORT_CONTEXT_SCHEMA: &str =
    "npa.package.targeted_authoring_support_context.v0.1";
/// Domain separator for index-neutral module identities.
pub const PACKAGE_TARGETED_AUTHORING_MODULE_IDENTITY_DOMAIN: &str =
    "npa.package.targeted_authoring_module_identity.v0.1";
/// Domain separator for ordered dependency-closure commitments.
pub const PACKAGE_TARGETED_AUTHORING_SUPPORT_CLOSURE_DOMAIN: &str =
    "npa.package.targeted_authoring_support_closure.v0.1";
/// Domain separator for external dependency leaves.
pub const PACKAGE_TARGETED_AUTHORING_EXTERNAL_LEAF_DOMAIN: &str =
    "npa.package.targeted_authoring_external_leaf.v0.1";

/// Exact toolchain identity shared by support-cache keys in one invocation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TargetedAuthoringToolchainIdentity {
    /// SHA-256 of the exact running executable bytes.
    pub executable_hash: PackageHash,
    /// CLI authoring ABI profile.
    pub cli_authoring_abi: String,
    /// frontend authoring ABI profile.
    pub frontend_authoring_abi: String,
    /// producer authoring ABI profile.
    pub producer_authoring_abi: String,
    /// kernel authoring ABI profile.
    pub kernel_authoring_abi: String,
}

/// Invocation-independent semantic context used to construct module keys.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TargetedAuthoringSupportKeyContext {
    /// Exact executable and authoring ABI identities.
    pub toolchain: TargetedAuthoringToolchainIdentity,
    /// Producer profile used when a module has no manifest override.
    pub default_producer_profile: String,
    /// Normalized semantic compile and resource options.
    pub semantic_compiler_options: Vec<String>,
    /// Commitment to the effective axiom policy.
    pub axiom_policy_hash: PackageHash,
    /// Source-interface schema reconstructed by the payload.
    pub source_interface_schema: String,
    /// Reconstruction algorithm version.
    pub source_interface_reconstruction_version: String,
}

/// One exact canonical certificate import-table row.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TargetedAuthoringCertificateImportIdentity {
    /// Imported module name.
    pub module: Name,
    /// Required canonical export hash.
    pub export_hash: PackageHash,
    /// Optional canonical certificate hash exactly as encoded.
    pub certificate_hash: Option<PackageHash>,
}

/// Observed semantic identities for one local module's current artifacts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TargetedAuthoringLocalModuleInput {
    /// Module name used for index-neutral matching.
    pub module: Name,
    /// SHA-256 of the current source bytes.
    pub current_source_hash: PackageHash,
    /// SHA-256 of the current certificate-file bytes.
    pub current_certificate_file_hash: PackageHash,
    /// Actual export hash decoded from the canonical certificate.
    pub actual_export_hash: PackageHash,
    /// Actual axiom-report hash decoded from the canonical certificate.
    pub actual_axiom_report_hash: PackageHash,
    /// Actual canonical certificate hash.
    pub actual_certificate_hash: PackageHash,
    /// Exact canonical certificate import table in encoded order.
    pub certificate_imports: Vec<TargetedAuthoringCertificateImportIdentity>,
}

/// Observed identity of one hash-pinned external certificate dependency.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TargetedAuthoringExternalModuleInput {
    /// External module name used for index-neutral matching.
    pub module: Name,
    /// SHA-256 of the current vendored certificate-file bytes.
    pub current_certificate_file_hash: PackageHash,
    /// Actual export hash decoded from that certificate.
    pub actual_export_hash: PackageHash,
    /// Actual canonical certificate hash decoded from that certificate.
    pub actual_certificate_hash: PackageHash,
}

/// Index-neutral identity of one direct resolved dependency artifact.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TargetedAuthoringDependencyIdentity {
    /// Dependency package id.
    pub package: PackageId,
    /// Exact dependency package version.
    pub version: PackageVersion,
    /// Dependency module name.
    pub module: Name,
    /// Domain-separated, index-neutral module identity.
    pub module_identity: PackageHash,
    /// Exact current dependency certificate-file hash.
    pub certificate_file_hash: PackageHash,
    /// Manifest-pinned dependency export hash.
    pub expected_export_hash: PackageHash,
    /// Manifest-pinned dependency canonical certificate hash.
    pub expected_certificate_hash: PackageHash,
    /// Actual dependency export hash.
    pub actual_export_hash: PackageHash,
    /// Actual canonical dependency certificate hash.
    pub actual_certificate_hash: PackageHash,
}

/// Complete semantic preimage for one targeted-authoring support-cache key.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TargetedAuthoringSupportKeyInput {
    /// Exact executable and ABI identity.
    pub toolchain: TargetedAuthoringToolchainIdentity,
    /// Owning package id.
    pub package: PackageId,
    /// Exact owning package version.
    pub version: PackageVersion,
    /// Core language profile.
    pub core_spec: String,
    /// Kernel profile.
    pub kernel_profile: String,
    /// Canonical certificate format profile.
    pub certificate_format: String,
    /// Checker profile.
    pub checker_profile: String,
    /// Producer profile effective for this module.
    pub producer_profile: String,
    /// Normalized semantic compile and resource options.
    pub semantic_compiler_options: Vec<String>,
    /// Commitment to the effective axiom policy.
    pub axiom_policy_hash: PackageHash,
    /// Module name.
    pub module: Name,
    /// Domain-separated, index-neutral module identity.
    pub module_identity: PackageHash,
    /// SHA-256 of current source bytes.
    pub current_source_hash: PackageHash,
    /// Manifest-pinned expected source hash.
    pub expected_source_hash: PackageHash,
    /// SHA-256 of current certificate-file bytes.
    pub current_certificate_file_hash: PackageHash,
    /// Manifest-pinned expected certificate-file hash.
    pub expected_certificate_file_hash: PackageHash,
    /// Manifest-pinned expected export hash.
    pub expected_export_hash: PackageHash,
    /// Manifest-pinned expected axiom-report hash.
    pub expected_axiom_report_hash: PackageHash,
    /// Manifest-pinned expected canonical certificate hash.
    pub expected_certificate_hash: PackageHash,
    /// Actual export hash from the canonical certificate.
    pub actual_export_hash: PackageHash,
    /// Actual axiom-report hash from the canonical certificate.
    pub actual_axiom_report_hash: PackageHash,
    /// Actual canonical certificate hash.
    pub actual_certificate_hash: PackageHash,
    /// Exact canonical certificate import table in semantic order.
    pub certificate_imports: Vec<TargetedAuthoringCertificateImportIdentity>,
    /// Ordered Merkle commitment to the exact dependency closure.
    pub dependency_closure_commitment: PackageHash,
    /// Manifest direct Human imports in manifest semantic order.
    pub manifest_human_imports: Vec<crate::graph::ResolvedModuleImportIdentity>,
    /// Reconstructed source-interface schema.
    pub source_interface_schema: String,
    /// Reconstruction algorithm version.
    pub source_interface_reconstruction_version: String,
}

/// One planned support-cache key and its closure commitment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TargetedAuthoringSupportPlanEntry {
    /// Complete `sha256:` cache key.
    pub cache_key: String,
    /// Ordered dependency-closure commitment included in the key.
    pub closure_commitment: PackageHash,
}

/// Instrumentation proving bounded single-pass closure construction.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TargetedAuthoringSupportPlanWork {
    /// Unique local and external vertices whose commitments were constructed.
    pub vertex_visits: usize,
    /// Direct dependency edges examined.
    pub edge_visits: usize,
    /// Unique local and external closure commitments constructed.
    pub closure_commitments: usize,
    /// Local support keys constructed.
    pub support_keys: usize,
}

/// Planned keys for the selected local support closure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TargetedAuthoringSupportPlan {
    /// Entries keyed by index-neutral module name.
    pub entries: BTreeMap<Name, TargetedAuthoringSupportPlanEntry>,
    /// Work counters for this plan.
    pub work: TargetedAuthoringSupportPlanWork,
}

/// One support key constructed at a module's ordinary topological position.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TargetedAuthoringIncrementalSupportKey {
    /// Complete normalized key input retained for exact entry comparison.
    pub key_input: TargetedAuthoringSupportKeyInput,
    /// Complete `sha256:` cache key.
    pub cache_key: String,
    /// Ordered dependency-closure commitment included in the key.
    pub closure_commitment: PackageHash,
}

/// Bounded single-pass accumulator for dependency-ordered support keys.
///
/// Callers add local artifacts only when their ordinary traversal position is
/// reached. Every local dependency must already have been added; external
/// artifacts are supplied once after the unchanged live external check.
#[derive(Clone, Debug)]
pub struct TargetedAuthoringSupportKeyAccumulator {
    local_inputs: BTreeMap<Name, TargetedAuthoringRetainedLocalIdentity>,
    local_commitments: BTreeMap<Name, PackageHash>,
    external_inputs: BTreeMap<Name, TargetedAuthoringExternalModuleInput>,
    external_commitments: BTreeMap<Name, PackageHash>,
    external_vertices: BTreeSet<Name>,
    visited_local_indices: BTreeSet<usize>,
    work: TargetedAuthoringSupportPlanWork,
}

#[derive(Clone, Copy, Debug)]
struct TargetedAuthoringRetainedLocalIdentity {
    current_certificate_file_hash: PackageHash,
    actual_export_hash: PackageHash,
    actual_certificate_hash: PackageHash,
}

impl TargetedAuthoringSupportKeyAccumulator {
    /// Initialize the command accumulator from already-live external artifacts.
    pub fn new(
        external_inputs: Vec<TargetedAuthoringExternalModuleInput>,
    ) -> Result<Self, TargetedAuthoringCacheError> {
        check_limit(
            "closure_modules",
            external_inputs.len(),
            TARGETED_AUTHORING_CACHE_LIMITS_V1.closure_modules,
        )?;
        let mut unique = BTreeMap::new();
        for input in external_inputs {
            let module = input.module.clone();
            if unique.insert(module.clone(), input).is_some() {
                return Err(duplicate("external artifact", &module));
            }
        }
        Ok(Self {
            local_inputs: BTreeMap::new(),
            local_commitments: BTreeMap::new(),
            external_inputs: unique,
            external_commitments: BTreeMap::new(),
            external_vertices: BTreeSet::new(),
            visited_local_indices: BTreeSet::new(),
            work: TargetedAuthoringSupportPlanWork::default(),
        })
    }

    /// Record one local artifact and optionally construct its exact support key.
    ///
    /// `construct_key` is false for a forced-live prerequisite whose closure
    /// identity is still required by a later eligible support consumer.
    pub fn push_local(
        &mut self,
        validated: &ValidatedPackageManifest,
        context: &TargetedAuthoringSupportKeyContext,
        module_index: usize,
        artifact: TargetedAuthoringLocalModuleInput,
        construct_key: bool,
    ) -> Result<Option<TargetedAuthoringIncrementalSupportKey>, TargetedAuthoringCacheError> {
        let manifest = validated.manifest();
        let graph = validated.graph();
        let module = manifest.modules.get(module_index).ok_or_else(|| {
            TargetedAuthoringCacheError::MissingIdentity {
                kind: "local module index",
                value: module_index.to_string(),
            }
        })?;
        if artifact.module != module.module {
            return Err(TargetedAuthoringCacheError::MissingIdentity {
                kind: "local artifact",
                value: module.module.as_dotted(),
            });
        }
        if self.external_inputs.contains_key(&artifact.module) {
            return Err(duplicate("local/external artifact", &artifact.module));
        }
        if !self.visited_local_indices.insert(module_index) {
            return Err(duplicate("local artifact", &artifact.module));
        }
        check_limit(
            "closure_modules",
            self.visited_local_indices.len() + self.external_vertices.len(),
            TARGETED_AUTHORING_CACHE_LIMITS_V1.closure_modules,
        )?;

        let resolved_imports = graph
            .resolved_module_imports
            .get(module_index)
            .ok_or_else(|| invalid_graph("local module import row is out of range"))?;
        check_limit(
            "direct_imports",
            resolved_imports.len(),
            TARGETED_AUTHORING_CACHE_LIMITS_V1.direct_imports,
        )?;
        reject_duplicate_resolved_imports(resolved_imports)?;
        reject_duplicate_certificate_imports(&artifact.certificate_imports)?;

        let module_origin = manifest
            .local_module_identity(module_index)
            .ok_or_else(|| invalid_graph("local module index is out of range"))?;
        let module_identity = targeted_authoring_module_identity(&module_origin);
        let mut children = Vec::with_capacity(resolved_imports.len());
        for import in resolved_imports {
            self.work.edge_visits = self
                .work
                .edge_visits
                .checked_add(1)
                .ok_or_else(|| invalid_graph("dependency edge count overflow"))?;
            check_limit(
                "closure_dependency_edges",
                self.work.edge_visits,
                TARGETED_AUTHORING_CACHE_LIMITS_V1.closure_dependency_edges,
            )?;
            let (dependency, child_commitment) = match import.kind {
                ResolvedModuleImportKind::Local { module_index } => {
                    let dependency_module = manifest
                        .modules
                        .get(module_index)
                        .ok_or_else(|| invalid_graph("local import index is out of range"))?;
                    if dependency_module.module != import.module
                        || dependency_module.expected_export_hash != import.export_hash
                        || dependency_module.expected_certificate_hash != import.certificate_hash
                    {
                        return Err(invalid_graph(
                            "resolved local import does not match the manifest",
                        ));
                    }
                    let dependency_input =
                        self.local_inputs.get(&import.module).ok_or_else(|| {
                            invalid_graph("local dependency does not precede its importer")
                        })?;
                    let dependency_origin = manifest
                        .local_module_identity(module_index)
                        .ok_or_else(|| invalid_graph("local dependency index is out of range"))?;
                    let dependency_module_identity =
                        targeted_authoring_module_identity(&dependency_origin);
                    let dependency = TargetedAuthoringDependencyIdentity {
                        package: dependency_origin.package,
                        version: dependency_origin.version,
                        module: dependency_origin.module.clone(),
                        module_identity: dependency_module_identity,
                        certificate_file_hash: dependency_input.current_certificate_file_hash,
                        expected_export_hash: import.export_hash,
                        expected_certificate_hash: import.certificate_hash,
                        actual_export_hash: dependency_input.actual_export_hash,
                        actual_certificate_hash: dependency_input.actual_certificate_hash,
                    };
                    let child = self
                        .local_commitments
                        .get(&import.module)
                        .copied()
                        .ok_or_else(|| {
                            invalid_graph("local dependency commitment is unavailable")
                        })?;
                    (dependency, child)
                }
                ResolvedModuleImportKind::External { import_index } => {
                    let external_manifest = manifest
                        .imports
                        .as_deref()
                        .and_then(|imports| imports.get(import_index))
                        .ok_or_else(|| invalid_graph("external import index is out of range"))?;
                    if external_manifest.module != import.module
                        || external_manifest.export_hash != import.export_hash
                        || external_manifest.certificate_hash != import.certificate_hash
                    {
                        return Err(invalid_graph(
                            "resolved external import does not match the manifest",
                        ));
                    }
                    let external = self.external_inputs.get(&import.module).ok_or_else(|| {
                        TargetedAuthoringCacheError::MissingIdentity {
                            kind: "external artifact",
                            value: import.module.as_dotted(),
                        }
                    })?;
                    if self.external_vertices.insert(import.module.clone()) {
                        check_limit(
                            "closure_modules",
                            self.visited_local_indices.len() + self.external_vertices.len(),
                            TARGETED_AUTHORING_CACHE_LIMITS_V1.closure_modules,
                        )?;
                        self.work.vertex_visits = self
                            .work
                            .vertex_visits
                            .checked_add(1)
                            .ok_or_else(|| invalid_graph("vertex count overflow"))?;
                    }
                    let origin = PackageModuleIdentity {
                        package: external_manifest.package.clone(),
                        version: external_manifest.version.clone(),
                        module: external_manifest.module.clone(),
                    };
                    let dependency_module_identity = targeted_authoring_module_identity(&origin);
                    let dependency = TargetedAuthoringDependencyIdentity {
                        package: origin.package,
                        version: origin.version,
                        module: origin.module.clone(),
                        module_identity: dependency_module_identity,
                        certificate_file_hash: external.current_certificate_file_hash,
                        expected_export_hash: import.export_hash,
                        expected_certificate_hash: import.certificate_hash,
                        actual_export_hash: external.actual_export_hash,
                        actual_certificate_hash: external.actual_certificate_hash,
                    };
                    let child = if let Some(commitment) =
                        self.external_commitments.get(&import.module).copied()
                    {
                        commitment
                    } else {
                        let commitment = external_leaf_commitment(&dependency);
                        self.external_commitments
                            .insert(import.module.clone(), commitment);
                        self.work.closure_commitments = self
                            .work
                            .closure_commitments
                            .checked_add(1)
                            .ok_or_else(|| invalid_graph("closure commitment count overflow"))?;
                        commitment
                    };
                    (dependency, child)
                }
            };
            children.push((dependency, child_commitment));
        }

        let closure_commitment = local_closure_commitment(&LocalClosureCommitmentInput {
            manifest,
            module,
            origin: &module_origin,
            module_identity,
            context,
            artifact: &artifact,
            resolved_imports,
            children: &children,
        });
        self.local_commitments
            .insert(module.module.clone(), closure_commitment);
        self.local_inputs.insert(
            module.module.clone(),
            TargetedAuthoringRetainedLocalIdentity {
                current_certificate_file_hash: artifact.current_certificate_file_hash,
                actual_export_hash: artifact.actual_export_hash,
                actual_certificate_hash: artifact.actual_certificate_hash,
            },
        );
        self.work.vertex_visits = self
            .work
            .vertex_visits
            .checked_add(1)
            .ok_or_else(|| invalid_graph("vertex count overflow"))?;
        self.work.closure_commitments = self
            .work
            .closure_commitments
            .checked_add(1)
            .ok_or_else(|| invalid_graph("closure commitment count overflow"))?;

        if !construct_key {
            return Ok(None);
        }
        let key_input = TargetedAuthoringSupportKeyInput {
            toolchain: context.toolchain.clone(),
            package: manifest.package.clone(),
            version: manifest.version.clone(),
            core_spec: manifest.core_spec.clone(),
            kernel_profile: manifest.kernel_profile.clone(),
            certificate_format: manifest.certificate_format.clone(),
            checker_profile: manifest.checker_profile.clone(),
            producer_profile: module
                .producer_profile
                .clone()
                .unwrap_or_else(|| context.default_producer_profile.clone()),
            semantic_compiler_options: context.semantic_compiler_options.clone(),
            axiom_policy_hash: context.axiom_policy_hash,
            module: module.module.clone(),
            module_identity,
            current_source_hash: artifact.current_source_hash,
            expected_source_hash: module.expected_source_hash,
            current_certificate_file_hash: artifact.current_certificate_file_hash,
            expected_certificate_file_hash: module.expected_certificate_file_hash,
            expected_export_hash: module.expected_export_hash,
            expected_axiom_report_hash: module.expected_axiom_report_hash,
            expected_certificate_hash: module.expected_certificate_hash,
            actual_export_hash: artifact.actual_export_hash,
            actual_axiom_report_hash: artifact.actual_axiom_report_hash,
            actual_certificate_hash: artifact.actual_certificate_hash,
            certificate_imports: artifact.certificate_imports,
            dependency_closure_commitment: closure_commitment,
            manifest_human_imports: resolved_imports
                .iter()
                .map(ResolvedModuleImport::semantic_identity)
                .collect(),
            source_interface_schema: context.source_interface_schema.clone(),
            source_interface_reconstruction_version: context
                .source_interface_reconstruction_version
                .clone(),
        };
        let key_input = normalized_targeted_authoring_support_key_input(&key_input);
        let cache_key = targeted_authoring_support_cache_key(&key_input)?;
        self.work.support_keys = self
            .work
            .support_keys
            .checked_add(1)
            .ok_or_else(|| invalid_graph("support key count overflow"))?;
        Ok(Some(TargetedAuthoringIncrementalSupportKey {
            key_input,
            cache_key,
            closure_commitment,
        }))
    }

    /// Return bounded single-pass work recorded so far.
    pub const fn work(&self) -> TargetedAuthoringSupportPlanWork {
        self.work
    }
}

/// Deterministic support-key planning error.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TargetedAuthoringCacheError {
    /// A required identity was absent.
    MissingIdentity {
        /// Identity category.
        kind: &'static str,
        /// Missing module or value.
        value: String,
    },
    /// Two inputs claimed the same semantic identity.
    DuplicateIdentity {
        /// Identity category.
        kind: &'static str,
        /// Duplicated module or value.
        value: String,
    },
    /// Manifest and graph data were structurally inconsistent.
    InvalidGraph {
        /// Deterministic explanation.
        detail: String,
    },
    /// A frozen targeted-authoring resource bound was exceeded.
    LimitExceeded {
        /// Bounded collection.
        field: &'static str,
        /// Frozen maximum.
        maximum: usize,
        /// Observed amount.
        actual: usize,
    },
}

impl fmt::Display for TargetedAuthoringCacheError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingIdentity { kind, value } => {
                write!(formatter, "missing {kind} identity for {value}")
            }
            Self::DuplicateIdentity { kind, value } => {
                write!(formatter, "duplicate {kind} identity for {value}")
            }
            Self::InvalidGraph { detail } => write!(formatter, "invalid package graph: {detail}"),
            Self::LimitExceeded {
                field,
                maximum,
                actual,
            } => {
                write!(formatter, "{field} exceeds limit {maximum}: {actual}")
            }
        }
    }
}

impl std::error::Error for TargetedAuthoringCacheError {}

/// Canonically serialize the complete semantic support-cache key preimage.
pub fn targeted_authoring_support_cache_key_material(
    input: &TargetedAuthoringSupportKeyInput,
) -> Result<String, TargetedAuthoringCacheError> {
    targeted_authoring_support_key_input_json(input)
}

pub(super) fn normalized_targeted_authoring_support_key_input(
    input: &TargetedAuthoringSupportKeyInput,
) -> TargetedAuthoringSupportKeyInput {
    let mut normalized = input.clone();
    normalized.semantic_compiler_options.sort();
    normalized.semantic_compiler_options.dedup();
    normalized
}

pub(super) fn targeted_authoring_support_key_input_json(
    input: &TargetedAuthoringSupportKeyInput,
) -> Result<String, TargetedAuthoringCacheError> {
    check_key_strings(input)?;
    check_limit(
        "semantic_compiler_options",
        input.semantic_compiler_options.len(),
        TARGETED_AUTHORING_CACHE_LIMITS_V1.compiler_options,
    )?;
    check_limit(
        "certificate_imports",
        input.certificate_imports.len(),
        TARGETED_AUTHORING_CACHE_LIMITS_V1.certificate_imports,
    )?;
    check_limit(
        "manifest_human_imports",
        input.manifest_human_imports.len(),
        TARGETED_AUTHORING_CACHE_LIMITS_V1.direct_imports,
    )?;
    reject_duplicate_certificate_imports(&input.certificate_imports)?;
    reject_duplicate_human_imports(&input.manifest_human_imports)?;

    let normalized = normalized_targeted_authoring_support_key_input(input);
    Ok(json_object_in_order(vec![
        (
            "cache_schema",
            json_string(PACKAGE_TARGETED_AUTHORING_SUPPORT_KEY_SCHEMA),
        ),
        (
            "payload_schema",
            json_string(PACKAGE_TARGETED_AUTHORING_SUPPORT_CONTEXT_SCHEMA),
        ),
        (
            "executable_hash",
            hash_json(input.toolchain.executable_hash),
        ),
        (
            "cli_authoring_abi",
            json_string(&input.toolchain.cli_authoring_abi),
        ),
        (
            "frontend_authoring_abi",
            json_string(&input.toolchain.frontend_authoring_abi),
        ),
        (
            "producer_authoring_abi",
            json_string(&input.toolchain.producer_authoring_abi),
        ),
        (
            "kernel_authoring_abi",
            json_string(&input.toolchain.kernel_authoring_abi),
        ),
        ("package", json_string(input.package.as_str())),
        ("version", json_string(input.version.as_str())),
        ("core_spec", json_string(&input.core_spec)),
        ("kernel_profile", json_string(&input.kernel_profile)),
        ("certificate_format", json_string(&input.certificate_format)),
        ("checker_profile", json_string(&input.checker_profile)),
        ("producer_profile", json_string(&input.producer_profile)),
        (
            "semantic_compiler_options",
            json_array(
                normalized
                    .semantic_compiler_options
                    .iter()
                    .map(|value| json_string(value))
                    .collect(),
            ),
        ),
        ("axiom_policy_hash", hash_json(input.axiom_policy_hash)),
        ("module", json_string(&input.module.as_dotted())),
        ("module_identity", hash_json(input.module_identity)),
        ("current_source_hash", hash_json(input.current_source_hash)),
        (
            "expected_source_hash",
            hash_json(input.expected_source_hash),
        ),
        (
            "current_certificate_file_hash",
            hash_json(input.current_certificate_file_hash),
        ),
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
        ("actual_export_hash", hash_json(input.actual_export_hash)),
        (
            "actual_axiom_report_hash",
            hash_json(input.actual_axiom_report_hash),
        ),
        (
            "actual_certificate_hash",
            hash_json(input.actual_certificate_hash),
        ),
        (
            "certificate_imports",
            json_array(
                input
                    .certificate_imports
                    .iter()
                    .map(certificate_import_json)
                    .collect(),
            ),
        ),
        (
            "dependency_closure_commitment",
            hash_json(input.dependency_closure_commitment),
        ),
        (
            "manifest_human_imports",
            json_array(
                input
                    .manifest_human_imports
                    .iter()
                    .map(human_import_json)
                    .collect(),
            ),
        ),
        (
            "source_interface_schema",
            json_string(&input.source_interface_schema),
        ),
        (
            "source_interface_reconstruction_version",
            json_string(&input.source_interface_reconstruction_version),
        ),
    ]))
}

/// Compute the complete lowercase `sha256:` support-cache key.
pub fn targeted_authoring_support_cache_key(
    input: &TargetedAuthoringSupportKeyInput,
) -> Result<String, TargetedAuthoringCacheError> {
    Ok(format_package_hash(&package_file_hash(
        targeted_authoring_support_cache_key_material(input)?.as_bytes(),
    )))
}

/// Derive a domain-separated module identity without manifest indices or paths.
pub fn targeted_authoring_module_identity(identity: &PackageModuleIdentity) -> PackageHash {
    package_file_hash(
        json_object_in_order(vec![
            (
                "domain",
                json_string(PACKAGE_TARGETED_AUTHORING_MODULE_IDENTITY_DOMAIN),
            ),
            ("package", json_string(identity.package.as_str())),
            ("version", json_string(identity.version.as_str())),
            ("module", json_string(&identity.module.as_dotted())),
        ])
        .as_bytes(),
    )
}

/// Plan support keys for selected local modules and all of their local dependencies.
///
/// The graph is traversed once to discover the selected closure. Commitments
/// and keys are then constructed once per vertex in dependency-topological
/// order; no flattened transitive dependency vector is materialized per key.
/// Selected indices are transient scheduling inputs and never enter a key or
/// commitment.
pub fn plan_targeted_authoring_support_keys(
    validated: &ValidatedPackageManifest,
    context: &TargetedAuthoringSupportKeyContext,
    local_inputs: &[TargetedAuthoringLocalModuleInput],
    external_inputs: &[TargetedAuthoringExternalModuleInput],
    selected_module_indices: &BTreeSet<usize>,
) -> Result<TargetedAuthoringSupportPlan, TargetedAuthoringCacheError> {
    let manifest = validated.manifest();
    let graph = validated.graph();
    let local_inputs = unique_local_inputs(local_inputs)?;
    let external_inputs = unique_external_inputs(external_inputs)?;
    reject_cross_domain_input_identities(&local_inputs, &external_inputs)?;

    let mut selected_indices = BTreeSet::new();
    let mut pending = VecDeque::new();
    let mut selected_import_rows = BTreeMap::new();
    let mut external_vertices = BTreeSet::new();
    let mut work = TargetedAuthoringSupportPlanWork::default();
    for &index in selected_module_indices {
        if index >= manifest.modules.len() {
            return Err(TargetedAuthoringCacheError::MissingIdentity {
                kind: "selected local module index",
                value: index.to_string(),
            });
        }
        if selected_indices.insert(index) {
            check_limit(
                "closure_modules",
                selected_indices.len(),
                TARGETED_AUTHORING_CACHE_LIMITS_V1.closure_modules,
            )?;
            pending.push_back(index);
        }
    }
    while let Some(index) = pending.pop_front() {
        let imports = graph.resolved_module_imports[index].clone();
        for import in &imports {
            work.edge_visits += 1;
            check_limit(
                "closure_dependency_edges",
                work.edge_visits,
                TARGETED_AUTHORING_CACHE_LIMITS_V1.closure_dependency_edges,
            )?;
            match import.kind {
                ResolvedModuleImportKind::Local { module_index } => {
                    if module_index >= manifest.modules.len() {
                        return Err(invalid_graph("local import index is out of range"));
                    }
                    if selected_indices.insert(module_index) {
                        check_limit(
                            "closure_modules",
                            selected_indices.len() + external_vertices.len(),
                            TARGETED_AUTHORING_CACHE_LIMITS_V1.closure_modules,
                        )?;
                        pending.push_back(module_index);
                    }
                }
                ResolvedModuleImportKind::External { .. } => {
                    if external_vertices.insert(import.module.clone()) {
                        check_limit(
                            "closure_modules",
                            selected_indices.len() + external_vertices.len(),
                            TARGETED_AUTHORING_CACHE_LIMITS_V1.closure_modules,
                        )?;
                    }
                }
            }
        }
        selected_import_rows.insert(index, imports);
    }
    check_limit(
        "closure_modules",
        selected_indices.len() + external_vertices.len(),
        TARGETED_AUTHORING_CACHE_LIMITS_V1.closure_modules,
    )?;
    work.vertex_visits = selected_indices.len() + external_vertices.len();

    // Identity ambiguity is a preimage error, so reject it across the complete
    // selected closure before constructing any module identity or commitment.
    for &index in &selected_indices {
        let module = &manifest.modules[index];
        let imports = selected_import_rows
            .get(&index)
            .ok_or_else(|| invalid_graph("selected module import row was not visited"))?;
        reject_duplicate_resolved_imports(imports)?;
        let local = local_inputs.get(&module.module).ok_or_else(|| {
            TargetedAuthoringCacheError::MissingIdentity {
                kind: "local artifact",
                value: module.module.as_dotted(),
            }
        })?;
        reject_duplicate_certificate_imports(&local.certificate_imports)?;
    }

    let mut dependency_counts = BTreeMap::new();
    let mut reverse_dependencies = BTreeMap::<usize, Vec<usize>>::new();
    let mut ready = BTreeSet::new();
    for &index in &selected_indices {
        let imports = selected_import_rows
            .get(&index)
            .ok_or_else(|| invalid_graph("selected module import row was not visited"))?;
        let mut dependency_count = 0_usize;
        for import in imports {
            if let ResolvedModuleImportKind::Local {
                module_index: dependency_index,
            } = import.kind
            {
                dependency_count += 1;
                reverse_dependencies
                    .entry(dependency_index)
                    .or_default()
                    .push(index);
            }
        }
        dependency_counts.insert(index, dependency_count);
        if dependency_count == 0 {
            ready.insert((manifest.modules[index].module.clone(), index));
        }
    }
    let mut selected_order = Vec::with_capacity(selected_indices.len());
    while let Some((_, index)) = ready.pop_first() {
        selected_order.push(index);
        for &dependent in reverse_dependencies
            .get(&index)
            .map_or(&[][..], Vec::as_slice)
        {
            let remaining = dependency_counts
                .get_mut(&dependent)
                .ok_or_else(|| invalid_graph("reverse dependency is outside selected closure"))?;
            *remaining = remaining
                .checked_sub(1)
                .ok_or_else(|| invalid_graph("dependency edge was counted more than once"))?;
            if *remaining == 0 {
                ready.insert((manifest.modules[dependent].module.clone(), dependent));
            }
        }
    }
    if selected_order.len() != selected_indices.len() {
        return Err(invalid_graph(
            "topological order omits a selected dependency or contains a cycle",
        ));
    }

    let mut commitments = BTreeMap::<Name, PackageHash>::new();
    let mut external_commitments = BTreeMap::<Name, PackageHash>::new();
    let mut entries = BTreeMap::new();

    for index in selected_order {
        let module = &manifest.modules[index];
        let resolved_imports = selected_import_rows
            .get(&index)
            .ok_or_else(|| invalid_graph("selected module import row was not visited"))?;
        let local = local_inputs.get(&module.module).ok_or_else(|| {
            TargetedAuthoringCacheError::MissingIdentity {
                kind: "local artifact",
                value: module.module.as_dotted(),
            }
        })?;
        check_limit(
            "direct_imports",
            resolved_imports.len(),
            TARGETED_AUTHORING_CACHE_LIMITS_V1.direct_imports,
        )?;

        let module_origin = manifest
            .local_module_identity(index)
            .ok_or_else(|| invalid_graph("selected local module index is out of range"))?;
        let module_identity = targeted_authoring_module_identity(&module_origin);
        let mut children = Vec::with_capacity(resolved_imports.len());
        for import in resolved_imports {
            let (dependency, child_commitment) = match import.kind {
                ResolvedModuleImportKind::Local { module_index } => {
                    let dependency_module = manifest
                        .modules
                        .get(module_index)
                        .ok_or_else(|| invalid_graph("local import index is out of range"))?;
                    if dependency_module.module != import.module {
                        return Err(invalid_graph(
                            "resolved local import name does not match its index",
                        ));
                    }
                    if dependency_module.expected_export_hash != import.export_hash
                        || dependency_module.expected_certificate_hash != import.certificate_hash
                    {
                        return Err(invalid_graph(
                            "resolved local import hashes do not match the manifest",
                        ));
                    }
                    let dependency_input = local_inputs.get(&import.module).ok_or_else(|| {
                        TargetedAuthoringCacheError::MissingIdentity {
                            kind: "local dependency artifact",
                            value: import.module.as_dotted(),
                        }
                    })?;
                    let dependency_origin = manifest
                        .local_module_identity(module_index)
                        .ok_or_else(|| invalid_graph("local dependency index is out of range"))?;
                    let dependency_module_identity =
                        targeted_authoring_module_identity(&dependency_origin);
                    let dependency = TargetedAuthoringDependencyIdentity {
                        package: dependency_origin.package,
                        version: dependency_origin.version,
                        module: dependency_origin.module.clone(),
                        module_identity: dependency_module_identity,
                        certificate_file_hash: dependency_input.current_certificate_file_hash,
                        expected_export_hash: import.export_hash,
                        expected_certificate_hash: import.certificate_hash,
                        actual_export_hash: dependency_input.actual_export_hash,
                        actual_certificate_hash: dependency_input.actual_certificate_hash,
                    };
                    let child = commitments.get(&import.module).copied().ok_or_else(|| {
                        invalid_graph("local dependency does not precede its importer")
                    })?;
                    (dependency, child)
                }
                ResolvedModuleImportKind::External { import_index } => {
                    let external_manifest = manifest
                        .imports
                        .as_deref()
                        .and_then(|imports| imports.get(import_index))
                        .ok_or_else(|| invalid_graph("external import index is out of range"))?;
                    if external_manifest.module != import.module {
                        return Err(invalid_graph(
                            "resolved external import name does not match its index",
                        ));
                    }
                    if external_manifest.export_hash != import.export_hash
                        || external_manifest.certificate_hash != import.certificate_hash
                    {
                        return Err(invalid_graph(
                            "resolved external import hashes do not match the manifest",
                        ));
                    }
                    let external = external_inputs.get(&import.module).ok_or_else(|| {
                        TargetedAuthoringCacheError::MissingIdentity {
                            kind: "external artifact",
                            value: import.module.as_dotted(),
                        }
                    })?;
                    let origin = PackageModuleIdentity {
                        package: external_manifest.package.clone(),
                        version: external_manifest.version.clone(),
                        module: external_manifest.module.clone(),
                    };
                    let dependency_module_identity = targeted_authoring_module_identity(&origin);
                    let dependency = TargetedAuthoringDependencyIdentity {
                        package: origin.package,
                        version: origin.version,
                        module: origin.module.clone(),
                        module_identity: dependency_module_identity,
                        certificate_file_hash: external.current_certificate_file_hash,
                        expected_export_hash: import.export_hash,
                        expected_certificate_hash: import.certificate_hash,
                        actual_export_hash: external.actual_export_hash,
                        actual_certificate_hash: external.actual_certificate_hash,
                    };
                    let child = if let Some(commitment) = external_commitments.get(&import.module) {
                        *commitment
                    } else {
                        let commitment = external_leaf_commitment(&dependency);
                        external_commitments.insert(import.module.clone(), commitment);
                        work.closure_commitments += 1;
                        commitment
                    };
                    (dependency, child)
                }
            };
            children.push((dependency, child_commitment));
        }

        let closure_commitment = local_closure_commitment(&LocalClosureCommitmentInput {
            manifest,
            module,
            origin: &module_origin,
            module_identity,
            context,
            artifact: local,
            resolved_imports,
            children: &children,
        });
        commitments.insert(module.module.clone(), closure_commitment);
        work.closure_commitments += 1;

        let input = TargetedAuthoringSupportKeyInput {
            toolchain: context.toolchain.clone(),
            package: manifest.package.clone(),
            version: manifest.version.clone(),
            core_spec: manifest.core_spec.clone(),
            kernel_profile: manifest.kernel_profile.clone(),
            certificate_format: manifest.certificate_format.clone(),
            checker_profile: manifest.checker_profile.clone(),
            producer_profile: module
                .producer_profile
                .clone()
                .unwrap_or_else(|| context.default_producer_profile.clone()),
            semantic_compiler_options: context.semantic_compiler_options.clone(),
            axiom_policy_hash: context.axiom_policy_hash,
            module: module.module.clone(),
            module_identity,
            current_source_hash: local.current_source_hash,
            expected_source_hash: module.expected_source_hash,
            current_certificate_file_hash: local.current_certificate_file_hash,
            expected_certificate_file_hash: module.expected_certificate_file_hash,
            expected_export_hash: module.expected_export_hash,
            expected_axiom_report_hash: module.expected_axiom_report_hash,
            expected_certificate_hash: module.expected_certificate_hash,
            actual_export_hash: local.actual_export_hash,
            actual_axiom_report_hash: local.actual_axiom_report_hash,
            actual_certificate_hash: local.actual_certificate_hash,
            certificate_imports: local.certificate_imports.clone(),
            dependency_closure_commitment: closure_commitment,
            manifest_human_imports: resolved_imports
                .iter()
                .map(ResolvedModuleImport::semantic_identity)
                .collect(),
            source_interface_schema: context.source_interface_schema.clone(),
            source_interface_reconstruction_version: context
                .source_interface_reconstruction_version
                .clone(),
        };
        let cache_key = targeted_authoring_support_cache_key(&input)?;
        work.support_keys += 1;
        entries.insert(
            module.module.clone(),
            TargetedAuthoringSupportPlanEntry {
                cache_key,
                closure_commitment,
            },
        );
    }
    Ok(TargetedAuthoringSupportPlan { entries, work })
}

fn unique_local_inputs(
    inputs: &[TargetedAuthoringLocalModuleInput],
) -> Result<BTreeMap<Name, &TargetedAuthoringLocalModuleInput>, TargetedAuthoringCacheError> {
    let mut values = BTreeMap::new();
    for input in inputs {
        if values.insert(input.module.clone(), input).is_some() {
            return Err(duplicate("local artifact", &input.module));
        }
    }
    Ok(values)
}

fn unique_external_inputs(
    inputs: &[TargetedAuthoringExternalModuleInput],
) -> Result<BTreeMap<Name, &TargetedAuthoringExternalModuleInput>, TargetedAuthoringCacheError> {
    let mut values = BTreeMap::new();
    for input in inputs {
        if values.insert(input.module.clone(), input).is_some() {
            return Err(duplicate("external artifact", &input.module));
        }
    }
    Ok(values)
}

fn reject_cross_domain_input_identities(
    local_inputs: &BTreeMap<Name, &TargetedAuthoringLocalModuleInput>,
    external_inputs: &BTreeMap<Name, &TargetedAuthoringExternalModuleInput>,
) -> Result<(), TargetedAuthoringCacheError> {
    if let Some(module) = local_inputs
        .keys()
        .find(|module| external_inputs.contains_key(*module))
    {
        return Err(duplicate("local/external artifact", module));
    }
    Ok(())
}

struct LocalClosureCommitmentInput<'a> {
    manifest: &'a PackageManifest,
    module: &'a PackageModule,
    origin: &'a PackageModuleIdentity,
    module_identity: PackageHash,
    context: &'a TargetedAuthoringSupportKeyContext,
    artifact: &'a TargetedAuthoringLocalModuleInput,
    resolved_imports: &'a [ResolvedModuleImport],
    children: &'a [(TargetedAuthoringDependencyIdentity, PackageHash)],
}

fn local_closure_commitment(input: &LocalClosureCommitmentInput<'_>) -> PackageHash {
    let mut compiler_options = input.context.semantic_compiler_options.clone();
    compiler_options.sort();
    compiler_options.dedup();
    package_file_hash(
        json_object_in_order(vec![
            (
                "domain",
                json_string(PACKAGE_TARGETED_AUTHORING_SUPPORT_CLOSURE_DOMAIN),
            ),
            ("node_kind", json_string("local")),
            (
                "cache_schema",
                json_string(PACKAGE_TARGETED_AUTHORING_SUPPORT_KEY_SCHEMA),
            ),
            (
                "payload_schema",
                json_string(PACKAGE_TARGETED_AUTHORING_SUPPORT_CONTEXT_SCHEMA),
            ),
            (
                "executable_hash",
                hash_json(input.context.toolchain.executable_hash),
            ),
            (
                "cli_authoring_abi",
                json_string(&input.context.toolchain.cli_authoring_abi),
            ),
            (
                "frontend_authoring_abi",
                json_string(&input.context.toolchain.frontend_authoring_abi),
            ),
            (
                "producer_authoring_abi",
                json_string(&input.context.toolchain.producer_authoring_abi),
            ),
            (
                "kernel_authoring_abi",
                json_string(&input.context.toolchain.kernel_authoring_abi),
            ),
            ("package", json_string(input.origin.package.as_str())),
            ("version", json_string(input.origin.version.as_str())),
            ("core_spec", json_string(&input.manifest.core_spec)),
            (
                "kernel_profile",
                json_string(&input.manifest.kernel_profile),
            ),
            (
                "certificate_format",
                json_string(&input.manifest.certificate_format),
            ),
            (
                "checker_profile",
                json_string(&input.manifest.checker_profile),
            ),
            (
                "producer_profile",
                json_string(
                    input
                        .module
                        .producer_profile
                        .as_deref()
                        .unwrap_or(&input.context.default_producer_profile),
                ),
            ),
            (
                "semantic_compiler_options",
                json_array(
                    compiler_options
                        .iter()
                        .map(|value| json_string(value))
                        .collect(),
                ),
            ),
            (
                "axiom_policy_hash",
                hash_json(input.context.axiom_policy_hash),
            ),
            ("module", json_string(&input.origin.module.as_dotted())),
            ("module_identity", hash_json(input.module_identity)),
            (
                "current_source_hash",
                hash_json(input.artifact.current_source_hash),
            ),
            (
                "expected_source_hash",
                hash_json(input.module.expected_source_hash),
            ),
            (
                "current_certificate_file_hash",
                hash_json(input.artifact.current_certificate_file_hash),
            ),
            (
                "expected_certificate_file_hash",
                hash_json(input.module.expected_certificate_file_hash),
            ),
            (
                "expected_export_hash",
                hash_json(input.module.expected_export_hash),
            ),
            (
                "expected_axiom_report_hash",
                hash_json(input.module.expected_axiom_report_hash),
            ),
            (
                "expected_certificate_hash",
                hash_json(input.module.expected_certificate_hash),
            ),
            (
                "actual_export_hash",
                hash_json(input.artifact.actual_export_hash),
            ),
            (
                "actual_axiom_report_hash",
                hash_json(input.artifact.actual_axiom_report_hash),
            ),
            (
                "actual_certificate_hash",
                hash_json(input.artifact.actual_certificate_hash),
            ),
            (
                "certificate_imports",
                json_array(
                    input
                        .artifact
                        .certificate_imports
                        .iter()
                        .map(certificate_import_json)
                        .collect(),
                ),
            ),
            (
                "manifest_human_imports",
                json_array(
                    input
                        .resolved_imports
                        .iter()
                        .map(ResolvedModuleImport::semantic_identity)
                        .map(|identity| human_import_json(&identity))
                        .collect(),
                ),
            ),
            (
                "source_interface_schema",
                json_string(&input.context.source_interface_schema),
            ),
            (
                "source_interface_reconstruction_version",
                json_string(&input.context.source_interface_reconstruction_version),
            ),
            (
                "dependencies",
                json_array(
                    input
                        .children
                        .iter()
                        .map(|(dependency, commitment)| {
                            json_object_in_order(vec![
                                ("identity", dependency_json(dependency)),
                                ("child_commitment", hash_json(*commitment)),
                            ])
                        })
                        .collect(),
                ),
            ),
        ])
        .as_bytes(),
    )
}

fn external_leaf_commitment(identity: &TargetedAuthoringDependencyIdentity) -> PackageHash {
    package_file_hash(
        json_object_in_order(vec![
            (
                "domain",
                json_string(PACKAGE_TARGETED_AUTHORING_EXTERNAL_LEAF_DOMAIN),
            ),
            ("identity", dependency_json(identity)),
        ])
        .as_bytes(),
    )
}

fn dependency_json(identity: &TargetedAuthoringDependencyIdentity) -> String {
    json_object_in_order(vec![
        ("package", json_string(identity.package.as_str())),
        ("version", json_string(identity.version.as_str())),
        ("module", json_string(&identity.module.as_dotted())),
        ("module_identity", hash_json(identity.module_identity)),
        (
            "certificate_file_hash",
            hash_json(identity.certificate_file_hash),
        ),
        (
            "expected_export_hash",
            hash_json(identity.expected_export_hash),
        ),
        (
            "expected_certificate_hash",
            hash_json(identity.expected_certificate_hash),
        ),
        ("actual_export_hash", hash_json(identity.actual_export_hash)),
        (
            "actual_certificate_hash",
            hash_json(identity.actual_certificate_hash),
        ),
    ])
}

fn certificate_import_json(identity: &TargetedAuthoringCertificateImportIdentity) -> String {
    json_object_in_order(vec![
        ("module", json_string(&identity.module.as_dotted())),
        ("export_hash", hash_json(identity.export_hash)),
        (
            "certificate_hash",
            identity
                .certificate_hash
                .map(hash_json)
                .unwrap_or_else(|| "null".to_owned()),
        ),
    ])
}

fn human_import_json(identity: &crate::graph::ResolvedModuleImportIdentity) -> String {
    json_object_in_order(vec![
        ("module", json_string(&identity.module.as_dotted())),
        ("export_hash", hash_json(identity.export_hash)),
        ("certificate_hash", hash_json(identity.certificate_hash)),
    ])
}

fn check_key_strings(
    input: &TargetedAuthoringSupportKeyInput,
) -> Result<(), TargetedAuthoringCacheError> {
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
        ("package", input.package.as_str()),
        ("version", input.version.as_str()),
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
        check_limit(
            field,
            value.len(),
            TARGETED_AUTHORING_CACHE_LIMITS_V1.json_string_bytes,
        )?;
    }
    check_limit(
        "module",
        input.module.as_dotted().len(),
        TARGETED_AUTHORING_CACHE_LIMITS_V1.json_string_bytes,
    )?;
    for option in &input.semantic_compiler_options {
        check_limit(
            "semantic_compiler_option",
            option.len(),
            TARGETED_AUTHORING_CACHE_LIMITS_V1.json_string_bytes,
        )?;
    }
    for import in &input.certificate_imports {
        check_limit(
            "certificate_import_module",
            import.module.as_dotted().len(),
            TARGETED_AUTHORING_CACHE_LIMITS_V1.json_string_bytes,
        )?;
    }
    for import in &input.manifest_human_imports {
        check_limit(
            "manifest_human_import_module",
            import.module.as_dotted().len(),
            TARGETED_AUTHORING_CACHE_LIMITS_V1.json_string_bytes,
        )?;
    }
    Ok(())
}

fn reject_duplicate_certificate_imports(
    imports: &[TargetedAuthoringCertificateImportIdentity],
) -> Result<(), TargetedAuthoringCacheError> {
    let mut seen = BTreeSet::new();
    for import in imports {
        if !seen.insert(import.module.clone()) {
            return Err(duplicate("certificate import", &import.module));
        }
    }
    Ok(())
}

fn reject_duplicate_human_imports(
    imports: &[crate::graph::ResolvedModuleImportIdentity],
) -> Result<(), TargetedAuthoringCacheError> {
    let mut seen = BTreeSet::new();
    for import in imports {
        if !seen.insert(import.module.clone()) {
            return Err(duplicate("manifest Human import", &import.module));
        }
    }
    Ok(())
}

fn reject_duplicate_resolved_imports(
    imports: &[ResolvedModuleImport],
) -> Result<(), TargetedAuthoringCacheError> {
    let mut seen = BTreeSet::new();
    for import in imports {
        if !seen.insert(import.module.clone()) {
            return Err(duplicate("resolved dependency", &import.module));
        }
    }
    Ok(())
}

fn duplicate(kind: &'static str, module: &Name) -> TargetedAuthoringCacheError {
    TargetedAuthoringCacheError::DuplicateIdentity {
        kind,
        value: module.as_dotted(),
    }
}

fn invalid_graph(detail: impl Into<String>) -> TargetedAuthoringCacheError {
    TargetedAuthoringCacheError::InvalidGraph {
        detail: detail.into(),
    }
}

fn check_limit(
    field: &'static str,
    actual: usize,
    maximum: usize,
) -> Result<(), TargetedAuthoringCacheError> {
    if actual > maximum {
        Err(TargetedAuthoringCacheError::LimitExceeded {
            field,
            maximum,
            actual,
        })
    } else {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        graph::ResolvedModuleImportIdentity,
        manifest::{PackageExternalImport, PackageModule, PackagePolicy},
        path::PackagePath,
        schema::PACKAGE_MANIFEST_SCHEMA,
        validate::validate_manifest,
    };

    fn h(value: u8) -> PackageHash {
        PackageHash::new([value; 32])
    }

    fn named_hash(module: &str, role: &str) -> PackageHash {
        package_file_hash(format!("{module}:{role}").as_bytes())
    }

    fn module(name: &str, imports: &[&str]) -> PackageModule {
        PackageModule {
            module: Name::from_dotted(name),
            source: PackagePath::new(format!("{name}/source.npa")),
            certificate: PackagePath::new(format!("{name}/certificate.npcert")),
            imports: imports.iter().map(Name::from_dotted).collect(),
            expected_source_hash: named_hash(name, "expected-source"),
            expected_certificate_file_hash: named_hash(name, "expected-certificate-file"),
            expected_export_hash: named_hash(name, "expected-export"),
            expected_axiom_report_hash: named_hash(name, "expected-axiom"),
            expected_certificate_hash: named_hash(name, "expected-certificate"),
            meta: None,
            replay: None,
            producer_profile: Some("npa.producer.fixture.v0.1".to_owned()),
            inductives: None,
            definitions: None,
            theorems: None,
            axioms: None,
            tags: None,
        }
    }

    fn manifest(modules: Vec<PackageModule>) -> PackageManifest {
        PackageManifest {
            schema: PACKAGE_MANIFEST_SCHEMA.to_owned(),
            package: PackageId::new("fixture-package"),
            version: PackageVersion::new("1.2.3"),
            core_spec: "npa.core.v0.1".to_owned(),
            kernel_profile: "npa.kernel.v0.1".to_owned(),
            certificate_format: "npa.certificate.canonical.v0.1".to_owned(),
            checker_profile: "npa.checker.reference.v0.1".to_owned(),
            policy: PackagePolicy {
                allow_custom_axioms: false,
                allowed_axioms: Vec::new(),
            },
            modules,
            license: None,
            repository: None,
            description: None,
            imports: None,
        }
    }

    fn context() -> TargetedAuthoringSupportKeyContext {
        TargetedAuthoringSupportKeyContext {
            toolchain: TargetedAuthoringToolchainIdentity {
                executable_hash: named_hash("tool", "bytes"),
                cli_authoring_abi: "npa.cli.authoring.v0.1".to_owned(),
                frontend_authoring_abi: "npa.frontend.authoring.v0.1".to_owned(),
                producer_authoring_abi: "npa.producer.authoring.v0.1".to_owned(),
                kernel_authoring_abi: "npa.kernel.authoring.v0.1".to_owned(),
            },
            default_producer_profile: "npa.producer.default.v0.1".to_owned(),
            semantic_compiler_options: vec![
                "equation-compiler=v1".to_owned(),
                "max-declarations=65536".to_owned(),
            ],
            axiom_policy_hash: named_hash("policy", "effective"),
            source_interface_schema: "npa.source_interface.v0.1".to_owned(),
            source_interface_reconstruction_version: "npa.reconstruct.v0.1".to_owned(),
        }
    }

    fn local_input(module: &PackageModule) -> TargetedAuthoringLocalModuleInput {
        TargetedAuthoringLocalModuleInput {
            module: module.module.clone(),
            current_source_hash: named_hash(&module.module.as_dotted(), "current-source"),
            current_certificate_file_hash: named_hash(
                &module.module.as_dotted(),
                "current-certificate-file",
            ),
            actual_export_hash: named_hash(&module.module.as_dotted(), "actual-export"),
            actual_axiom_report_hash: named_hash(&module.module.as_dotted(), "actual-axiom"),
            actual_certificate_hash: named_hash(&module.module.as_dotted(), "actual-certificate"),
            certificate_imports: module
                .imports
                .iter()
                .map(|import| TargetedAuthoringCertificateImportIdentity {
                    module: import.clone(),
                    export_hash: named_hash(&import.as_dotted(), "actual-export"),
                    certificate_hash: Some(named_hash(&import.as_dotted(), "actual-certificate")),
                })
                .collect(),
        }
    }

    fn local_inputs(manifest: &PackageManifest) -> Vec<TargetedAuthoringLocalModuleInput> {
        manifest.modules.iter().map(local_input).collect()
    }

    fn selected(manifest: &PackageManifest, module: &str) -> BTreeSet<usize> {
        [manifest
            .modules
            .iter()
            .position(|candidate| candidate.module == Name::from_dotted(module))
            .unwrap()]
        .into_iter()
        .collect()
    }

    fn plan(
        manifest: &PackageManifest,
        local_inputs: &[TargetedAuthoringLocalModuleInput],
        selected_modules: &BTreeSet<usize>,
    ) -> TargetedAuthoringSupportPlan {
        let validated = validate_manifest(manifest.clone()).unwrap();
        plan_targeted_authoring_support_keys(
            &validated,
            &context(),
            local_inputs,
            &[],
            selected_modules,
        )
        .unwrap()
    }

    fn golden_input() -> TargetedAuthoringSupportKeyInput {
        TargetedAuthoringSupportKeyInput {
            toolchain: TargetedAuthoringToolchainIdentity {
                executable_hash: h(1),
                cli_authoring_abi: "cli-v1".to_owned(),
                frontend_authoring_abi: "frontend-v1".to_owned(),
                producer_authoring_abi: "producer-abi-v1".to_owned(),
                kernel_authoring_abi: "kernel-abi-v1".to_owned(),
            },
            package: PackageId::new("golden-package"),
            version: PackageVersion::new("1.2.3"),
            core_spec: "core-v1".to_owned(),
            kernel_profile: "kernel-v1".to_owned(),
            certificate_format: "certificate-v1".to_owned(),
            checker_profile: "checker-v1".to_owned(),
            producer_profile: "producer-v1".to_owned(),
            semantic_compiler_options: vec!["z=3".to_owned(), "a=1".to_owned(), "a=1".to_owned()],
            axiom_policy_hash: h(2),
            module: Name::from_dotted("Golden.Module"),
            module_identity: h(3),
            current_source_hash: h(4),
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
                module: Name::from_dotted("Golden.Dependency"),
                export_hash: h(14),
                certificate_hash: Some(h(15)),
            }],
            dependency_closure_commitment: h(16),
            manifest_human_imports: vec![ResolvedModuleImportIdentity {
                module: Name::from_dotted("Golden.Dependency"),
                export_hash: h(17),
                certificate_hash: h(18),
            }],
            source_interface_schema: "source-interface-v1".to_owned(),
            source_interface_reconstruction_version: "reconstruct-v1".to_owned(),
        }
    }

    #[test]
    fn support_cache_key_canonical_serialization_golden_vector() {
        let input = golden_input();
        let material = targeted_authoring_support_cache_key_material(&input).unwrap();
        assert!(material.starts_with(
            r#"{"cache_schema":"npa.package.targeted_authoring_support_key.v0.1","payload_schema":"npa.package.targeted_authoring_support_context.v0.1""#
        ));
        assert!(material.contains(r#""semantic_compiler_options":["a=1","z=3"]"#));
        assert_eq!(
            targeted_authoring_support_cache_key(&input).unwrap(),
            "sha256:32c578f6623e0485c613d7ab08e46da0d5de8fd9f6480fc4f081581ccf96f3c0"
        );
    }

    #[test]
    fn targeted_authoring_differential_support_key_every_semantic_field_mutation_changes_key() {
        let base = golden_input();
        let base_key = targeted_authoring_support_cache_key(&base).unwrap();
        let mut variants = Vec::new();
        macro_rules! changed {
            ($body:expr) => {{
                let mut value = base.clone();
                $body(&mut value);
                variants.push(value);
            }};
        }
        changed!(|v: &mut TargetedAuthoringSupportKeyInput| v.toolchain.executable_hash = h(101));
        changed!(|v: &mut TargetedAuthoringSupportKeyInput| v
            .toolchain
            .cli_authoring_abi
            .push('x'));
        changed!(|v: &mut TargetedAuthoringSupportKeyInput| v
            .toolchain
            .frontend_authoring_abi
            .push('x'));
        changed!(|v: &mut TargetedAuthoringSupportKeyInput| v
            .toolchain
            .producer_authoring_abi
            .push('x'));
        changed!(|v: &mut TargetedAuthoringSupportKeyInput| v
            .toolchain
            .kernel_authoring_abi
            .push('x'));
        changed!(|v: &mut TargetedAuthoringSupportKeyInput| v.package =
            PackageId::new("changed-package"));
        changed!(
            |v: &mut TargetedAuthoringSupportKeyInput| v.version = PackageVersion::new("9.9.9")
        );
        changed!(|v: &mut TargetedAuthoringSupportKeyInput| v.core_spec.push('x'));
        changed!(|v: &mut TargetedAuthoringSupportKeyInput| v.kernel_profile.push('x'));
        changed!(|v: &mut TargetedAuthoringSupportKeyInput| v.certificate_format.push('x'));
        changed!(|v: &mut TargetedAuthoringSupportKeyInput| v.checker_profile.push('x'));
        changed!(|v: &mut TargetedAuthoringSupportKeyInput| v.producer_profile.push('x'));
        changed!(|v: &mut TargetedAuthoringSupportKeyInput| v
            .semantic_compiler_options
            .push("new=1".to_owned()));
        changed!(|v: &mut TargetedAuthoringSupportKeyInput| v.axiom_policy_hash = h(102));
        changed!(|v: &mut TargetedAuthoringSupportKeyInput| v.module =
            Name::from_dotted("Changed.Module"));
        changed!(|v: &mut TargetedAuthoringSupportKeyInput| v.module_identity = h(103));
        changed!(|v: &mut TargetedAuthoringSupportKeyInput| v.current_source_hash = h(104));
        changed!(|v: &mut TargetedAuthoringSupportKeyInput| v.expected_source_hash = h(105));
        changed!(
            |v: &mut TargetedAuthoringSupportKeyInput| v.current_certificate_file_hash = h(106)
        );
        changed!(
            |v: &mut TargetedAuthoringSupportKeyInput| v.expected_certificate_file_hash = h(107)
        );
        changed!(|v: &mut TargetedAuthoringSupportKeyInput| v.expected_export_hash = h(108));
        changed!(|v: &mut TargetedAuthoringSupportKeyInput| v.expected_axiom_report_hash = h(109));
        changed!(|v: &mut TargetedAuthoringSupportKeyInput| v.expected_certificate_hash = h(110));
        changed!(|v: &mut TargetedAuthoringSupportKeyInput| v.actual_export_hash = h(111));
        changed!(|v: &mut TargetedAuthoringSupportKeyInput| v.actual_axiom_report_hash = h(112));
        changed!(|v: &mut TargetedAuthoringSupportKeyInput| v.actual_certificate_hash = h(113));
        changed!(
            |v: &mut TargetedAuthoringSupportKeyInput| v.certificate_imports[0].module =
                Name::from_dotted("Changed.Dependency")
        );
        changed!(
            |v: &mut TargetedAuthoringSupportKeyInput| v.certificate_imports[0].export_hash =
                h(114)
        );
        changed!(
            |v: &mut TargetedAuthoringSupportKeyInput| v.certificate_imports[0].certificate_hash =
                None
        );
        changed!(
            |v: &mut TargetedAuthoringSupportKeyInput| v.dependency_closure_commitment = h(116)
        );
        changed!(
            |v: &mut TargetedAuthoringSupportKeyInput| v.manifest_human_imports[0].module =
                Name::from_dotted("Changed.Human")
        );
        changed!(
            |v: &mut TargetedAuthoringSupportKeyInput| v.manifest_human_imports[0].export_hash =
                h(117)
        );
        changed!(
            |v: &mut TargetedAuthoringSupportKeyInput| v.manifest_human_imports[0]
                .certificate_hash = h(118)
        );
        changed!(|v: &mut TargetedAuthoringSupportKeyInput| v.source_interface_schema.push('x'));
        changed!(|v: &mut TargetedAuthoringSupportKeyInput| v
            .source_interface_reconstruction_version
            .push('x'));

        for (index, variant) in variants.iter().enumerate() {
            assert_ne!(
                targeted_authoring_support_cache_key(variant).unwrap(),
                base_key,
                "semantic mutation {index} did not invalidate the key"
            );
        }
    }

    #[test]
    fn targeted_authoring_differential_support_key_every_observation_field_is_non_semantic() {
        #[allow(dead_code)]
        #[derive(Clone)]
        struct Observations {
            target_seed: String,
            absolute_path: String,
            cache_path: String,
            cwd: String,
            git_state: String,
            mtime: u64,
            module_index: usize,
            topological_position: usize,
            traversal_order: Vec<usize>,
            timestamp: u64,
            duration_ns: u64,
            timing_selector: String,
            fuel_selector: String,
            diagnostic: String,
            host: String,
        }
        fn key(input: &TargetedAuthoringSupportKeyInput, _observations: &Observations) -> String {
            targeted_authoring_support_cache_key(input).unwrap()
        }
        let input = golden_input();
        let base = Observations {
            target_seed: "Target.One".to_owned(),
            absolute_path: "/checkout/a".to_owned(),
            cache_path: "/cache/a".to_owned(),
            cwd: "/cwd/a".to_owned(),
            git_state: "clean".to_owned(),
            mtime: 1,
            module_index: 2,
            topological_position: 3,
            traversal_order: vec![0, 1],
            timestamp: 4,
            duration_ns: 5,
            timing_selector: "off".to_owned(),
            fuel_selector: "summary".to_owned(),
            diagnostic: "first".to_owned(),
            host: "host-a".to_owned(),
        };
        let expected = key(&input, &base);
        let mut variants = Vec::new();
        macro_rules! observed {
            ($body:expr) => {{
                let mut value = base.clone();
                $body(&mut value);
                variants.push(value);
            }};
        }
        observed!(|v: &mut Observations| v.target_seed.push('x'));
        observed!(|v: &mut Observations| v.absolute_path.push('x'));
        observed!(|v: &mut Observations| v.cache_path.push('x'));
        observed!(|v: &mut Observations| v.cwd.push('x'));
        observed!(|v: &mut Observations| v.git_state.push('x'));
        observed!(|v: &mut Observations| v.mtime += 1);
        observed!(|v: &mut Observations| v.module_index += 1);
        observed!(|v: &mut Observations| v.topological_position += 1);
        observed!(|v: &mut Observations| v.traversal_order.reverse());
        observed!(|v: &mut Observations| v.timestamp += 1);
        observed!(|v: &mut Observations| v.duration_ns += 1);
        observed!(|v: &mut Observations| v.timing_selector.push('x'));
        observed!(|v: &mut Observations| v.fuel_selector.push('x'));
        observed!(|v: &mut Observations| v.diagnostic.push('x'));
        observed!(|v: &mut Observations| v.host.push('x'));
        for variant in &variants {
            assert_eq!(key(&input, variant), expected);
        }
    }

    #[test]
    fn support_closure_commitment_diamond_is_linear_and_prerequisite_sensitive() {
        let manifest = manifest(vec![
            module("Fixture.Root", &[]),
            module("Fixture.Left", &["Fixture.Root"]),
            module("Fixture.Right", &["Fixture.Root"]),
            module("Fixture.Target", &["Fixture.Left", "Fixture.Right"]),
        ]);
        let inputs = local_inputs(&manifest);
        let first = plan(&manifest, &inputs, &selected(&manifest, "Fixture.Target"));
        assert_eq!(first.work.vertex_visits, 4);
        assert_eq!(first.work.edge_visits, 4);
        assert_eq!(first.work.closure_commitments, 4);
        assert_eq!(first.work.support_keys, 4);
        assert_eq!(
            format_package_hash(
                &first.entries[&Name::from_dotted("Fixture.Target")].closure_commitment
            ),
            "sha256:1217c05ae8bdb07ea94216122950fd77d844b0c28bfeb17b323189921b61946c"
        );

        let mut changed = inputs.clone();
        changed
            .iter_mut()
            .find(|input| input.module == Name::from_dotted("Fixture.Root"))
            .unwrap()
            .current_certificate_file_hash = h(200);
        let second = plan(&manifest, &changed, &selected(&manifest, "Fixture.Target"));
        assert_ne!(
            first.entries[&Name::from_dotted("Fixture.Target")].cache_key,
            second.entries[&Name::from_dotted("Fixture.Target")].cache_key
        );

        let mut changed_manifest = manifest.clone();
        let root = changed_manifest
            .modules
            .iter_mut()
            .find(|module| module.module == Name::from_dotted("Fixture.Root"))
            .unwrap();
        root.expected_axiom_report_hash = h(201);
        root.producer_profile = Some("npa.producer.changed.v0.1".to_owned());
        let third = plan(
            &changed_manifest,
            &inputs,
            &selected(&changed_manifest, "Fixture.Target"),
        );
        assert_ne!(
            first.entries[&Name::from_dotted("Fixture.Target")].cache_key,
            third.entries[&Name::from_dotted("Fixture.Target")].cache_key
        );
    }

    #[test]
    fn targeted_authoring_incremental_lookup_keys_match_batch_plan_in_ordinary_order() {
        let manifest = manifest(vec![
            module("Fixture.Root", &[]),
            module("Fixture.Left", &["Fixture.Root"]),
            module("Fixture.Right", &["Fixture.Root"]),
            module("Fixture.Target", &["Fixture.Left", "Fixture.Right"]),
        ]);
        let validated = validate_manifest(manifest.clone()).unwrap();
        let inputs = local_inputs(&manifest);
        let selected = (0..manifest.modules.len()).collect::<BTreeSet<_>>();
        let batch =
            plan_targeted_authoring_support_keys(&validated, &context(), &inputs, &[], &selected)
                .unwrap();
        let mut accumulator = TargetedAuthoringSupportKeyAccumulator::new(Vec::new()).unwrap();
        let mut incremental = BTreeMap::new();
        for &module_index in &validated.graph().topological_order {
            let key = accumulator
                .push_local(
                    &validated,
                    &context(),
                    module_index,
                    inputs[module_index].clone(),
                    true,
                )
                .unwrap()
                .unwrap();
            incremental.insert(
                manifest.modules[module_index].module.clone(),
                (key.cache_key, key.closure_commitment),
            );
        }

        assert_eq!(incremental.len(), batch.entries.len());
        for (module, entry) in &batch.entries {
            assert_eq!(
                incremental.get(module),
                Some(&(entry.cache_key.clone(), entry.closure_commitment))
            );
        }
        assert_eq!(accumulator.work(), batch.work);
    }

    #[test]
    fn support_closure_commitment_long_chain_visits_each_vertex_and_edge_once() {
        const LENGTH: usize = 300;
        let mut modules = Vec::with_capacity(LENGTH);
        for index in 0..LENGTH {
            let name = format!("Fixture.M{index:04}");
            let imports = if index == 0 {
                Vec::new()
            } else {
                vec![format!("Fixture.M{:04}", index - 1)]
            };
            let import_refs = imports.iter().map(String::as_str).collect::<Vec<_>>();
            modules.push(module(&name, &import_refs));
        }
        let manifest = manifest(modules);
        let inputs = local_inputs(&manifest);
        let result = plan(
            &manifest,
            &inputs,
            &selected(&manifest, &format!("Fixture.M{:04}", LENGTH - 1)),
        );
        assert_eq!(result.entries.len(), LENGTH);
        assert_eq!(result.work.vertex_visits, LENGTH);
        assert_eq!(result.work.edge_visits, LENGTH - 1);
        assert_eq!(result.work.closure_commitments, LENGTH);
        assert_eq!(result.work.support_keys, LENGTH);
    }

    #[test]
    fn targeted_authoring_differential_manifest_reorder_and_reindexed_graph_are_equivalent() {
        let original = manifest(vec![
            module("Fixture.Root", &[]),
            module("Fixture.Left", &["Fixture.Root"]),
            module("Fixture.Right", &["Fixture.Root"]),
            module("Fixture.Target", &["Fixture.Left", "Fixture.Right"]),
        ]);
        let reordered = manifest(vec![
            module("Fixture.Target", &["Fixture.Left", "Fixture.Right"]),
            module("Fixture.Right", &["Fixture.Root"]),
            module("Fixture.Root", &[]),
            module("Fixture.Left", &["Fixture.Root"]),
        ]);
        let mut reordered_inputs = local_inputs(&reordered);
        reordered_inputs.reverse();
        let first = plan(
            &original,
            &local_inputs(&original),
            &selected(&original, "Fixture.Target"),
        );
        let second = plan(
            &reordered,
            &reordered_inputs,
            &selected(&reordered, "Fixture.Target"),
        );
        assert_eq!(first.entries, second.entries);
        assert_eq!(first.work, second.work);
    }

    #[test]
    fn support_closure_commitment_external_certificate_file_mutation_invalidates_importer() {
        let mut manifest = manifest(vec![module("Fixture.Target", &["External.Module"])]);
        manifest.imports = Some(vec![PackageExternalImport {
            module: Name::from_dotted("External.Module"),
            package: PackageId::new("external-package"),
            version: PackageVersion::new("2.0.0"),
            certificate: PackagePath::new("External/Module/certificate.npcert"),
            export_hash: h(21),
            certificate_hash: h(22),
        }]);
        let local = local_inputs(&manifest);
        let selected = selected(&manifest, "Fixture.Target");
        let validated = validate_manifest(manifest.clone()).unwrap();
        let external = TargetedAuthoringExternalModuleInput {
            module: Name::from_dotted("External.Module"),
            current_certificate_file_hash: h(23),
            actual_export_hash: h(24),
            actual_certificate_hash: h(25),
        };
        let first = plan_targeted_authoring_support_keys(
            &validated,
            &context(),
            &local,
            std::slice::from_ref(&external),
            &selected,
        )
        .unwrap();
        let mut changed = external;
        changed.current_certificate_file_hash = h(26);
        let second = plan_targeted_authoring_support_keys(
            &validated,
            &context(),
            &local,
            &[changed],
            &selected,
        )
        .unwrap();
        assert_eq!(first.work.vertex_visits, 2);
        assert_eq!(first.work.edge_visits, 1);
        assert_ne!(
            first.entries[&Name::from_dotted("Fixture.Target")].cache_key,
            second.entries[&Name::from_dotted("Fixture.Target")].cache_key
        );
    }

    #[test]
    fn support_closure_commitment_rejects_duplicate_and_ambiguous_imports() {
        let manifest = manifest(vec![
            module("Fixture.Dependency", &[]),
            module(
                "Fixture.Target",
                &["Fixture.Dependency", "Fixture.Dependency"],
            ),
        ]);
        let selected = selected(&manifest, "Fixture.Target");
        let local = local_inputs(&manifest);
        let validated = validate_manifest(manifest).unwrap();
        let error =
            plan_targeted_authoring_support_keys(&validated, &context(), &local, &[], &selected)
                .unwrap_err();
        assert!(matches!(
            error,
            TargetedAuthoringCacheError::DuplicateIdentity {
                kind: "resolved dependency",
                ..
            }
        ));

        let mut input = golden_input();
        input
            .certificate_imports
            .push(input.certificate_imports[0].clone());
        assert!(matches!(
            targeted_authoring_support_cache_key(&input),
            Err(TargetedAuthoringCacheError::DuplicateIdentity {
                kind: "certificate import",
                ..
            })
        ));
    }

    #[test]
    fn support_closure_commitment_rejects_cycle_or_incomplete_topology() {
        let manifest = manifest(vec![
            module("Fixture.A", &["Fixture.B"]),
            module("Fixture.B", &["Fixture.A"]),
        ]);
        assert!(validate_manifest(manifest).is_err());
    }
}

//! Package lock data model and canonical JSON parsing.
//!
//! A package lock is generated orchestration metadata. It records source-free
//! certificate identities for package graph verification, but it is not proof
//! evidence by itself.

use std::{
    collections::{BTreeMap, BTreeSet},
    error::Error,
    fmt,
    fs::File,
    io::{self, Read},
    path::Path,
};

use npa_cert::Name;

use crate::{
    artifact_snapshot::{
        HashedPackageLockArtifact, OwnedPackageLockArtifact, PackageArtifactPreparationObservation,
        PackageLockArtifactSnapshots, PreparedArtifactObservationMode,
        PreparedArtifactRetentionPolicy, PreparedPackageArtifacts,
    },
    error::{PackageLockError, PackageLockResult},
    graph::ResolvedModuleImport,
    hash::{format_package_hash, package_file_hash, parse_package_hash, PackageHash},
    json::{parse_json, JsonMember, JsonValue},
    manifest::{PackageExternalImport, PackageModule, PackageVersion},
    name::{validate_package_id, PackageId},
    path::{validate_package_path, PackagePath},
    schema::PACKAGE_LOCK_SCHEMA,
    validate::{validate_package_version, ValidatedPackageManifest},
};

/// Generated `npa.package.lock.v0.1` package lock artifact.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageLockManifest {
    /// Lock schema string; must equal [`PACKAGE_LOCK_SCHEMA`].
    pub schema: String,
    /// Package identity copied from the validated package manifest.
    pub package: PackageId,
    /// Exact package version copied from the validated package manifest.
    pub version: PackageVersion,
    /// Exact manifest path and file hash used to produce the lock.
    pub manifest: PackageLockManifestReference,
    /// Source-free certificate entries sorted canonically when serialized.
    pub entries: Vec<PackageLockEntry>,
}

impl PackageLockManifest {
    /// Serialize the lock as deterministic canonical JSON.
    pub fn canonical_json(&self) -> PackageLockResult<String> {
        validate_package_lock_manifest(self)?;
        Ok(package_lock_json_unchecked(&normalized_package_lock(self)))
    }
}

/// Package manifest identity recorded inside a package lock.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageLockManifestReference {
    /// Package-relative path to the manifest bytes.
    pub path: PackagePath,
    /// Exact SHA-256 hash of the manifest file bytes.
    pub file_hash: PackageHash,
}

/// Package lock entry origin.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PackageLockEntryOrigin {
    /// Certificate belongs to the local package.
    Local,
    /// Certificate belongs to an external hash-pinned package import.
    External,
}

impl PackageLockEntryOrigin {
    /// Return the lock JSON origin string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Local => "local",
            Self::External => "external",
        }
    }

    fn parse(value: &str, path: &str) -> PackageLockResult<Self> {
        match value {
            "local" => Ok(Self::Local),
            "external" => Ok(Self::External),
            _ => Err(PackageLockError::invalid_origin(path, value)),
        }
    }
}

/// One source-free certificate identity in a package lock.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageLockEntry {
    /// Module provided by this certificate entry.
    pub module: Name,
    /// Whether the entry is local to the package or external.
    pub origin: PackageLockEntryOrigin,
    /// Package-relative path to the certificate bytes.
    pub certificate: PackagePath,
    /// Exact SHA-256 hash of the certificate file bytes.
    pub certificate_file_hash: PackageHash,
    /// Canonical export hash declared by the certificate.
    pub export_hash: PackageHash,
    /// Canonical axiom report hash declared by the certificate.
    pub axiom_report_hash: PackageHash,
    /// Canonical certificate hash declared by the certificate.
    pub certificate_hash: PackageHash,
    /// Direct certificate import identities.
    pub imports: Vec<PackageLockImport>,
    /// External package identity; present only when [`Self::origin`] is external.
    pub package: Option<PackageId>,
    /// External package version; present only when [`Self::origin`] is external.
    pub version: Option<PackageVersion>,
}

/// One direct certificate import identity recorded in a package lock entry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageLockImport {
    /// Imported module name.
    pub module: Name,
    /// Imported module export hash.
    pub export_hash: PackageHash,
    /// Imported module certificate hash.
    pub certificate_hash: PackageHash,
}

/// Certificate artifact bytes provided to the package lock builder.
#[derive(Clone, Debug)]
pub struct PackageLockArtifact<'a> {
    /// Package-relative certificate path.
    pub path: PackagePath,
    /// Exact certificate file bytes at [`Self::path`].
    pub bytes: &'a [u8],
}

struct DerivedPackageLockEntry {
    entry: PackageLockEntry,
    file_hash: PackageHash,
    decoded: npa_cert::ModuleCert,
}

/// Resolved package-lock import graph.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageLockGraph {
    /// Direct imports for each canonical, module-sorted package-lock entry.
    pub resolved_entry_imports: Vec<Vec<PackageLockResolvedImport>>,
    /// Deterministic certificate verification order, dependency before dependent.
    pub topological_order: Vec<Name>,
}

/// One package-lock import resolved to another canonical package-lock entry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageLockResolvedImport {
    /// Imported module name.
    pub module: Name,
    /// Index into the canonical, module-sorted package-lock entry list.
    pub entry_index: usize,
    /// Imported module export hash.
    pub export_hash: PackageHash,
    /// Imported module certificate hash.
    pub certificate_hash: PackageHash,
}

/// Operation counts collected only by tests and the explicit planning benchmark.
#[cfg(any(test, feature = "planning-benchmark"))]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PackageGraphPlanningCounterSummary {
    /// Successful operation-scoped graph-index constructions.
    pub graph_index_constructions: u64,
    /// Internal invariant failures observed during index construction.
    pub graph_index_invariant_failures: u64,
    /// Reverse-adjacency list sorts; canonical construction requires zero.
    pub reverse_list_sort_calls: u64,
    /// Entries removed from forward dependency worklists.
    pub forward_vertex_dequeues: u64,
    /// Dependency edges visited by forward worklists.
    pub forward_edge_visits: u64,
    /// Entries removed from reverse dependency worklists.
    pub reverse_vertex_dequeues: u64,
    /// Reverse-dependency edges visited by reverse worklists.
    pub reverse_edge_visits: u64,
    /// Entry-mark slots allocated once for reverse-origin traversals.
    pub reverse_visit_slots_initialized: u64,
    /// Reverse-closure origins started with reusable epoch marks.
    pub reverse_origin_epochs: u64,
    /// Origin/entry pairs removed from provenance worklists.
    pub provenance_pair_dequeues: u64,
    /// Edges visited while propagating one provenance origin.
    pub provenance_edge_visits: u64,
    /// Entry-mark slots allocated once for provenance traversals.
    pub provenance_visit_slots_initialized: u64,
    /// Provenance origins started with reusable epoch marks.
    pub provenance_origin_epochs: u64,
    /// Selected entries assigned to a topological layer.
    pub layer_assignments: u64,
    /// Direct dependency edges inspected during layer assignment.
    pub layer_dependency_edge_visits: u64,
    /// Whether any counter saturated its `u64` representation.
    pub overflowed: bool,
}

#[cfg(any(test, feature = "planning-benchmark"))]
impl PackageGraphPlanningCounterSummary {
    /// Merge lower planning work into this operation-owned summary.
    pub fn merge(&mut self, other: Self) {
        macro_rules! merge_field {
            ($field:ident) => {
                let (next, overflowed) = self.$field.overflowing_add(other.$field);
                self.$field = if overflowed { u64::MAX } else { next };
                self.overflowed |= overflowed;
            };
        }
        merge_field!(graph_index_constructions);
        merge_field!(graph_index_invariant_failures);
        merge_field!(reverse_list_sort_calls);
        merge_field!(forward_vertex_dequeues);
        merge_field!(forward_edge_visits);
        merge_field!(reverse_vertex_dequeues);
        merge_field!(reverse_edge_visits);
        merge_field!(reverse_visit_slots_initialized);
        merge_field!(reverse_origin_epochs);
        merge_field!(provenance_pair_dequeues);
        merge_field!(provenance_edge_visits);
        merge_field!(provenance_visit_slots_initialized);
        merge_field!(provenance_origin_epochs);
        merge_field!(layer_assignments);
        merge_field!(layer_dependency_edge_visits);
        self.overflowed |= other.overflowed;
    }
}

trait PackageGraphPlanningCounterSink {
    fn graph_index_constructed(&mut self) {}
    fn graph_index_invariant_failed(&mut self) {}
    fn forward_vertex_dequeued(&mut self) {}
    fn forward_edges_visited(&mut self, _count: usize) {}
    fn layer_assigned(&mut self) {}
    fn layer_dependency_edges_visited(&mut self, _count: usize) {}
}

impl PackageGraphPlanningCounterSink for () {}

#[cfg(any(test, feature = "planning-benchmark"))]
impl PackageGraphPlanningCounterSummary {
    fn increment(value: &mut u64, overflowed: &mut bool) {
        let (next, overflow) = value.overflowing_add(1);
        *value = if overflow { u64::MAX } else { next };
        *overflowed |= overflow;
    }

    fn add_usize(value: &mut u64, addend: usize, overflowed: &mut bool) {
        let addend = u64::try_from(addend).unwrap_or(u64::MAX);
        let (next, overflow) = value.overflowing_add(addend);
        *value = if overflow { u64::MAX } else { next };
        *overflowed |= overflow || addend == u64::MAX;
    }
}

#[cfg(any(test, feature = "planning-benchmark"))]
impl PackageGraphPlanningCounterSink for PackageGraphPlanningCounterSummary {
    fn graph_index_constructed(&mut self) {
        Self::increment(&mut self.graph_index_constructions, &mut self.overflowed);
    }

    fn graph_index_invariant_failed(&mut self) {
        Self::increment(
            &mut self.graph_index_invariant_failures,
            &mut self.overflowed,
        );
    }

    fn forward_vertex_dequeued(&mut self) {
        Self::increment(&mut self.forward_vertex_dequeues, &mut self.overflowed);
    }

    fn forward_edges_visited(&mut self, count: usize) {
        Self::add_usize(&mut self.forward_edge_visits, count, &mut self.overflowed);
    }

    fn layer_assigned(&mut self) {
        Self::increment(&mut self.layer_assignments, &mut self.overflowed);
    }

    fn layer_dependency_edges_visited(&mut self, count: usize) {
        Self::add_usize(
            &mut self.layer_dependency_edge_visits,
            count,
            &mut self.overflowed,
        );
    }
}

/// Operation-scoped adjacency and topological index for a validated lock graph.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PackageLockGraphIndex {
    module_by_entry: Vec<Name>,
    entry_by_module: BTreeMap<Name, usize>,
    topological_entries: Vec<usize>,
    topological_position_by_entry: Vec<usize>,
    dependencies_by_entry: Vec<Vec<usize>>,
    reverse_dependencies_by_entry: Vec<Vec<usize>>,
}

impl PackageLockGraphIndex {
    /// Return the canonical module for an entry index.
    pub fn module_by_entry(&self, entry: usize) -> Option<&Name> {
        self.module_by_entry.get(entry)
    }

    /// Resolve a canonical module to its entry index.
    pub fn entry_by_module(&self, module: &Name) -> Option<usize> {
        self.entry_by_module.get(module).copied()
    }

    /// Return dependency-first entry indices.
    pub fn topological_entries(&self) -> &[usize] {
        &self.topological_entries
    }

    /// Return the topological position of an entry.
    pub fn topological_position(&self, entry: usize) -> Option<usize> {
        self.topological_position_by_entry.get(entry).copied()
    }

    /// Return direct dependency entry indices.
    pub fn dependencies(&self, entry: usize) -> Option<&[usize]> {
        self.dependencies_by_entry.get(entry).map(Vec::as_slice)
    }

    /// Return direct reverse-dependent entry indices.
    pub fn reverse_dependencies(&self, entry: usize) -> Option<&[usize]> {
        self.reverse_dependencies_by_entry
            .get(entry)
            .map(Vec::as_slice)
    }

    /// Compute dependency closure from sorted seed names with a linear worklist.
    pub fn dependency_closure(
        &self,
        seeds: &BTreeSet<Name>,
    ) -> Result<Vec<bool>, PackageLockIndexInvariantError> {
        self.dependency_closure_with_sink(seeds, &mut ())
    }

    /// Counted dependency closure for tests and the closed planning benchmark.
    #[cfg(any(test, feature = "planning-benchmark"))]
    #[doc(hidden)]
    pub fn dependency_closure_with_planning_counters(
        &self,
        seeds: &BTreeSet<Name>,
        counters: &mut PackageGraphPlanningCounterSummary,
    ) -> Result<Vec<bool>, PackageLockIndexInvariantError> {
        self.dependency_closure_with_sink(seeds, counters)
    }

    fn dependency_closure_with_sink<S: PackageGraphPlanningCounterSink>(
        &self,
        seeds: &BTreeSet<Name>,
        counters: &mut S,
    ) -> Result<Vec<bool>, PackageLockIndexInvariantError> {
        let mut selected = vec![false; self.module_by_entry.len()];
        let mut pending = Vec::with_capacity(seeds.len());
        for seed in seeds {
            let entry = self.entry_by_module(seed).ok_or_else(|| {
                PackageLockIndexInvariantError::new("selected_module_missing_from_index")
            })?;
            if !selected[entry] {
                selected[entry] = true;
                pending.push(entry);
            }
        }
        while let Some(entry) = pending.pop() {
            counters.forward_vertex_dequeued();
            counters.forward_edges_visited(self.dependencies_by_entry[entry].len());
            for dependency in &self.dependencies_by_entry[entry] {
                if !selected[*dependency] {
                    selected[*dependency] = true;
                    pending.push(*dependency);
                }
            }
        }
        Ok(selected)
    }

    /// Assign selected entries to minimal topological layers in one pass.
    pub fn topological_layers(&self, selected: &[bool]) -> Vec<Vec<usize>> {
        self.topological_layers_with_sink(selected, &mut ())
    }

    /// Counted layer assignment for tests and the closed planning benchmark.
    #[cfg(any(test, feature = "planning-benchmark"))]
    #[doc(hidden)]
    pub fn topological_layers_with_planning_counters(
        &self,
        selected: &[bool],
        counters: &mut PackageGraphPlanningCounterSummary,
    ) -> Vec<Vec<usize>> {
        self.topological_layers_with_sink(selected, counters)
    }

    fn topological_layers_with_sink<S: PackageGraphPlanningCounterSink>(
        &self,
        selected: &[bool],
        counters: &mut S,
    ) -> Vec<Vec<usize>> {
        let mut layer_by_entry = vec![0usize; self.module_by_entry.len()];
        let mut layers = Vec::<Vec<usize>>::new();
        for entry in &self.topological_entries {
            if !selected.get(*entry).copied().unwrap_or(false) {
                continue;
            }
            counters.layer_assigned();
            counters.layer_dependency_edges_visited(self.dependencies_by_entry[*entry].len());
            let layer = self.dependencies_by_entry[*entry]
                .iter()
                .filter(|dependency| selected.get(**dependency).copied().unwrap_or(false))
                .map(|dependency| layer_by_entry[*dependency].saturating_add(1))
                .max()
                .unwrap_or(0);
            if layers.len() <= layer {
                layers.resize_with(layer + 1, Vec::new);
            }
            layers[layer].push(*entry);
            layer_by_entry[*entry] = layer;
        }
        layers
    }
}

/// Validated normalized lock, graph, and their operation-scoped index.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IndexedPackageLockGraph {
    lock: PackageLockManifest,
    graph: PackageLockGraph,
    index: PackageLockGraphIndex,
}

impl IndexedPackageLockGraph {
    /// Return the exact normalized lock used to build the index.
    pub fn lock(&self) -> &PackageLockManifest {
        &self.lock
    }

    /// Return normalized lock entries.
    pub fn entries(&self) -> &[PackageLockEntry] {
        &self.lock.entries
    }

    /// Return the source-compatible graph projection.
    pub fn graph(&self) -> &PackageLockGraph {
        &self.graph
    }

    /// Return the operation-scoped adjacency index.
    pub fn index(&self) -> &PackageLockGraphIndex {
        &self.index
    }
}

/// Failure while constructing a validated indexed package-lock graph.
#[derive(Debug)]
pub enum IndexedPackageLockGraphError {
    /// Existing public package-lock validation failure.
    Lock(PackageLockError),
    /// Same-call validated graph products violated an internal invariant.
    InternalInvariant(PackageLockIndexInvariantError),
}

impl fmt::Display for IndexedPackageLockGraphError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Lock(error) => write!(formatter, "{error}"),
            Self::InternalInvariant(error) => write!(formatter, "{error}"),
        }
    }
}

impl Error for IndexedPackageLockGraphError {}

impl From<PackageLockError> for IndexedPackageLockGraphError {
    fn from(error: PackageLockError) -> Self {
        Self::Lock(error)
    }
}

/// Non-serialized same-call index invariant failure.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PackageLockIndexInvariantError {
    invariant: &'static str,
}

impl PackageLockIndexInvariantError {
    fn new(invariant: &'static str) -> Self {
        Self { invariant }
    }

    /// Return the fixed internal invariant identifier.
    pub fn invariant(&self) -> &'static str {
        self.invariant
    }
}

impl fmt::Display for PackageLockIndexInvariantError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "package lock index invariant failed: {}",
            self.invariant
        )
    }
}

impl Error for PackageLockIndexInvariantError {}

/// Build a package lock from a validated manifest and explicit certificate bytes.
///
/// This builder reads no source, replay, metadata, theorem-index, or AI trace
/// paths. The manifest bytes are used only to record their exact file hash, and
/// each certificate artifact is decoded only far enough to extract module,
/// import, export, axiom-report, and certificate identity hashes.
pub fn build_package_lock_from_artifacts<'a>(
    validated: &ValidatedPackageManifest,
    manifest_path: PackagePath,
    manifest_bytes: &[u8],
    artifacts: impl IntoIterator<Item = PackageLockArtifact<'a>>,
) -> PackageLockResult<PackageLockManifest> {
    build_package_lock_from_artifacts_impl(
        validated,
        manifest_path,
        manifest_bytes,
        artifacts,
        true,
    )
}

/// Build a package lock from freshly rebuilt local certificate bytes.
///
/// This is intended for package write mode, where local certificate hashes in the manifest may
/// still describe the previous checked-in artifacts. External import hashes remain strict.
pub fn build_package_lock_from_artifacts_allowing_local_hash_updates<'a>(
    validated: &ValidatedPackageManifest,
    manifest_path: PackagePath,
    manifest_bytes: &[u8],
    artifacts: impl IntoIterator<Item = PackageLockArtifact<'a>>,
) -> PackageLockResult<PackageLockManifest> {
    build_package_lock_from_artifacts_impl(
        validated,
        manifest_path,
        manifest_bytes,
        artifacts,
        false,
    )
}

/// Build a canonical package lock and an operation-local owned artifact snapshot.
///
/// The input byte owners are consumed without copying their buffers. File hashes
/// and complete certificate decodes performed while deriving the lock are reused
/// by the returned artifact owner according to `retention_policy`.
pub fn build_package_lock_and_snapshot_owned_artifacts(
    validated: &ValidatedPackageManifest,
    manifest_path: PackagePath,
    manifest_bytes: &[u8],
    artifacts: impl IntoIterator<Item = OwnedPackageLockArtifact>,
    retention_policy: PreparedArtifactRetentionPolicy,
    observation_mode: PreparedArtifactObservationMode,
    preparation_observation: Option<&mut PackageArtifactPreparationObservation>,
) -> PackageLockResult<PackageLockArtifactSnapshots> {
    build_package_lock_and_snapshot_owned_artifacts_with_payload_observation(
        validated,
        manifest_path,
        manifest_bytes,
        artifacts,
        retention_policy,
        observation_mode,
        preparation_observation,
        None,
    )
}

/// Build a lock and artifact snapshot while also observing decoded payload freezes.
#[allow(clippy::too_many_arguments)]
pub fn build_package_lock_and_snapshot_owned_artifacts_with_payload_observation(
    validated: &ValidatedPackageManifest,
    manifest_path: PackagePath,
    manifest_bytes: &[u8],
    artifacts: impl IntoIterator<Item = OwnedPackageLockArtifact>,
    retention_policy: PreparedArtifactRetentionPolicy,
    observation_mode: PreparedArtifactObservationMode,
    preparation_observation: Option<&mut PackageArtifactPreparationObservation>,
    payload_observation: Option<&mut npa_cert::CertificatePayloadObservation>,
) -> PackageLockResult<PackageLockArtifactSnapshots> {
    let (lock, prepared) = derive_package_lock_and_snapshot_owned_artifacts(
        validated,
        manifest_path,
        manifest_bytes,
        artifacts,
        retention_policy,
        observation_mode,
        preparation_observation,
        payload_observation,
    )?;
    validate_package_lock_against_manifest_graph_impl(validated, &lock, true)?;
    Ok(PackageLockArtifactSnapshots::new(
        normalized_package_lock(&lock),
        prepared,
    ))
}

/// Build a lock, prepared artifacts, and their single operation-scoped index.
#[doc(hidden)]
#[allow(clippy::too_many_arguments)]
pub fn build_indexed_package_lock_and_snapshot_owned_artifacts_with_payload_observation(
    validated: &ValidatedPackageManifest,
    manifest_path: PackagePath,
    manifest_bytes: &[u8],
    artifacts: impl IntoIterator<Item = OwnedPackageLockArtifact>,
    retention_policy: PreparedArtifactRetentionPolicy,
    observation_mode: PreparedArtifactObservationMode,
    preparation_observation: Option<&mut PackageArtifactPreparationObservation>,
    payload_observation: Option<&mut npa_cert::CertificatePayloadObservation>,
) -> Result<(IndexedPackageLockGraph, PreparedPackageArtifacts), IndexedPackageLockGraphError> {
    let (lock, prepared) = derive_package_lock_and_snapshot_owned_artifacts(
        validated,
        manifest_path,
        manifest_bytes,
        artifacts,
        retention_policy,
        observation_mode,
        preparation_observation,
        payload_observation,
    )?;
    let indexed = validate_package_lock_against_manifest_indexed(validated, &lock)?;
    Ok((indexed, prepared))
}

#[allow(clippy::too_many_arguments)]
fn derive_package_lock_and_snapshot_owned_artifacts(
    validated: &ValidatedPackageManifest,
    manifest_path: PackagePath,
    manifest_bytes: &[u8],
    artifacts: impl IntoIterator<Item = OwnedPackageLockArtifact>,
    retention_policy: PreparedArtifactRetentionPolicy,
    observation_mode: PreparedArtifactObservationMode,
    mut preparation_observation: Option<&mut PackageArtifactPreparationObservation>,
    mut payload_observation: Option<&mut npa_cert::CertificatePayloadObservation>,
) -> PackageLockResult<(PackageLockManifest, PreparedPackageArtifacts)> {
    validate_lock_path(&manifest_path, "manifest.path")?;
    let manifest = validated.manifest();
    let mut artifact_owners = owned_artifact_map(artifacts)?;
    let mut entries = Vec::new();
    let mut prepared = PreparedPackageArtifacts::new(observation_mode);

    for (index, module) in manifest.modules.iter().enumerate() {
        let certificate_path = format!("modules[{index}].certificate");
        let derived = {
            let artifact = owned_certificate_artifact(
                &artifact_owners,
                &module.certificate,
                &certificate_path,
            )?;
            derive_local_lock_entry(
                index,
                module,
                artifact.bytes(),
                true,
                preparation_observation.as_deref_mut(),
                payload_observation.as_deref_mut(),
            )?
        };
        let owner = artifact_owners
            .remove(&module.certificate)
            .expect("owned artifact was resolved immediately above");
        let hashed = HashedPackageLockArtifact::from_lock_derivation(owner, derived.file_hash);
        prepared.push_derived(
            hashed,
            npa_cert::RetainedDecodedModuleCert::from_decoded(derived.decoded),
            retention_policy,
        );
        entries.push(derived.entry);
    }

    for (index, import) in manifest
        .imports
        .as_deref()
        .unwrap_or(&[])
        .iter()
        .enumerate()
    {
        let certificate_path = format!("imports[{index}].certificate");
        let derived = {
            let artifact = owned_certificate_artifact(
                &artifact_owners,
                &import.certificate,
                &certificate_path,
            )?;
            derive_external_lock_entry(
                index,
                import,
                artifact.bytes(),
                preparation_observation.as_deref_mut(),
                payload_observation.as_deref_mut(),
            )?
        };
        let owner = artifact_owners
            .remove(&import.certificate)
            .expect("owned artifact was resolved immediately above");
        let hashed = HashedPackageLockArtifact::from_lock_derivation(owner, derived.file_hash);
        prepared.push_derived(
            hashed,
            npa_cert::RetainedDecodedModuleCert::from_decoded(derived.decoded),
            retention_policy,
        );
        entries.push(derived.entry);
    }

    let lock = PackageLockManifest {
        schema: PACKAGE_LOCK_SCHEMA.to_owned(),
        package: manifest.package.clone(),
        version: manifest.version.clone(),
        manifest: PackageLockManifestReference {
            path: manifest_path,
            file_hash: package_file_hash(manifest_bytes),
        },
        entries,
    };
    validate_package_lock_manifest(&lock)?;
    Ok((lock, prepared))
}

fn build_package_lock_from_artifacts_impl<'a>(
    validated: &ValidatedPackageManifest,
    manifest_path: PackagePath,
    manifest_bytes: &[u8],
    artifacts: impl IntoIterator<Item = PackageLockArtifact<'a>>,
    check_local_manifest_hashes: bool,
) -> PackageLockResult<PackageLockManifest> {
    validate_lock_path(&manifest_path, "manifest.path")?;
    let manifest = validated.manifest();
    let artifact_bytes = artifact_byte_map(artifacts)?;
    let mut entries = Vec::new();

    for (index, module) in manifest.modules.iter().enumerate() {
        let certificate_path = format!("modules[{index}].certificate");
        let bytes =
            certificate_artifact_bytes(&artifact_bytes, &module.certificate, &certificate_path)?;
        entries.push(local_lock_entry(
            index,
            module,
            bytes,
            check_local_manifest_hashes,
        )?);
    }

    for (index, import) in manifest
        .imports
        .as_deref()
        .unwrap_or(&[])
        .iter()
        .enumerate()
    {
        let certificate_path = format!("imports[{index}].certificate");
        let bytes =
            certificate_artifact_bytes(&artifact_bytes, &import.certificate, &certificate_path)?;
        entries.push(external_lock_entry(index, import, bytes)?);
    }

    let lock = PackageLockManifest {
        schema: PACKAGE_LOCK_SCHEMA.to_owned(),
        package: manifest.package.clone(),
        version: manifest.version.clone(),
        manifest: PackageLockManifestReference {
            path: manifest_path,
            file_hash: package_file_hash(manifest_bytes),
        },
        entries,
    };
    validate_package_lock_manifest(&lock)?;
    validate_package_lock_against_manifest_graph_impl(
        validated,
        &lock,
        check_local_manifest_hashes,
    )?;
    Ok(normalized_package_lock(&lock))
}

/// Build a package lock by reading only the manifest file and certificate files under a package root.
pub fn build_package_lock_from_package_root(
    validated: &ValidatedPackageManifest,
    package_root: impl AsRef<Path>,
    manifest_path: PackagePath,
) -> PackageLockResult<PackageLockManifest> {
    build_package_lock_from_package_root_impl(validated, package_root, manifest_path, true)
}

/// Build a package lock from a package root while allowing local certificate hash refreshes.
///
/// This is intended for package write/sync workflows that have already rebuilt local certificate
/// files but have not yet rewritten the local module hash fields in `npa-package.toml`. External
/// import hashes remain strict.
pub fn build_package_lock_from_package_root_allowing_local_hash_updates(
    validated: &ValidatedPackageManifest,
    package_root: impl AsRef<Path>,
    manifest_path: PackagePath,
) -> PackageLockResult<PackageLockManifest> {
    build_package_lock_from_package_root_impl(validated, package_root, manifest_path, false)
}

fn build_package_lock_from_package_root_impl(
    validated: &ValidatedPackageManifest,
    package_root: impl AsRef<Path>,
    manifest_path: PackagePath,
    check_local_manifest_hashes: bool,
) -> PackageLockResult<PackageLockManifest> {
    let package_root = package_root.as_ref();
    validate_lock_path(&manifest_path, "manifest.path")?;
    let reader = PackageRootReader::open(package_root).map_err(|error| {
        PackageLockError::artifact_read_failed(
            "manifest.path",
            "manifest",
            manifest_path.as_str(),
            error.to_string(),
        )
    })?;
    let manifest_bytes =
        read_package_artifact(&reader, &manifest_path, "manifest.path", "manifest")?;
    let mut certificate_buffers = Vec::<(PackagePath, Vec<u8>)>::new();
    let manifest = validated.manifest();

    for (index, module) in manifest.modules.iter().enumerate() {
        let path = format!("modules[{index}].certificate");
        let bytes = read_certificate_artifact(&reader, &module.certificate, &path)?;
        certificate_buffers.push((module.certificate.clone(), bytes));
    }

    for (index, import) in manifest
        .imports
        .as_deref()
        .unwrap_or(&[])
        .iter()
        .enumerate()
    {
        let path = format!("imports[{index}].certificate");
        let bytes = read_certificate_artifact(&reader, &import.certificate, &path)?;
        certificate_buffers.push((import.certificate.clone(), bytes));
    }

    let artifacts = certificate_buffers
        .iter()
        .map(|(path, bytes)| PackageLockArtifact {
            path: path.clone(),
            bytes: bytes.as_slice(),
        });
    build_package_lock_from_artifacts_impl(
        validated,
        manifest_path,
        &manifest_bytes,
        artifacts,
        check_local_manifest_hashes,
    )
}

/// Validate a package lock against manifest-resolved imports and return its lock graph.
pub fn validate_package_lock_against_manifest_graph(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
) -> PackageLockResult<PackageLockGraph> {
    validate_package_lock_against_manifest_graph_impl(validated, lock, true)
}

/// Validate and normalize a manifest/lock pair for deterministic metadata comparison.
///
/// This boundary is intended for read-only comparison of an untrusted package
/// snapshot. It checks the same package identity, local hash pins, imports, and
/// graph invariants as ordinary package verification, but deliberately returns
/// no reusable verifier graph or index.
pub fn normalize_package_lock_against_manifest_for_comparison(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
) -> PackageLockResult<PackageLockManifest> {
    Ok(
        validate_package_lock_against_manifest_graph_product(validated, lock, true)?
            .normalized_lock,
    )
}

/// Validate an observed package lock while allowing local manifest hash-pin drift.
///
/// This audit-only boundary keeps package identity, lock shape, module/import
/// accountability, and external pins strict. Ordinary package verification must
/// use [`validate_package_lock_against_manifest_graph`].
#[doc(hidden)]
pub fn validate_observed_package_lock_against_manifest_graph(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
) -> PackageLockResult<PackageLockGraph> {
    validate_package_lock_against_manifest_graph_impl(validated, lock, false)
}

fn validate_package_lock_against_manifest_graph_impl(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    check_local_hashes: bool,
) -> PackageLockResult<PackageLockGraph> {
    Ok(
        validate_package_lock_against_manifest_graph_product(validated, lock, check_local_hashes)?
            .graph,
    )
}

struct NormalizedPackageLockGraphBuild {
    normalized_lock: PackageLockManifest,
    graph: PackageLockGraph,
}

fn validate_package_lock_against_manifest_graph_product(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    check_local_hashes: bool,
) -> PackageLockResult<NormalizedPackageLockGraphBuild> {
    let product = build_normalized_package_lock_graph(lock)?;
    validate_manifest_lock_entries(validated, &product.normalized_lock)?;
    validate_local_certificate_imports(validated, &product.normalized_lock, check_local_hashes)?;
    if check_local_hashes {
        validate_local_manifest_hashes(validated, &product.normalized_lock)?;
    }
    Ok(product)
}

/// Build a resolved package-lock graph and deterministic verification order.
pub fn build_package_lock_graph(lock: &PackageLockManifest) -> PackageLockResult<PackageLockGraph> {
    Ok(build_normalized_package_lock_graph(lock)?.graph)
}

fn build_normalized_package_lock_graph(
    lock: &PackageLockManifest,
) -> PackageLockResult<NormalizedPackageLockGraphBuild> {
    validate_package_lock_manifest(lock)?;
    let normalized_lock = normalized_package_lock(lock);
    let resolved_entry_imports = resolve_lock_entry_imports(&normalized_lock.entries)?;
    let topological_order =
        lock_topological_order(&normalized_lock.entries, &resolved_entry_imports)?;

    Ok(NormalizedPackageLockGraphBuild {
        normalized_lock,
        graph: PackageLockGraph {
            resolved_entry_imports,
            topological_order,
        },
    })
}

/// Build a normalized package-lock graph and one reusable operation-scoped index.
pub fn build_indexed_package_lock_graph(
    lock: &PackageLockManifest,
) -> Result<IndexedPackageLockGraph, IndexedPackageLockGraphError> {
    let product = build_normalized_package_lock_graph(lock)?;
    build_indexed_package_lock_graph_from_validated(product.normalized_lock, product.graph)
}

/// Build the closed benchmark index while collecting actual index work.
#[cfg(any(test, feature = "planning-benchmark"))]
#[doc(hidden)]
pub fn build_indexed_package_lock_graph_with_planning_counters(
    lock: &PackageLockManifest,
    counters: &mut PackageGraphPlanningCounterSummary,
) -> Result<IndexedPackageLockGraph, IndexedPackageLockGraphError> {
    let product = build_normalized_package_lock_graph(lock)?;
    build_indexed_package_lock_graph_from_validated_with_sink(
        product.normalized_lock,
        product.graph,
        counters,
    )
}

/// Strictly validate a manifest/lock pair and return its reusable graph index.
pub fn validate_package_lock_against_manifest_indexed(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
) -> Result<IndexedPackageLockGraph, IndexedPackageLockGraphError> {
    let product = validate_package_lock_against_manifest_graph_product(validated, lock, true)?;
    build_indexed_package_lock_graph_from_validated(product.normalized_lock, product.graph)
}

/// Audit-validate a manifest/lock pair and return its reusable graph index.
#[doc(hidden)]
pub fn validate_observed_package_lock_against_manifest_indexed(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
) -> Result<IndexedPackageLockGraph, IndexedPackageLockGraphError> {
    let product = validate_package_lock_against_manifest_graph_product(validated, lock, false)?;
    build_indexed_package_lock_graph_from_validated(product.normalized_lock, product.graph)
}

fn build_indexed_package_lock_graph_from_validated(
    lock: PackageLockManifest,
    graph: PackageLockGraph,
) -> Result<IndexedPackageLockGraph, IndexedPackageLockGraphError> {
    build_indexed_package_lock_graph_from_validated_with_sink(lock, graph, &mut ())
}

fn build_indexed_package_lock_graph_from_validated_with_sink<S: PackageGraphPlanningCounterSink>(
    lock: PackageLockManifest,
    graph: PackageLockGraph,
    counters: &mut S,
) -> Result<IndexedPackageLockGraph, IndexedPackageLockGraphError> {
    counters.graph_index_constructed();
    let entry_count = lock.entries.len();
    if graph.resolved_entry_imports.len() != entry_count
        || graph.topological_order.len() != entry_count
    {
        counters.graph_index_invariant_failed();
        return Err(IndexedPackageLockGraphError::InternalInvariant(
            PackageLockIndexInvariantError::new("graph_entry_count"),
        ));
    }
    let module_by_entry = lock
        .entries
        .iter()
        .map(|entry| entry.module.clone())
        .collect::<Vec<_>>();
    let entry_by_module = module_by_entry
        .iter()
        .cloned()
        .enumerate()
        .map(|(entry, module)| (module, entry))
        .collect::<BTreeMap<_, _>>();
    if entry_by_module.len() != entry_count {
        counters.graph_index_invariant_failed();
        return Err(IndexedPackageLockGraphError::InternalInvariant(
            PackageLockIndexInvariantError::new("duplicate_module_index"),
        ));
    }
    let mut topological_entries = Vec::with_capacity(entry_count);
    let mut topological_position_by_entry = vec![usize::MAX; entry_count];
    for (position, module) in graph.topological_order.iter().enumerate() {
        let entry = entry_by_module.get(module).copied().ok_or_else(|| {
            counters.graph_index_invariant_failed();
            IndexedPackageLockGraphError::InternalInvariant(PackageLockIndexInvariantError::new(
                "topological_module_missing",
            ))
        })?;
        if topological_position_by_entry[entry] != usize::MAX {
            counters.graph_index_invariant_failed();
            return Err(IndexedPackageLockGraphError::InternalInvariant(
                PackageLockIndexInvariantError::new("duplicate_topological_entry"),
            ));
        }
        topological_position_by_entry[entry] = position;
        topological_entries.push(entry);
    }
    let mut dependencies_by_entry = vec![Vec::new(); entry_count];
    let mut reverse_dependencies_by_entry = vec![Vec::new(); entry_count];
    let mut seen_dependency_epoch = vec![0usize; entry_count];
    let mut epoch = 0usize;
    for dependent in &topological_entries {
        epoch = epoch.saturating_add(1);
        let mut dependencies = Vec::with_capacity(graph.resolved_entry_imports[*dependent].len());
        for import in &graph.resolved_entry_imports[*dependent] {
            let dependency = import.entry_index;
            if dependency >= entry_count
                || module_by_entry.get(dependency) != Some(&import.module)
                || topological_position_by_entry[dependency]
                    >= topological_position_by_entry[*dependent]
                || seen_dependency_epoch[dependency] == epoch
            {
                counters.graph_index_invariant_failed();
                return Err(IndexedPackageLockGraphError::InternalInvariant(
                    PackageLockIndexInvariantError::new("dependency_edge"),
                ));
            }
            seen_dependency_epoch[dependency] = epoch;
            dependencies.push(dependency);
            reverse_dependencies_by_entry[dependency].push(*dependent);
        }
        dependencies_by_entry[*dependent] = dependencies;
    }
    Ok(IndexedPackageLockGraph {
        lock,
        graph,
        index: PackageLockGraphIndex {
            module_by_entry,
            entry_by_module,
            topological_entries,
            topological_position_by_entry,
            dependencies_by_entry,
            reverse_dependencies_by_entry,
        },
    })
}

fn artifact_byte_map<'a>(
    artifacts: impl IntoIterator<Item = PackageLockArtifact<'a>>,
) -> PackageLockResult<BTreeMap<PackagePath, &'a [u8]>> {
    let mut artifact_bytes = BTreeMap::new();
    for artifact in artifacts {
        if artifact_bytes
            .insert(artifact.path.clone(), artifact.bytes)
            .is_some()
        {
            return Err(PackageLockError::duplicate_certificate_path(
                "artifacts",
                artifact.path.as_str(),
            ));
        }
    }
    Ok(artifact_bytes)
}

fn owned_artifact_map(
    artifacts: impl IntoIterator<Item = OwnedPackageLockArtifact>,
) -> PackageLockResult<BTreeMap<PackagePath, OwnedPackageLockArtifact>> {
    let mut artifact_owners = BTreeMap::new();
    for artifact in artifacts {
        let path = artifact.path().clone();
        if artifact_owners.insert(path.clone(), artifact).is_some() {
            return Err(PackageLockError::duplicate_certificate_path(
                "artifacts",
                path.as_str(),
            ));
        }
    }
    Ok(artifact_owners)
}

fn owned_certificate_artifact<'a>(
    artifacts: &'a BTreeMap<PackagePath, OwnedPackageLockArtifact>,
    path: &PackagePath,
    error_path: &str,
) -> PackageLockResult<&'a OwnedPackageLockArtifact> {
    artifacts
        .get(path)
        .ok_or_else(|| PackageLockError::certificate_missing(error_path, path.as_str()))
}

fn certificate_artifact_bytes<'a>(
    artifacts: &BTreeMap<PackagePath, &'a [u8]>,
    path: &PackagePath,
    error_path: &str,
) -> PackageLockResult<&'a [u8]> {
    artifacts
        .get(path)
        .copied()
        .ok_or_else(|| PackageLockError::certificate_missing(error_path, path.as_str()))
}

fn read_certificate_artifact(
    package_root: &PackageRootReader,
    path: &PackagePath,
    error_path: &str,
) -> PackageLockResult<Vec<u8>> {
    match package_root.read(path) {
        Ok(bytes) => Ok(bytes),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Err(
            PackageLockError::certificate_missing(error_path, path.as_str()),
        ),
        Err(error) => Err(PackageLockError::artifact_read_failed(
            error_path,
            "certificate",
            path.as_str(),
            error.to_string(),
        )),
    }
}

fn read_package_artifact(
    package_root: &PackageRootReader,
    path: &PackagePath,
    error_path: &str,
    field: &str,
) -> PackageLockResult<Vec<u8>> {
    package_root.read(path).map_err(|error| {
        PackageLockError::artifact_read_failed(error_path, field, path.as_str(), error.to_string())
    })
}

/// One retained package-root directory capability. All root-builder reads are
/// resolved relative to this descriptor, so swapping the root path after the
/// call starts cannot redirect later manifest or certificate reads.
struct PackageRootReader {
    root: File,
}

#[cfg(unix)]
impl PackageRootReader {
    fn open(path: &Path) -> io::Result<Self> {
        use std::{
            ffi::{CString, OsString},
            os::{fd::FromRawFd, unix::ffi::OsStrExt},
            path::Component,
        };

        let mut normalized = Vec::<OsString>::new();
        let absolute = path.is_absolute();
        let start = if absolute { "/" } else { "." };
        for component in path.components() {
            match component {
                Component::RootDir | Component::CurDir => {}
                Component::Normal(value) => normalized.push(value.to_owned()),
                Component::ParentDir => {
                    if !absolute
                        && normalized
                            .last()
                            .is_none_or(|value| value.as_os_str() == std::ffi::OsStr::new(".."))
                    {
                        normalized.push(OsString::from(".."));
                    } else if normalized.pop().is_none() {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidInput,
                            "package root escapes its retained starting directory",
                        ));
                    }
                }
                Component::Prefix(_) => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "unsupported package-root prefix",
                    ));
                }
            }
        }
        // macOS exposes `/var` and `/tmp` as fixed compatibility symlinks
        // into `/private`. Rewrite only those operating-system aliases before
        // the no-follow walk; every package-controlled component remains
        // descriptor-relative and must not be a symbolic link.
        if package_root_uses_macos_compatibility_alias(path, normalized.first()) {
            normalized.insert(0, OsString::from("private"));
        }
        let root = CString::new(start).expect("filesystem start has no NUL");
        // SAFETY: the constant pathname is NUL terminated; successful ownership
        // is transferred to File exactly once.
        let descriptor = unsafe {
            libc::open(
                root.as_ptr(),
                libc::O_RDONLY | libc::O_CLOEXEC | libc::O_DIRECTORY | libc::O_NOFOLLOW,
            )
        };
        if descriptor < 0 {
            return Err(io::Error::last_os_error());
        }
        // SAFETY: descriptor is freshly owned.
        let mut directory = unsafe { File::from_raw_fd(descriptor) };
        for component in normalized {
            let component = CString::new(component.as_bytes()).map_err(|_| {
                io::Error::new(io::ErrorKind::InvalidInput, "package root contains NUL")
            })?;
            use std::os::fd::{AsRawFd, FromRawFd as _};
            // SAFETY: parent descriptor and component are live and valid.
            let descriptor = unsafe {
                libc::openat(
                    directory.as_raw_fd(),
                    component.as_ptr(),
                    libc::O_RDONLY | libc::O_CLOEXEC | libc::O_DIRECTORY | libc::O_NOFOLLOW,
                )
            };
            if descriptor < 0 {
                return Err(io::Error::last_os_error());
            }
            // SAFETY: descriptor is freshly owned.
            directory = unsafe { File::from_raw_fd(descriptor) };
        }
        Ok(Self { root: directory })
    }

    fn read(&self, path: &PackagePath) -> io::Result<Vec<u8>> {
        self.read_bounded(path, npa_cert::MAX_CERTIFICATE_BYTES as u64)
    }

    fn read_bounded(&self, path: &PackagePath, limit: u64) -> io::Result<Vec<u8>> {
        use std::os::fd::AsRawFd;
        use std::{
            ffi::CString,
            os::{fd::FromRawFd, unix::ffi::OsStrExt},
            path::Component,
        };

        validate_package_path(path, "package_file.path")
            .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "invalid package path"))?;
        let mut components = Path::new(path.as_str()).components().peekable();
        let mut directory = self.root.try_clone()?;
        while let Some(component) = components.next() {
            let Component::Normal(component) = component else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "invalid package path component",
                ));
            };
            let component = CString::new(component.as_bytes()).map_err(|_| {
                io::Error::new(io::ErrorKind::InvalidInput, "package path contains NUL")
            })?;
            if components.peek().is_some() {
                // SAFETY: retained parent descriptor and component are valid.
                let descriptor = unsafe {
                    libc::openat(
                        directory.as_raw_fd(),
                        component.as_ptr(),
                        libc::O_RDONLY | libc::O_CLOEXEC | libc::O_DIRECTORY | libc::O_NOFOLLOW,
                    )
                };
                if descriptor < 0 {
                    return Err(io::Error::last_os_error());
                }
                // SAFETY: descriptor is freshly owned.
                directory = unsafe { File::from_raw_fd(descriptor) };
            } else {
                // O_NONBLOCK avoids blocking on a hostile FIFO before fstat.
                // SAFETY: retained parent descriptor and component are valid.
                let descriptor = unsafe {
                    libc::openat(
                        directory.as_raw_fd(),
                        component.as_ptr(),
                        libc::O_RDONLY | libc::O_CLOEXEC | libc::O_NOFOLLOW | libc::O_NONBLOCK,
                    )
                };
                if descriptor < 0 {
                    return Err(io::Error::last_os_error());
                }
                // SAFETY: descriptor is freshly owned.
                let mut file = unsafe { File::from_raw_fd(descriptor) };
                let metadata = file.metadata()?;
                if !metadata.file_type().is_file() {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "package artifact is not a regular file",
                    ));
                }
                if metadata.len() > limit {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "package artifact exceeds its byte limit",
                    ));
                }
                let mut bytes = Vec::new();
                file.by_ref().take(limit + 1).read_to_end(&mut bytes)?;
                if bytes.len() as u64 > limit {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "package artifact exceeds its byte limit",
                    ));
                }
                return Ok(bytes);
            }
        }
        Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "package artifact path is empty",
        ))
    }
}

#[cfg(unix)]
fn package_root_uses_macos_compatibility_alias(
    path: &Path,
    first: Option<&std::ffi::OsString>,
) -> bool {
    use std::ffi::OsStr;

    cfg!(target_os = "macos")
        && path.is_absolute()
        && first.is_some_and(|component| {
            component == OsStr::new("var") || component == OsStr::new("tmp")
        })
}

#[cfg(not(unix))]
impl PackageRootReader {
    fn open(_path: &Path) -> io::Result<Self> {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "package-root filesystem lock building requires Unix no-follow I/O",
        ))
    }

    fn read(&self, _path: &PackagePath) -> io::Result<Vec<u8>> {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "package-root filesystem lock building requires Unix no-follow I/O",
        ))
    }
}

fn local_lock_entry(
    index: usize,
    module: &PackageModule,
    certificate_bytes: &[u8],
    check_manifest_hashes: bool,
) -> PackageLockResult<PackageLockEntry> {
    Ok(derive_local_lock_entry(
        index,
        module,
        certificate_bytes,
        check_manifest_hashes,
        None,
        None,
    )?
    .entry)
}

fn derive_local_lock_entry(
    index: usize,
    module: &PackageModule,
    certificate_bytes: &[u8],
    check_manifest_hashes: bool,
    preparation_observation: Option<&mut PackageArtifactPreparationObservation>,
    payload_observation: Option<&mut npa_cert::CertificatePayloadObservation>,
) -> PackageLockResult<DerivedPackageLockEntry> {
    let mut preparation_observation = preparation_observation;
    let base_path = format!("modules[{index}]");
    if let Some(observation) = preparation_observation.as_deref_mut() {
        observation.observe_file_hash();
    }
    let certificate_file_hash = package_file_hash(certificate_bytes);
    if check_manifest_hashes {
        check_certificate_file_hash(
            format!("{base_path}.expected_certificate_file_hash"),
            "expected_certificate_file_hash",
            module.expected_certificate_file_hash,
            certificate_file_hash,
        )?;
    }

    if let Some(observation) = preparation_observation {
        observation.observe_full_decode();
    }
    let cert = decode_lock_certificate_observed(
        certificate_bytes,
        format!("{base_path}.certificate"),
        payload_observation,
    )?;
    check_certificate_module(
        format!("{base_path}.certificate"),
        &module.module,
        &cert.header().module,
    )?;
    if check_manifest_hashes {
        check_export_hash(
            format!("{base_path}.expected_export_hash"),
            "expected_export_hash",
            module.expected_export_hash,
            PackageHash::from(cert.hashes().export_hash),
        )?;
        check_axiom_report_hash(
            format!("{base_path}.expected_axiom_report_hash"),
            "expected_axiom_report_hash",
            module.expected_axiom_report_hash,
            PackageHash::from(cert.hashes().axiom_report_hash),
        )?;
        check_certificate_hash(
            format!("{base_path}.expected_certificate_hash"),
            "expected_certificate_hash",
            module.expected_certificate_hash,
            PackageHash::from(cert.hashes().certificate_hash),
        )?;
    }

    let entry = PackageLockEntry {
        module: module.module.clone(),
        origin: PackageLockEntryOrigin::Local,
        certificate: module.certificate.clone(),
        certificate_file_hash,
        export_hash: PackageHash::from(cert.hashes().export_hash),
        axiom_report_hash: PackageHash::from(cert.hashes().axiom_report_hash),
        certificate_hash: PackageHash::from(cert.hashes().certificate_hash),
        imports: lock_imports(cert.imports(), &format!("{base_path}.certificate.imports"))?,
        package: None,
        version: None,
    };
    Ok(DerivedPackageLockEntry {
        entry,
        file_hash: certificate_file_hash,
        decoded: cert,
    })
}

fn external_lock_entry(
    index: usize,
    import: &PackageExternalImport,
    certificate_bytes: &[u8],
) -> PackageLockResult<PackageLockEntry> {
    Ok(derive_external_lock_entry(index, import, certificate_bytes, None, None)?.entry)
}

fn derive_external_lock_entry(
    index: usize,
    import: &PackageExternalImport,
    certificate_bytes: &[u8],
    preparation_observation: Option<&mut PackageArtifactPreparationObservation>,
    payload_observation: Option<&mut npa_cert::CertificatePayloadObservation>,
) -> PackageLockResult<DerivedPackageLockEntry> {
    let mut preparation_observation = preparation_observation;
    let base_path = format!("imports[{index}]");
    if let Some(observation) = preparation_observation.as_deref_mut() {
        observation.observe_file_hash();
    }
    let certificate_file_hash = package_file_hash(certificate_bytes);
    if let Some(observation) = preparation_observation {
        observation.observe_full_decode();
    }
    let cert = decode_lock_certificate_observed(
        certificate_bytes,
        format!("{base_path}.certificate"),
        payload_observation,
    )?;
    check_certificate_module(
        format!("{base_path}.certificate"),
        &import.module,
        &cert.header().module,
    )?;
    check_export_hash(
        format!("{base_path}.export_hash"),
        "export_hash",
        import.export_hash,
        PackageHash::from(cert.hashes().export_hash),
    )?;
    check_certificate_hash(
        format!("{base_path}.certificate_hash"),
        "certificate_hash",
        import.certificate_hash,
        PackageHash::from(cert.hashes().certificate_hash),
    )?;

    let entry = PackageLockEntry {
        module: import.module.clone(),
        origin: PackageLockEntryOrigin::External,
        certificate: import.certificate.clone(),
        certificate_file_hash,
        export_hash: PackageHash::from(cert.hashes().export_hash),
        axiom_report_hash: PackageHash::from(cert.hashes().axiom_report_hash),
        certificate_hash: PackageHash::from(cert.hashes().certificate_hash),
        imports: lock_imports(cert.imports(), &format!("{base_path}.certificate.imports"))?,
        package: Some(import.package.clone()),
        version: Some(import.version.clone()),
    };
    Ok(DerivedPackageLockEntry {
        entry,
        file_hash: certificate_file_hash,
        decoded: cert,
    })
}

fn decode_lock_certificate_observed(
    certificate_bytes: &[u8],
    path: impl Into<String>,
    observation: Option<&mut npa_cert::CertificatePayloadObservation>,
) -> PackageLockResult<npa_cert::ModuleCert> {
    npa_cert::decode_module_cert_observed(certificate_bytes, observation)
        .map_err(|error| PackageLockError::certificate_decode_failed(path, format!("{error:?}")))
}

fn lock_imports(
    imports: &[npa_cert::ImportEntry],
    path: &str,
) -> PackageLockResult<Vec<PackageLockImport>> {
    imports
        .iter()
        .enumerate()
        .map(|(index, import)| {
            Ok(PackageLockImport {
                module: import.module.clone(),
                export_hash: PackageHash::from(import.export_hash),
                certificate_hash: PackageHash::from(import.certificate_hash.ok_or_else(|| {
                    PackageLockError::import_certificate_hash_missing(format!(
                        "{path}[{index}].certificate_hash"
                    ))
                })?),
            })
        })
        .collect()
}

fn check_certificate_module(
    path: impl Into<String>,
    expected: &Name,
    actual: &Name,
) -> PackageLockResult<()> {
    if expected == actual {
        Ok(())
    } else {
        Err(PackageLockError::certificate_module_mismatch(
            path,
            expected.as_dotted(),
            actual.as_dotted(),
        ))
    }
}

fn check_certificate_file_hash(
    path: impl Into<String>,
    field: impl Into<String>,
    expected: PackageHash,
    actual: PackageHash,
) -> PackageLockResult<()> {
    if expected == actual {
        Ok(())
    } else {
        Err(PackageLockError::certificate_file_hash_mismatch(
            path,
            field,
            format_package_hash(&expected),
            format_package_hash(&actual),
        ))
    }
}

fn check_export_hash(
    path: impl Into<String>,
    field: impl Into<String>,
    expected: PackageHash,
    actual: PackageHash,
) -> PackageLockResult<()> {
    if expected == actual {
        Ok(())
    } else {
        Err(PackageLockError::export_hash_mismatch(
            path,
            field,
            format_package_hash(&expected),
            format_package_hash(&actual),
        ))
    }
}

fn check_axiom_report_hash(
    path: impl Into<String>,
    field: impl Into<String>,
    expected: PackageHash,
    actual: PackageHash,
) -> PackageLockResult<()> {
    if expected == actual {
        Ok(())
    } else {
        Err(PackageLockError::axiom_report_hash_mismatch(
            path,
            field,
            format_package_hash(&expected),
            format_package_hash(&actual),
        ))
    }
}

fn check_certificate_hash(
    path: impl Into<String>,
    field: impl Into<String>,
    expected: PackageHash,
    actual: PackageHash,
) -> PackageLockResult<()> {
    if expected == actual {
        Ok(())
    } else {
        Err(PackageLockError::certificate_hash_mismatch(
            path,
            field,
            format_package_hash(&expected),
            format_package_hash(&actual),
        ))
    }
}

/// Parse and validate a package lock from JSON.
pub fn parse_package_lock_json(source: &str) -> PackageLockResult<PackageLockManifest> {
    let root =
        parse_json(source).map_err(|error| PackageLockError::invalid_json(error.to_string()))?;
    let lock = parse_package_lock_value(&root)?;
    validate_package_lock_manifest(&lock)?;
    Ok(normalized_package_lock(&lock))
}

/// Validate a package lock data model without reading files or running checkers.
pub fn validate_package_lock_manifest(lock: &PackageLockManifest) -> PackageLockResult<()> {
    if lock.schema != PACKAGE_LOCK_SCHEMA {
        return Err(PackageLockError::unsupported_schema(
            "schema",
            "schema",
            PACKAGE_LOCK_SCHEMA,
            lock.schema.clone(),
        ));
    }
    validate_lock_package_id(&lock.package, "package")?;
    validate_lock_package_version(&lock.version, "version")?;
    validate_lock_path(&lock.manifest.path, "manifest.path")?;

    let mut modules = BTreeMap::<Name, usize>::new();
    let mut certificate_paths = BTreeMap::<String, usize>::new();
    for (entry_index, entry) in lock.entries.iter().enumerate() {
        let entry_path = format!("entries[{entry_index}]");
        validate_lock_module_name(&entry.module, format!("{entry_path}.module"))?;
        validate_lock_path(&entry.certificate, format!("{entry_path}.certificate"))?;
        if modules.insert(entry.module.clone(), entry_index).is_some() {
            return Err(PackageLockError::duplicate_lock_entry(
                format!("{entry_path}.module"),
                entry.module.as_dotted(),
            ));
        }
        if certificate_paths
            .insert(entry.certificate.as_str().to_owned(), entry_index)
            .is_some()
        {
            return Err(PackageLockError::duplicate_certificate_path(
                format!("{entry_path}.certificate"),
                entry.certificate.as_str(),
            ));
        }

        match entry.origin {
            PackageLockEntryOrigin::Local => {
                if let Some(package) = &entry.package {
                    return Err(PackageLockError::local_field_forbidden(
                        format!("{entry_path}.package"),
                        "package",
                        package.as_str(),
                    ));
                }
                if let Some(version) = &entry.version {
                    return Err(PackageLockError::local_field_forbidden(
                        format!("{entry_path}.version"),
                        "version",
                        version.as_str(),
                    ));
                }
            }
            PackageLockEntryOrigin::External => {
                let Some(package) = &entry.package else {
                    return Err(PackageLockError::external_field_required(
                        format!("{entry_path}.package"),
                        "package",
                    ));
                };
                let Some(version) = &entry.version else {
                    return Err(PackageLockError::external_field_required(
                        format!("{entry_path}.version"),
                        "version",
                    ));
                };
                validate_lock_package_id(package, format!("{entry_path}.package"))?;
                validate_lock_package_version(version, format!("{entry_path}.version"))?;
            }
        }

        validate_lock_imports(&entry.imports, &entry_path)?;
    }
    Ok(())
}

fn validate_lock_imports(imports: &[PackageLockImport], entry_path: &str) -> PackageLockResult<()> {
    let mut modules = BTreeSet::<Name>::new();
    for (import_index, import) in imports.iter().enumerate() {
        let import_path = format!("{entry_path}.imports[{import_index}]");
        validate_lock_module_name(&import.module, format!("{import_path}.module"))?;
        if !modules.insert(import.module.clone()) {
            return Err(PackageLockError::duplicate_import(
                format!("{import_path}.module"),
                import.module.as_dotted(),
            ));
        }
    }
    Ok(())
}

fn validate_manifest_lock_entries(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
) -> PackageLockResult<()> {
    let entry_indices = lock_entry_indices(&lock.entries);
    let manifest = validated.manifest();

    for (module_index, module) in manifest.modules.iter().enumerate() {
        let Some(entry_index) = entry_indices.get(&module.module).copied() else {
            return Err(PackageLockError::lock_entry_missing(
                format!("modules[{module_index}].module"),
                module.module.as_dotted(),
            ));
        };
        let entry = &lock.entries[entry_index];
        if entry.origin != PackageLockEntryOrigin::Local {
            return Err(PackageLockError::lock_entry_origin_mismatch(
                format!("entries[{entry_index}].origin"),
                "local",
                entry.origin.as_str(),
            ));
        }
        if entry.certificate != module.certificate {
            return Err(PackageLockError::lock_entry_identity_missing(
                format!("entries[{entry_index}].certificate"),
                "certificate",
                module.certificate.as_str(),
                entry.certificate.as_str(),
            ));
        }
    }

    for (import_index, import) in manifest
        .imports
        .as_deref()
        .unwrap_or(&[])
        .iter()
        .enumerate()
    {
        let Some(entry_index) = entry_indices.get(&import.module).copied() else {
            return Err(PackageLockError::lock_entry_missing(
                format!("imports[{import_index}].module"),
                import.module.as_dotted(),
            ));
        };
        let entry = &lock.entries[entry_index];
        if entry.origin != PackageLockEntryOrigin::External {
            return Err(PackageLockError::lock_entry_origin_mismatch(
                format!("entries[{entry_index}].origin"),
                "external",
                entry.origin.as_str(),
            ));
        }
        let entry_package = entry
            .package
            .as_ref()
            .expect("validated external lock entry carries package identity");
        if entry_package != &import.package {
            return Err(PackageLockError::lock_entry_identity_missing(
                format!("entries[{entry_index}].package"),
                "package",
                import.package.as_str(),
                entry_package.as_str(),
            ));
        }
        let entry_version = entry
            .version
            .as_ref()
            .expect("validated external lock entry carries package version");
        if entry_version != &import.version {
            return Err(PackageLockError::lock_entry_identity_missing(
                format!("entries[{entry_index}].version"),
                "version",
                import.version.as_str(),
                entry_version.as_str(),
            ));
        }
        if entry.certificate != import.certificate {
            return Err(PackageLockError::lock_entry_identity_missing(
                format!("entries[{entry_index}].certificate"),
                "certificate",
                import.certificate.as_str(),
                entry.certificate.as_str(),
            ));
        }
        check_export_hash(
            format!("entries[{entry_index}].export_hash"),
            "export_hash",
            import.export_hash,
            entry.export_hash,
        )?;
        check_certificate_hash(
            format!("entries[{entry_index}].certificate_hash"),
            "certificate_hash",
            import.certificate_hash,
            entry.certificate_hash,
        )?;
    }

    Ok(())
}

fn validate_local_manifest_hashes(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
) -> PackageLockResult<()> {
    let entry_indices = lock_entry_indices(&lock.entries);

    for module in &validated.manifest().modules {
        let entry_index = entry_indices
            .get(&module.module)
            .copied()
            .expect("validated manifest lock entry exists");
        let entry = &lock.entries[entry_index];
        check_certificate_file_hash(
            format!("entries[{entry_index}].certificate_file_hash"),
            "certificate_file_hash",
            module.expected_certificate_file_hash,
            entry.certificate_file_hash,
        )?;
        check_export_hash(
            format!("entries[{entry_index}].export_hash"),
            "export_hash",
            module.expected_export_hash,
            entry.export_hash,
        )?;
        check_axiom_report_hash(
            format!("entries[{entry_index}].axiom_report_hash"),
            "axiom_report_hash",
            module.expected_axiom_report_hash,
            entry.axiom_report_hash,
        )?;
        check_certificate_hash(
            format!("entries[{entry_index}].certificate_hash"),
            "certificate_hash",
            module.expected_certificate_hash,
            entry.certificate_hash,
        )?;
    }

    Ok(())
}

fn validate_local_certificate_imports(
    validated: &ValidatedPackageManifest,
    lock: &PackageLockManifest,
    check_import_hashes: bool,
) -> PackageLockResult<()> {
    let entry_indices = lock_entry_indices(&lock.entries);
    let manifest = validated.manifest();

    for (module_index, module) in manifest.modules.iter().enumerate() {
        let entry_index = entry_indices
            .get(&module.module)
            .copied()
            .expect("validated manifest lock entry exists");
        let entry = &lock.entries[entry_index];
        compare_manifest_imports(
            module_index,
            entry_index,
            &module.module,
            &validated.graph().resolved_module_imports[module_index],
            &entry.imports,
            check_import_hashes,
        )?;
    }

    Ok(())
}

fn compare_manifest_imports(
    module_index: usize,
    entry_index: usize,
    owner_module: &Name,
    expected_imports: &[ResolvedModuleImport],
    actual_imports: &[PackageLockImport],
    check_import_hashes: bool,
) -> PackageLockResult<()> {
    let owner_module_name = owner_module.as_dotted();
    let mut expected_by_module = BTreeMap::<Name, (usize, &ResolvedModuleImport)>::new();
    for (expected_index, expected) in expected_imports.iter().enumerate() {
        expected_by_module.insert(expected.module.clone(), (expected_index, expected));
    }

    let mut actual_modules = BTreeSet::<Name>::new();
    for (import_index, actual) in actual_imports.iter().enumerate() {
        let Some((_, expected)) = expected_by_module.get(&actual.module) else {
            // Certificate imports may include verified interface dependencies
            // that are not direct source imports in the manifest.
            continue;
        };

        if check_import_hashes
            || matches!(
                expected.kind,
                crate::graph::ResolvedModuleImportKind::External { .. }
            )
        {
            check_lock_import_export_hash(
                format!("entries[{entry_index}].imports[{import_index}].export_hash"),
                expected.export_hash,
                actual.export_hash,
            )
            .map_err(|error| error.with_module(owner_module_name.clone()))?;
            check_lock_import_certificate_hash(
                format!("entries[{entry_index}].imports[{import_index}].certificate_hash"),
                expected.certificate_hash,
                actual.certificate_hash,
            )
            .map_err(|error| error.with_module(owner_module_name.clone()))?;
        }
        actual_modules.insert(actual.module.clone());
    }

    for (expected_index, expected) in expected_imports.iter().enumerate() {
        if !actual_modules.contains(&expected.module) {
            return Err(PackageLockError::certificate_import_missing(
                format!("modules[{module_index}].imports[{expected_index}]"),
                expected.module.as_dotted(),
            )
            .with_module(owner_module_name.clone()));
        }
    }

    Ok(())
}

fn resolve_lock_entry_imports(
    entries: &[PackageLockEntry],
) -> PackageLockResult<Vec<Vec<PackageLockResolvedImport>>> {
    let entry_indices = lock_entry_indices(entries);
    let mut resolved_entries = Vec::with_capacity(entries.len());

    for (entry_index, entry) in entries.iter().enumerate() {
        let owner_module_name = entry.module.as_dotted();
        let mut resolved_imports = Vec::with_capacity(entry.imports.len());
        for (import_index, import) in entry.imports.iter().enumerate() {
            let import_path = format!("entries[{entry_index}].imports[{import_index}]");
            let Some(import_entry_index) = entry_indices.get(&import.module).copied() else {
                return Err(PackageLockError::lock_import_missing(
                    format!("{import_path}.module"),
                    import.module.as_dotted(),
                )
                .with_module(owner_module_name.clone()));
            };
            let import_entry = &entries[import_entry_index];

            if entry.origin == PackageLockEntryOrigin::External
                && import_entry.origin == PackageLockEntryOrigin::Local
            {
                return Err(PackageLockError::external_import_depends_on_local(
                    format!("{import_path}.module"),
                    import.module.as_dotted(),
                )
                .with_module(owner_module_name.clone()));
            }

            check_lock_import_export_hash(
                format!("{import_path}.export_hash"),
                import_entry.export_hash,
                import.export_hash,
            )
            .map_err(|error| error.with_module(owner_module_name.clone()))?;
            check_lock_import_certificate_hash(
                format!("{import_path}.certificate_hash"),
                import_entry.certificate_hash,
                import.certificate_hash,
            )
            .map_err(|error| error.with_module(owner_module_name.clone()))?;

            resolved_imports.push(PackageLockResolvedImport {
                module: import.module.clone(),
                entry_index: import_entry_index,
                export_hash: import.export_hash,
                certificate_hash: import.certificate_hash,
            });
        }
        resolved_entries.push(resolved_imports);
    }

    Ok(resolved_entries)
}

fn lock_entry_indices(entries: &[PackageLockEntry]) -> BTreeMap<Name, usize> {
    entries
        .iter()
        .enumerate()
        .map(|(index, entry)| (entry.module.clone(), index))
        .collect()
}

fn lock_topological_order(
    entries: &[PackageLockEntry],
    resolved_entry_imports: &[Vec<PackageLockResolvedImport>],
) -> PackageLockResult<Vec<Name>> {
    let mut states = vec![LockVisitState::Unvisited; entries.len()];
    let mut order = Vec::<Name>::with_capacity(entries.len());

    for entry_index in 0..entries.len() {
        if states[entry_index] == LockVisitState::Unvisited {
            visit_lock_entry(
                entry_index,
                entries,
                resolved_entry_imports,
                &mut states,
                &mut order,
            )?;
        }
    }

    Ok(order)
}

fn visit_lock_entry(
    entry_index: usize,
    entries: &[PackageLockEntry],
    resolved_entry_imports: &[Vec<PackageLockResolvedImport>],
    states: &mut [LockVisitState],
    order: &mut Vec<Name>,
) -> PackageLockResult<()> {
    states[entry_index] = LockVisitState::Visiting;
    let mut frames = vec![LockVisitFrame {
        entry_index,
        next_import_index: 0,
    }];

    while let Some(frame) = frames.last() {
        let entry_index = frame.entry_index;
        let import_index = frame.next_import_index;
        let Some(import) = resolved_entry_imports[entry_index].get(import_index) else {
            frames.pop();
            states[entry_index] = LockVisitState::Visited;
            order.push(entries[entry_index].module.clone());
            continue;
        };
        frames
            .last_mut()
            .expect("package-lock graph traversal has an active frame")
            .next_import_index += 1;

        match states[import.entry_index] {
            LockVisitState::Unvisited => {
                states[import.entry_index] = LockVisitState::Visiting;
                frames.push(LockVisitFrame {
                    entry_index: import.entry_index,
                    next_import_index: 0,
                });
            }
            LockVisitState::Visiting => {
                let stack = frames
                    .iter()
                    .map(|frame| frame.entry_index)
                    .collect::<Vec<_>>();
                return Err(PackageLockError::lock_import_cycle(
                    format!("entries[{entry_index}].imports"),
                    lock_cycle_path(entries, &stack, import.entry_index),
                )
                .with_module(entries[entry_index].module.as_dotted()));
            }
            LockVisitState::Visited => {}
        }
    }

    Ok(())
}

fn lock_cycle_path(entries: &[PackageLockEntry], stack: &[usize], repeated: usize) -> String {
    let start = stack
        .iter()
        .position(|entry_index| *entry_index == repeated)
        .unwrap_or(0);
    let mut cycle = stack[start..]
        .iter()
        .map(|entry_index| entries[*entry_index].module.as_dotted())
        .collect::<Vec<_>>();
    cycle.push(entries[repeated].module.as_dotted());
    cycle.join(" -> ")
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LockVisitState {
    Unvisited,
    Visiting,
    Visited,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct LockVisitFrame {
    entry_index: usize,
    next_import_index: usize,
}

fn check_lock_import_export_hash(
    path: impl Into<String>,
    expected: PackageHash,
    actual: PackageHash,
) -> PackageLockResult<()> {
    if expected == actual {
        Ok(())
    } else {
        Err(PackageLockError::lock_import_export_hash_mismatch(
            path,
            format_package_hash(&expected),
            format_package_hash(&actual),
        ))
    }
}

fn check_lock_import_certificate_hash(
    path: impl Into<String>,
    expected: PackageHash,
    actual: PackageHash,
) -> PackageLockResult<()> {
    if expected == actual {
        Ok(())
    } else {
        Err(PackageLockError::lock_import_certificate_hash_mismatch(
            path,
            format_package_hash(&expected),
            format_package_hash(&actual),
        ))
    }
}

fn parse_package_lock_value(value: &JsonValue) -> PackageLockResult<PackageLockManifest> {
    let members = expect_object(value, "$")?;
    reject_unknown_fields("$", members, TOP_LEVEL_FIELDS)?;

    Ok(PackageLockManifest {
        schema: required_string(members, "$", "schema")?,
        package: PackageId::new(required_string(members, "$", "package")?),
        version: PackageVersion::new(required_string(members, "$", "version")?),
        manifest: parse_manifest_reference(required_value(members, "$", "manifest")?)?,
        entries: required_array(members, "$", "entries")?
            .iter()
            .enumerate()
            .map(|(index, value)| parse_entry(index, value))
            .collect::<PackageLockResult<Vec<_>>>()?,
    })
}

fn parse_manifest_reference(value: &JsonValue) -> PackageLockResult<PackageLockManifestReference> {
    let path = "manifest";
    let members = expect_object(value, path)?;
    reject_unknown_fields(path, members, MANIFEST_REFERENCE_FIELDS)?;
    Ok(PackageLockManifestReference {
        path: PackagePath::new(required_string(members, path, "path")?),
        file_hash: required_hash(members, path, "file_hash")?,
    })
}

fn parse_entry(index: usize, value: &JsonValue) -> PackageLockResult<PackageLockEntry> {
    let path = format!("entries[{index}]");
    let members = expect_object(value, &path)?;
    reject_unknown_fields(&path, members, ENTRY_FIELDS)?;
    let origin_path = field_path(&path, "origin");
    let origin =
        PackageLockEntryOrigin::parse(&required_string(members, &path, "origin")?, &origin_path)?;

    Ok(PackageLockEntry {
        module: Name::from_dotted(required_string(members, &path, "module")?),
        origin,
        certificate: PackagePath::new(required_string(members, &path, "certificate")?),
        certificate_file_hash: required_hash(members, &path, "certificate_file_hash")?,
        export_hash: required_hash(members, &path, "export_hash")?,
        axiom_report_hash: required_hash(members, &path, "axiom_report_hash")?,
        certificate_hash: required_hash(members, &path, "certificate_hash")?,
        imports: required_array(members, &path, "imports")?
            .iter()
            .enumerate()
            .map(|(import_index, value)| parse_import(&path, import_index, value))
            .collect::<PackageLockResult<Vec<_>>>()?,
        package: optional_string(members, &path, "package")?.map(PackageId::new),
        version: optional_string(members, &path, "version")?.map(PackageVersion::new),
    })
}

fn parse_import(
    entry_path: &str,
    import_index: usize,
    value: &JsonValue,
) -> PackageLockResult<PackageLockImport> {
    let path = format!("{entry_path}.imports[{import_index}]");
    let members = expect_object(value, &path)?;
    reject_unknown_fields(&path, members, IMPORT_FIELDS)?;
    Ok(PackageLockImport {
        module: Name::from_dotted(required_string(members, &path, "module")?),
        export_hash: required_hash(members, &path, "export_hash")?,
        certificate_hash: required_hash(members, &path, "certificate_hash")?,
    })
}

const TOP_LEVEL_FIELDS: &[&str] = &["schema", "package", "version", "manifest", "entries"];
const MANIFEST_REFERENCE_FIELDS: &[&str] = &["path", "file_hash"];
const ENTRY_FIELDS: &[&str] = &[
    "module",
    "origin",
    "package",
    "version",
    "certificate",
    "certificate_file_hash",
    "export_hash",
    "axiom_report_hash",
    "certificate_hash",
    "imports",
];
const IMPORT_FIELDS: &[&str] = &["module", "export_hash", "certificate_hash"];

fn expect_object<'a>(value: &'a JsonValue, path: &str) -> PackageLockResult<&'a [JsonMember]> {
    value
        .object_members()
        .ok_or_else(|| PackageLockError::wrong_type(path, None, "object", value.kind().as_str()))
}

fn reject_unknown_fields(
    path: &str,
    members: &[JsonMember],
    allowed: &[&str],
) -> PackageLockResult<()> {
    let mut counts = BTreeMap::<&str, usize>::new();
    for member in members {
        *counts.entry(member.key()).or_insert(0) += 1;
    }

    if let Some((field, _)) = counts.iter().find(|(_, count)| **count > 1) {
        return Err(PackageLockError::duplicate_field(path, *field));
    }
    if let Some((field, _)) = counts
        .iter()
        .find(|(field, _)| !allowed.iter().any(|allowed| allowed == *field))
    {
        return Err(PackageLockError::unknown_field(path, *field));
    }
    Ok(())
}

fn required_value<'a>(
    members: &'a [JsonMember],
    path: &str,
    field: &str,
) -> PackageLockResult<&'a JsonValue> {
    members
        .iter()
        .find(|member| member.key() == field)
        .map(JsonMember::value)
        .ok_or_else(|| PackageLockError::missing_field(path, field))
}

fn required_string(members: &[JsonMember], path: &str, field: &str) -> PackageLockResult<String> {
    let value = required_value(members, path, field)?;
    value.string_value().map(ToOwned::to_owned).ok_or_else(|| {
        PackageLockError::wrong_type(
            field_path(path, field),
            Some(field.to_owned()),
            "string",
            value.kind().as_str(),
        )
    })
}

fn optional_string(
    members: &[JsonMember],
    path: &str,
    field: &str,
) -> PackageLockResult<Option<String>> {
    let Some(value) = members
        .iter()
        .find(|member| member.key() == field)
        .map(JsonMember::value)
    else {
        return Ok(None);
    };
    value
        .string_value()
        .map(|value| Some(value.to_owned()))
        .ok_or_else(|| {
            PackageLockError::wrong_type(
                field_path(path, field),
                Some(field.to_owned()),
                "string",
                value.kind().as_str(),
            )
        })
}

fn required_array<'a>(
    members: &'a [JsonMember],
    path: &str,
    field: &str,
) -> PackageLockResult<&'a [JsonValue]> {
    let value = required_value(members, path, field)?;
    value.array_elements().ok_or_else(|| {
        PackageLockError::wrong_type(
            field_path(path, field),
            Some(field.to_owned()),
            "array",
            value.kind().as_str(),
        )
    })
}

fn required_hash(
    members: &[JsonMember],
    path: &str,
    field: &str,
) -> PackageLockResult<PackageHash> {
    let field_path = field_path(path, field);
    let value = required_string(members, path, field)?;
    parse_package_hash(&value, &field_path)
        .map_err(|_| PackageLockError::invalid_hash_format(field_path, value))
}

fn validate_lock_module_name(name: &Name, path: impl Into<String>) -> PackageLockResult<()> {
    let path = path.into();
    if name.is_canonical() {
        Ok(())
    } else {
        Err(PackageLockError::invalid_module_name(
            path,
            name.as_dotted(),
        ))
    }
}

fn validate_lock_package_id(id: &PackageId, path: impl Into<String>) -> PackageLockResult<()> {
    let path = path.into();
    validate_package_id(id, &path)
        .map_err(|_| PackageLockError::invalid_package_id(path, id.as_str()))
}

fn validate_lock_package_version(
    version: &PackageVersion,
    path: impl Into<String>,
) -> PackageLockResult<()> {
    let path = path.into();
    validate_package_version(version, &path)
        .map_err(|_| PackageLockError::invalid_version(path, version.as_str()))
}

fn validate_lock_path(path: &PackagePath, error_path: impl Into<String>) -> PackageLockResult<()> {
    let error_path = error_path.into();
    validate_package_path(path, &error_path)
        .map_err(|_| PackageLockError::invalid_path(error_path, path.as_str()))
}

fn normalized_package_lock(lock: &PackageLockManifest) -> PackageLockManifest {
    let mut normalized = lock.clone();
    normalized
        .entries
        .sort_by(|left, right| left.module.cmp(&right.module));
    for entry in &mut normalized.entries {
        entry
            .imports
            .sort_by(|left, right| left.module.cmp(&right.module));
    }
    normalized
}

fn package_lock_json_unchecked(lock: &PackageLockManifest) -> String {
    json_object_in_order(vec![
        ("schema", json_string(&lock.schema)),
        ("package", json_string(lock.package.as_str())),
        ("version", json_string(lock.version.as_str())),
        ("manifest", manifest_reference_json(&lock.manifest)),
        (
            "entries",
            json_array(lock.entries.iter().map(entry_json_unchecked).collect()),
        ),
    ])
}

fn manifest_reference_json(manifest: &PackageLockManifestReference) -> String {
    json_object_in_order(vec![
        ("path", json_string(manifest.path.as_str())),
        ("file_hash", hash_json(manifest.file_hash)),
    ])
}

fn entry_json_unchecked(entry: &PackageLockEntry) -> String {
    let mut fields = vec![
        ("module", json_string(&entry.module.as_dotted())),
        ("origin", json_string(entry.origin.as_str())),
    ];
    if entry.origin == PackageLockEntryOrigin::External {
        fields.push((
            "package",
            json_string(
                entry
                    .package
                    .as_ref()
                    .expect("validated external entry has package")
                    .as_str(),
            ),
        ));
        fields.push((
            "version",
            json_string(
                entry
                    .version
                    .as_ref()
                    .expect("validated external entry has version")
                    .as_str(),
            ),
        ));
    }
    fields.extend([
        ("certificate", json_string(entry.certificate.as_str())),
        (
            "certificate_file_hash",
            hash_json(entry.certificate_file_hash),
        ),
        ("export_hash", hash_json(entry.export_hash)),
        ("axiom_report_hash", hash_json(entry.axiom_report_hash)),
        ("certificate_hash", hash_json(entry.certificate_hash)),
        (
            "imports",
            json_array(entry.imports.iter().map(import_json).collect()),
        ),
    ]);
    json_object_in_order(fields)
}

fn import_json(import: &PackageLockImport) -> String {
    json_object_in_order(vec![
        ("module", json_string(&import.module.as_dotted())),
        ("export_hash", hash_json(import.export_hash)),
        ("certificate_hash", hash_json(import.certificate_hash)),
    ])
}

fn json_object_in_order(fields: Vec<(&str, String)>) -> String {
    let mut out = String::new();
    out.push('{');
    for (index, (key, value)) in fields.iter().enumerate() {
        if index > 0 {
            out.push(',');
        }
        out.push_str(&json_string(key));
        out.push(':');
        out.push_str(value);
    }
    out.push('}');
    out
}

fn json_array(values: Vec<String>) -> String {
    let mut out = String::new();
    out.push('[');
    for (index, value) in values.iter().enumerate() {
        if index > 0 {
            out.push(',');
        }
        out.push_str(value);
    }
    out.push(']');
    out
}

fn hash_json(hash: PackageHash) -> String {
    json_string(&format_package_hash(&hash))
}

fn json_string(value: &str) -> String {
    let mut out = String::new();
    out.push('"');
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\u{0008}' => out.push_str("\\b"),
            '\t' => out.push_str("\\t"),
            '\n' => out.push_str("\\n"),
            '\u{000c}' => out.push_str("\\f"),
            '\r' => out.push_str("\\r"),
            '\u{0000}'..='\u{001f}' => {
                out.push_str("\\u00");
                out.push(hex_digit((ch as u8) >> 4));
                out.push(hex_digit((ch as u8) & 0x0f));
            }
            _ => out.push(ch),
        }
    }
    out.push('"');
    out
}

fn hex_digit(value: u8) -> char {
    match value {
        0..=9 => char::from(b'0' + value),
        10..=15 => char::from(b'a' + (value - 10)),
        _ => unreachable!("hex digit out of range"),
    }
}

fn field_path(path: &str, field: &str) -> String {
    if path == "$" {
        field.to_owned()
    } else {
        format!("{path}.{field}")
    }
}

#[cfg(all(test, unix))]
mod package_root_alias_tests {
    use super::*;
    use std::os::unix::fs::MetadataExt as _;
    use std::{ffi::OsString, path::PathBuf};

    #[test]
    fn package_root_reader_accepts_parent_relative_roots() {
        let current = std::env::current_dir().unwrap();
        let current_name = current.file_name().unwrap();
        let selected = PathBuf::from("..").join(current_name);
        let reader = PackageRootReader::open(&selected).unwrap();
        let reopened = reader.root.metadata().unwrap();
        let retained = std::fs::metadata(".").unwrap();

        assert_eq!(
            (reopened.dev(), reopened.ino()),
            (retained.dev(), retained.ino())
        );
    }

    #[test]
    fn macos_compatibility_alias_never_rewrites_relative_package_roots() {
        let tmp = OsString::from("tmp");
        let var = OsString::from("var");
        assert!(!package_root_uses_macos_compatibility_alias(
            Path::new("tmp/package"),
            Some(&tmp)
        ));
        assert!(!package_root_uses_macos_compatibility_alias(
            Path::new("var/package"),
            Some(&var)
        ));
        assert_eq!(
            package_root_uses_macos_compatibility_alias(Path::new("/tmp/package"), Some(&tmp)),
            cfg!(target_os = "macos")
        );
        assert_eq!(
            package_root_uses_macos_compatibility_alias(Path::new("/var/package"), Some(&var)),
            cfg!(target_os = "macos")
        );
    }
}

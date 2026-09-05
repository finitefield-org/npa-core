//! Safe cache-anchor resolution for package certificate authoring.
//!
//! This module owns placement and the capability probe shared by the diagnostic
//! result cache and targeted-authoring support cache, plus the current
//! diagnostic result-store policy. Cache entries remain untrusted sidecars.
//! Resolving an anchor never weakens package verification, and an unavailable
//! anchor suppresses all later cache filesystem operations.

use std::{
    collections::BTreeSet,
    ffi::OsStr,
    fs::{self, File},
    io::{self, Read},
    path::{Component, Path, PathBuf},
    sync::atomic::{AtomicU64 as CacheAtomicU64, Ordering as CacheOrdering},
    time::Instant,
};

#[cfg(test)]
use std::sync::atomic::{AtomicUsize, Ordering};

use npa_cert::{
    LOCAL_AUTHORING_PRODUCER_ABI, MAX_CERTIFICATE_BYTES, MAX_CERTIFICATE_EXPANDED_NODES,
    MAX_CLOSURE_EXPANDED_NODES, MAX_CLOSURE_MODULES, MAX_DECLARATIONS, MAX_EXPORTS, MAX_IMPORTS,
    MAX_LEVEL_TABLE_NODES, MAX_NAME_TABLE_ENTRIES, MAX_NESTED_VECTOR_ENTRIES,
    MAX_ROOT_EXPANDED_NODES, MAX_STRUCTURAL_DEPTH, MAX_TERM_TABLE_NODES,
};
use npa_frontend::{HumanCompileOptions, HUMAN_AUTHORING_INTERFACE_ABI};
use npa_kernel::LOCAL_AUTHORING_CONTEXT_ABI;
use npa_package::{
    format_package_hash, package_build_check_cache_default_base_relative_path,
    package_build_check_cache_key, package_build_check_cache_namespace_digest,
    package_build_check_result_entry_json, package_file_hash,
    parse_package_build_check_result_entry_json, parse_targeted_authoring_support_context_entry,
    targeted_authoring_support_context_entry_json, PackageArtifactErrorReason,
    PackageBuildCheckCacheKeyInput, PackageBuildCheckCachedStatus, PackageBuildCheckImportIdentity,
    PackageBuildCheckResultEntry, PackageCacheKeyDigest, PackageCacheNamespaceDigest,
    PackageCacheStoreVersion, PackageCacheTemporaryName, PackageHash, PackageModule,
    TargetedAuthoringSupportContextEntry, TargetedAuthoringToolchainIdentity,
    PACKAGE_BUILD_CHECK_CACHE_SCHEMA, PACKAGE_BUILD_CHECK_RESULT_SCHEMA,
    TARGETED_AUTHORING_CACHE_LIMITS_V1,
};
use sha2::{Digest, Sha256};

use crate::{
    args::PackageBuildCheckCacheMode,
    diagnostic::{CommandDiagnostic, DiagnosticKind},
    fs::no_follow_directory::{Directory, Identity},
    package::LoadedPackageRoot,
};

static NEXT_CACHE_PROBE: CacheAtomicU64 = CacheAtomicU64::new(0);
static NEXT_RESULT_TEMPORARY: CacheAtomicU64 = CacheAtomicU64::new(0);

const COMMAND: &str = "package build-certs";
const TOOL_IDENTITY_SCHEMA: &str = "npa.package.build_check_tool_identity.v0.2";

/// Semantic ABI of CLI adapters used for targeted local authoring.
pub const TARGETED_AUTHORING_ABI: &str = "npa.cli.targeted_authoring_abi.v1";
pub(crate) const TARGETED_AUTHORING_INTERFACE_RECONSTRUCTION_VERSION: &str =
    "npa.cli.human_interface_adapter.v1";

pub(crate) const TARGETED_EXTERNAL_IMPORT_LIMIT: usize = 65_536;
pub(crate) const TARGETED_EXTERNAL_DEPENDENCY_EDGE_LIMIT: usize = 1_048_576;
pub(crate) const TARGETED_EXTERNAL_CERTIFICATE_BYTES_LIMIT: usize = 256 * 1024 * 1024;

/// Result of the one cache-anchor probe performed for a package command.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PackageBuildCacheAvailability {
    /// The selected command mode does not use a local cache.
    Off,
    /// Every requested store was safely opened and its directory capability retained.
    Available,
    /// Placement, safety validation, or the capability probe failed.
    Unavailable,
}

/// Cache-anchor state retained for the lifetime of one package command.
///
/// Construct this value once with [`open_package_build_cache`]. An unavailable
/// value does not retry resolution and refuses later cache entry access.
#[derive(Debug)]
pub struct PackageBuildCache {
    state: PackageBuildCacheState,
    #[cfg(test)]
    root_resolutions: AtomicUsize,
    #[cfg(test)]
    cache_io_operations: AtomicUsize,
}

#[derive(Debug)]
enum PackageBuildCacheState {
    Off,
    Available(AvailableCache),
    Unavailable,
}

#[derive(Debug)]
struct AvailableCache {
    #[cfg_attr(not(test), allow(dead_code))]
    namespace: PackageCacheNamespaceDigest,
    #[cfg(test)]
    cache_base: PathBuf,
    stores: Vec<StoreCapability>,
}

#[derive(Debug)]
struct StoreCapability {
    version: PackageCacheStoreVersion,
    directory: Directory,
}

/// Resolve, validate, and open every requested package cache store exactly once.
///
/// `override_base`, when present, replaces the complete
/// `npa-package-audit-cache` base. Only the typed
/// `packages/<namespace>/<store>` suffix is appended to it. Passing `enabled =
/// false` returns [`PackageBuildCacheAvailability::Off`] without resolving any
/// package, Git, artifact, override, or cache path.
pub fn open_package_build_cache(
    enabled: bool,
    loaded: &LoadedPackageRoot,
    override_base: Option<&Path>,
    namespace: &PackageCacheNamespaceDigest,
    requested_stores: &[PackageCacheStoreVersion],
) -> PackageBuildCache {
    if !enabled {
        return PackageBuildCache::new(PackageBuildCacheState::Off, 0);
    }

    let state = resolve_and_open(loaded, override_base, namespace, requested_stores)
        .map(PackageBuildCacheState::Available)
        .unwrap_or(PackageBuildCacheState::Unavailable);
    PackageBuildCache::new(state, 1)
}

impl PackageBuildCache {
    fn new(state: PackageBuildCacheState, root_resolutions: usize) -> Self {
        #[cfg(not(test))]
        let _ = root_resolutions;
        Self {
            state,
            #[cfg(test)]
            root_resolutions: AtomicUsize::new(root_resolutions),
            #[cfg(test)]
            cache_io_operations: AtomicUsize::new(0),
        }
    }

    /// Return the stable result of this command's one-time cache probe.
    pub fn availability(&self) -> PackageBuildCacheAvailability {
        match self.state {
            PackageBuildCacheState::Off => PackageBuildCacheAvailability::Off,
            PackageBuildCacheState::Available(_) => PackageBuildCacheAvailability::Available,
            PackageBuildCacheState::Unavailable => PackageBuildCacheAvailability::Unavailable,
        }
    }

    /// Open one exact typed cache entry without following its final component.
    ///
    /// Off, unavailable, and unrequested stores return `Ok(None)` without any
    /// filesystem access. A present non-regular entry is an error rather than a
    /// cache hit.
    pub fn open_entry(
        &self,
        store: PackageCacheStoreVersion,
        key: &PackageCacheKeyDigest,
    ) -> io::Result<Option<File>> {
        let PackageBuildCacheState::Available(available) = &self.state else {
            return Ok(None);
        };
        let Some(store) = available
            .stores
            .iter()
            .find(|candidate| candidate.version == store)
        else {
            return Ok(None);
        };
        #[cfg(test)]
        self.cache_io_operations.fetch_add(1, Ordering::SeqCst);
        let filename = format!("{}.json", key.as_str());
        store.directory.open_regular_file(OsStr::new(&filename))
    }

    fn mark_unavailable(&mut self) {
        self.state = PackageBuildCacheState::Unavailable;
    }

    fn create_temporary_entry(
        &self,
        store: PackageCacheStoreVersion,
        temporary: &PackageCacheTemporaryName,
    ) -> io::Result<Option<File>> {
        let Some(store) = self.store(store) else {
            return Ok(None);
        };
        #[cfg(test)]
        self.cache_io_operations.fetch_add(1, Ordering::SeqCst);
        store
            .directory
            .create_new_regular_file(OsStr::new(temporary.as_str()))
            .map(Some)
    }

    #[cfg_attr(not(test), allow(dead_code))]
    fn publish_temporary_entry_no_replace(
        &self,
        store: PackageCacheStoreVersion,
        temporary: &PackageCacheTemporaryName,
        key: &PackageCacheKeyDigest,
    ) -> io::Result<()> {
        let Some(store) = self.store(store) else {
            return Err(io::Error::new(
                io::ErrorKind::NotFound,
                "cache store is unavailable",
            ));
        };
        #[cfg(test)]
        self.cache_io_operations.fetch_add(1, Ordering::SeqCst);
        let filename = format!("{}.json", key.as_str());
        store
            .directory
            .publish_file_no_replace(OsStr::new(temporary.as_str()), OsStr::new(&filename))
    }

    fn remove_temporary_entry(
        &self,
        store: PackageCacheStoreVersion,
        temporary: &PackageCacheTemporaryName,
    ) -> io::Result<()> {
        let Some(store) = self.store(store) else {
            return Ok(());
        };
        #[cfg(test)]
        self.cache_io_operations.fetch_add(1, Ordering::SeqCst);
        store.directory.remove_file(OsStr::new(temporary.as_str()))
    }

    fn store(&self, version: PackageCacheStoreVersion) -> Option<&StoreCapability> {
        let PackageBuildCacheState::Available(available) = &self.state else {
            return None;
        };
        available
            .stores
            .iter()
            .find(|candidate| candidate.version == version)
    }

    #[cfg_attr(not(test), allow(dead_code))]
    fn namespace(&self) -> Option<&PackageCacheNamespaceDigest> {
        let PackageBuildCacheState::Available(available) = &self.state else {
            return None;
        };
        Some(&available.namespace)
    }

    #[cfg(test)]
    pub(crate) fn test_cache_base(&self) -> Option<&Path> {
        match &self.state {
            PackageBuildCacheState::Available(available) => Some(&available.cache_base),
            PackageBuildCacheState::Off | PackageBuildCacheState::Unavailable => None,
        }
    }

    #[cfg(test)]
    pub(crate) fn test_counters(&self) -> PackageBuildCacheTestCounters {
        PackageBuildCacheTestCounters {
            root_resolutions: self.root_resolutions.load(Ordering::SeqCst),
            cache_io_operations: self.cache_io_operations.load(Ordering::SeqCst),
        }
    }
}

#[cfg_attr(not(test), allow(dead_code))]
mod targeted_authoring_support_store {
    use super::*;

    static NEXT_SUPPORT_TEMPORARY: CacheAtomicU64 = CacheAtomicU64::new(0);

    /// Per-command bounds shared by support-context lookup and immutable publication.
    #[derive(Debug, Default)]
    pub(crate) struct TargetedAuthoringSupportContextStoreBudget {
        addressed_keys: BTreeSet<PackageCacheKeyDigest>,
        loaded_bytes: usize,
        written_bytes: usize,
    }

    impl TargetedAuthoringSupportContextStoreBudget {
        pub(crate) fn new() -> Self {
            Self::default()
        }

        #[cfg(test)]
        pub(super) fn addressed_entries(&self) -> usize {
            self.addressed_keys.len()
        }

        pub(crate) fn loaded_bytes(&self) -> usize {
            self.loaded_bytes
        }

        #[cfg(test)]
        pub(super) fn written_bytes(&self) -> usize {
            self.written_bytes
        }

        pub(crate) fn written_bytes_for_summary(&self) -> usize {
            self.written_bytes
        }

        #[cfg(test)]
        pub(super) fn exhaust_address_budget(&mut self) {
            for index in 0..TARGETED_AUTHORING_CACHE_LIMITS_V1.cache_entries_per_command {
                let key =
                    PackageCacheKeyDigest::from_cache_key(&format!("sha256:{index:064x}")).unwrap();
                self.addressed_keys.insert(key);
            }
        }

        #[cfg(test)]
        pub(super) fn exhaust_loaded_byte_budget(&mut self) {
            self.loaded_bytes = TARGETED_AUTHORING_CACHE_LIMITS_V1.command_loaded_bytes;
        }

        #[cfg(test)]
        pub(super) fn exhaust_written_byte_budget(&mut self) {
            self.written_bytes = TARGETED_AUTHORING_CACHE_LIMITS_V1.command_written_bytes;
        }

        fn address(&mut self, key: &PackageCacheKeyDigest) -> bool {
            if self.addressed_keys.contains(key) {
                return true;
            }
            if self.addressed_keys.len()
                >= TARGETED_AUTHORING_CACHE_LIMITS_V1.cache_entries_per_command
            {
                return false;
            }
            self.addressed_keys.insert(key.clone())
        }

        fn remaining_loaded_bytes(&self) -> usize {
            TARGETED_AUTHORING_CACHE_LIMITS_V1
                .command_loaded_bytes
                .saturating_sub(self.loaded_bytes)
        }

        fn charge_loaded_bytes(&mut self, bytes: usize) -> bool {
            let Some(total) = self.loaded_bytes.checked_add(bytes) else {
                return false;
            };
            if total > TARGETED_AUTHORING_CACHE_LIMITS_V1.command_loaded_bytes {
                return false;
            }
            self.loaded_bytes = total;
            true
        }

        fn charge_written_bytes(&mut self, bytes: usize) -> bool {
            let Some(total) = self.written_bytes.checked_add(bytes) else {
                return false;
            };
            if total > TARGETED_AUTHORING_CACHE_LIMITS_V1.command_written_bytes {
                return false;
            }
            self.written_bytes = total;
            true
        }

        fn can_charge_written_bytes(&self, bytes: usize) -> bool {
            self.written_bytes.checked_add(bytes).is_some_and(|total| {
                total <= TARGETED_AUTHORING_CACHE_LIMITS_V1.command_written_bytes
            })
        }
    }

    /// Bounded exact-key support-store lookup result.
    #[derive(Clone, Debug, Eq, PartialEq)]
    pub(crate) enum TargetedAuthoringSupportContextStoreLookup {
        Hit(Box<TargetedAuthoringSupportContextEntry>),
        Missing,
        SchemaMiss,
        Stale,
        Invalid,
        Unavailable,
    }

    /// Validation classification for a destination observed during publication.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub(crate) enum TargetedAuthoringSupportContextWriterValidation {
        Stale,
        Invalid,
    }

    /// Result of one immutable support-context publication attempt.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub(crate) enum TargetedAuthoringSupportContextPublishOutcome {
        Published,
        ExistingEqual,
        Conflict(TargetedAuthoringSupportContextWriterValidation),
        Invalid,
        Unavailable,
    }

    /// Read and fully validate one exact support-context entry.
    pub(crate) fn read_targeted_authoring_support_context_store(
        cache: &PackageBuildCache,
        cache_key: &str,
        budget: &mut TargetedAuthoringSupportContextStoreBudget,
    ) -> TargetedAuthoringSupportContextStoreLookup {
        read_targeted_authoring_support_context_store_observed(cache, cache_key, budget, false).0
    }

    pub(crate) fn read_targeted_authoring_support_context_store_observed(
        cache: &PackageBuildCache,
        cache_key: &str,
        budget: &mut TargetedAuthoringSupportContextStoreBudget,
        observe_lookup: bool,
    ) -> (TargetedAuthoringSupportContextStoreLookup, u64) {
        if cache.availability() != PackageBuildCacheAvailability::Available
            || cache
                .store(PackageCacheStoreVersion::TARGETED_AUTHORING_SUPPORT)
                .is_none()
        {
            return (TargetedAuthoringSupportContextStoreLookup::Unavailable, 0);
        }
        let key = match PackageCacheKeyDigest::from_cache_key(cache_key) {
            Ok(key) => key,
            Err(_) => return (TargetedAuthoringSupportContextStoreLookup::Invalid, 0),
        };
        if !budget.address(&key) {
            return (TargetedAuthoringSupportContextStoreLookup::Invalid, 0);
        }
        let started = observe_lookup.then(Instant::now);
        let lookup =
            read_targeted_authoring_support_context_store_key(cache, cache_key, &key, budget);
        (lookup, started.map_or(0, elapsed_ns))
    }

    fn read_targeted_authoring_support_context_store_key(
        cache: &PackageBuildCache,
        cache_key: &str,
        key: &PackageCacheKeyDigest,
        budget: &mut TargetedAuthoringSupportContextStoreBudget,
    ) -> TargetedAuthoringSupportContextStoreLookup {
        let file = match cache.open_entry(PackageCacheStoreVersion::TARGETED_AUTHORING_SUPPORT, key)
        {
            Ok(Some(file)) => file,
            Ok(None) => return TargetedAuthoringSupportContextStoreLookup::Missing,
            Err(error) if support_entry_open_error_is_invalid(&error) => {
                return TargetedAuthoringSupportContextStoreLookup::Invalid;
            }
            Err(_) => return TargetedAuthoringSupportContextStoreLookup::Unavailable,
        };
        let bytes = match read_bounded_support_context_entry(file, budget) {
            SupportContextEntryRead::Bytes(bytes) => bytes,
            SupportContextEntryRead::Invalid => {
                return TargetedAuthoringSupportContextStoreLookup::Invalid;
            }
            SupportContextEntryRead::Unavailable => {
                return TargetedAuthoringSupportContextStoreLookup::Unavailable;
            }
        };
        match parse_targeted_authoring_support_context_entry(&bytes) {
            Ok(entry)
                if entry.cache_key == cache_key
                    && cache
                        .namespace()
                        .is_some_and(|value| value == &entry.namespace) =>
            {
                TargetedAuthoringSupportContextStoreLookup::Hit(Box::new(entry))
            }
            Ok(_) => TargetedAuthoringSupportContextStoreLookup::Stale,
            Err(error)
                if error.reason_code == PackageArtifactErrorReason::UnsupportedSchema
                    && error.path == "$.schema" =>
            {
                TargetedAuthoringSupportContextStoreLookup::SchemaMiss
            }
            Err(_) => TargetedAuthoringSupportContextStoreLookup::Invalid,
        }
    }

    enum SupportContextEntryRead {
        Bytes(Vec<u8>),
        Invalid,
        Unavailable,
    }

    fn read_bounded_support_context_entry(
        mut file: File,
        budget: &mut TargetedAuthoringSupportContextStoreBudget,
    ) -> SupportContextEntryRead {
        let metadata = match file.metadata() {
            Ok(metadata) => metadata,
            Err(_) => return SupportContextEntryRead::Unavailable,
        };
        let Ok(metadata_bytes) = usize::try_from(metadata.len()) else {
            return SupportContextEntryRead::Invalid;
        };
        let remaining = budget.remaining_loaded_bytes();
        if metadata_bytes > TARGETED_AUTHORING_CACHE_LIMITS_V1.support_entry_bytes
            || metadata_bytes > remaining
        {
            return SupportContextEntryRead::Invalid;
        }

        let mut bytes = Vec::with_capacity(metadata_bytes.min(4096));
        let mut buffer = [0_u8; 8192];
        loop {
            let allowed = TARGETED_AUTHORING_CACHE_LIMITS_V1
                .support_entry_bytes
                .saturating_sub(bytes.len())
                .min(budget.remaining_loaded_bytes());
            let read_capacity = allowed.min(buffer.len());
            if read_capacity == 0 {
                return match file.read(&mut buffer[..1]) {
                    Ok(0) => SupportContextEntryRead::Bytes(bytes),
                    Ok(_) => SupportContextEntryRead::Invalid,
                    Err(_) => SupportContextEntryRead::Unavailable,
                };
            }
            match file.read(&mut buffer[..read_capacity]) {
                Ok(0) => return SupportContextEntryRead::Bytes(bytes),
                Ok(read) => {
                    if !budget.charge_loaded_bytes(read) {
                        return SupportContextEntryRead::Invalid;
                    }
                    bytes.extend_from_slice(&buffer[..read]);
                }
                Err(_) => return SupportContextEntryRead::Unavailable,
            }
        }
    }

    fn support_entry_open_error_is_invalid(error: &io::Error) -> bool {
        error.kind() == io::ErrorKind::InvalidData || error.raw_os_error() == Some(libc::ELOOP)
    }

    /// Publish one canonical support entry without ever replacing an existing path.
    pub(crate) fn publish_targeted_authoring_support_context_store(
        cache: &PackageBuildCache,
        entry: &TargetedAuthoringSupportContextEntry,
        budget: &mut TargetedAuthoringSupportContextStoreBudget,
    ) -> TargetedAuthoringSupportContextPublishOutcome {
        publish_targeted_authoring_support_context_store_impl(cache, entry, budget, || {})
    }

    #[cfg(test)]
    pub(crate) fn publish_targeted_authoring_support_context_store_with_before_publish(
        cache: &PackageBuildCache,
        entry: &TargetedAuthoringSupportContextEntry,
        budget: &mut TargetedAuthoringSupportContextStoreBudget,
        before_publish: impl FnOnce(),
    ) -> TargetedAuthoringSupportContextPublishOutcome {
        publish_targeted_authoring_support_context_store_impl(cache, entry, budget, before_publish)
    }

    fn publish_targeted_authoring_support_context_store_impl(
        cache: &PackageBuildCache,
        entry: &TargetedAuthoringSupportContextEntry,
        budget: &mut TargetedAuthoringSupportContextStoreBudget,
        before_publish: impl FnOnce(),
    ) -> TargetedAuthoringSupportContextPublishOutcome {
        if cache.availability() != PackageBuildCacheAvailability::Available
            || cache
                .store(PackageCacheStoreVersion::TARGETED_AUTHORING_SUPPORT)
                .is_none()
        {
            return TargetedAuthoringSupportContextPublishOutcome::Unavailable;
        }
        if cache
            .namespace()
            .is_none_or(|value| value != &entry.namespace)
        {
            return TargetedAuthoringSupportContextPublishOutcome::Invalid;
        }
        let key = match PackageCacheKeyDigest::from_cache_key(&entry.cache_key) {
            Ok(key) => key,
            Err(_) => return TargetedAuthoringSupportContextPublishOutcome::Invalid,
        };
        if !budget.address(&key) {
            return TargetedAuthoringSupportContextPublishOutcome::Invalid;
        }
        let canonical = match targeted_authoring_support_context_entry_json(entry) {
            Ok(canonical) => canonical,
            Err(_) => return TargetedAuthoringSupportContextPublishOutcome::Invalid,
        };
        if canonical.len() > TARGETED_AUTHORING_CACHE_LIMITS_V1.support_entry_bytes
            || !budget.can_charge_written_bytes(canonical.len())
        {
            return TargetedAuthoringSupportContextPublishOutcome::Invalid;
        }

        let (temporary, mut file) = match create_support_temporary(cache, &key) {
            Some(value) => value,
            None => return TargetedAuthoringSupportContextPublishOutcome::Unavailable,
        };
        let write_succeeded = std::io::Write::write_all(&mut file, canonical.as_bytes()).is_ok()
            && file.sync_all().is_ok();
        drop(file);
        if !write_succeeded {
            let _ = cache.remove_temporary_entry(
                PackageCacheStoreVersion::TARGETED_AUTHORING_SUPPORT,
                &temporary,
            );
            return TargetedAuthoringSupportContextPublishOutcome::Unavailable;
        }
        // Count bytes only after the complete temporary payload reached stable
        // storage. This includes a later collision loser, but excludes failed
        // or partial writes.
        if !budget.charge_written_bytes(canonical.len()) {
            let _ = cache.remove_temporary_entry(
                PackageCacheStoreVersion::TARGETED_AUTHORING_SUPPORT,
                &temporary,
            );
            return TargetedAuthoringSupportContextPublishOutcome::Invalid;
        }

        before_publish();
        let published = match cache.publish_temporary_entry_no_replace(
            PackageCacheStoreVersion::TARGETED_AUTHORING_SUPPORT,
            &temporary,
            &key,
        ) {
            Ok(()) => true,
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => false,
            Err(_) => {
                let _ = cache.remove_temporary_entry(
                    PackageCacheStoreVersion::TARGETED_AUTHORING_SUPPORT,
                    &temporary,
                );
                return TargetedAuthoringSupportContextPublishOutcome::Unavailable;
            }
        };

        let winner = read_targeted_authoring_support_context_store_key(
            cache,
            &entry.cache_key,
            &key,
            budget,
        );
        let _ = cache.remove_temporary_entry(
            PackageCacheStoreVersion::TARGETED_AUTHORING_SUPPORT,
            &temporary,
        );
        match winner {
            TargetedAuthoringSupportContextStoreLookup::Hit(actual)
                if targeted_authoring_support_context_entry_json(&actual)
                    .is_ok_and(|value| value == canonical) =>
            {
                if published {
                    TargetedAuthoringSupportContextPublishOutcome::Published
                } else {
                    TargetedAuthoringSupportContextPublishOutcome::ExistingEqual
                }
            }
            TargetedAuthoringSupportContextStoreLookup::Hit(_)
            | TargetedAuthoringSupportContextStoreLookup::Stale => {
                TargetedAuthoringSupportContextPublishOutcome::Conflict(
                    TargetedAuthoringSupportContextWriterValidation::Stale,
                )
            }
            TargetedAuthoringSupportContextStoreLookup::Unavailable => {
                TargetedAuthoringSupportContextPublishOutcome::Unavailable
            }
            TargetedAuthoringSupportContextStoreLookup::Missing
            | TargetedAuthoringSupportContextStoreLookup::SchemaMiss
            | TargetedAuthoringSupportContextStoreLookup::Invalid => {
                TargetedAuthoringSupportContextPublishOutcome::Conflict(
                    TargetedAuthoringSupportContextWriterValidation::Invalid,
                )
            }
        }
    }

    fn create_support_temporary(
        cache: &PackageBuildCache,
        key: &PackageCacheKeyDigest,
    ) -> Option<(PackageCacheTemporaryName, File)> {
        for _ in 0..16 {
            let nonce = NEXT_SUPPORT_TEMPORARY.fetch_add(1, CacheOrdering::SeqCst);
            let unique = format!("{}-{nonce}", std::process::id());
            let temporary = PackageCacheTemporaryName::new(key, &unique).ok()?;
            match cache.create_temporary_entry(
                PackageCacheStoreVersion::TARGETED_AUTHORING_SUPPORT,
                &temporary,
            ) {
                Ok(Some(file)) => return Some((temporary, file)),
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
                Ok(None) | Err(_) => return None,
            }
        }
        None
    }
}

#[cfg(test)]
pub(crate) use targeted_authoring_support_store::publish_targeted_authoring_support_context_store_with_before_publish;
#[cfg_attr(not(test), allow(unused_imports))]
pub(crate) use targeted_authoring_support_store::{
    publish_targeted_authoring_support_context_store,
    read_targeted_authoring_support_context_store,
    read_targeted_authoring_support_context_store_observed,
    TargetedAuthoringSupportContextPublishOutcome, TargetedAuthoringSupportContextStoreBudget,
    TargetedAuthoringSupportContextStoreLookup, TargetedAuthoringSupportContextWriterValidation,
};

#[derive(Clone, Debug)]
pub(crate) struct PackageBuildCheckCertificateIdentity {
    pub(crate) module_index: usize,
    pub(crate) source_hash: PackageHash,
    pub(crate) output_certificate_format: String,
    pub(crate) output_core_spec: String,
}

#[derive(Debug)]
pub(crate) struct PackageBuildCheckCacheSession {
    cache: PackageBuildCache,
    tool_build_hash: Option<PackageHash>,
    unavailable_reason: Option<PackageBuildCheckCacheUnavailableReason>,
    tool_identity_observation: PackageBuildCacheToolIdentityObservation,
}

pub(crate) fn coalesced_build_check_cache_unavailable_diagnostic(
    mode: &'static str,
    result: &mut PackageBuildCheckCacheSession,
    support: Option<&TargetedAuthoringSupportCacheSession>,
) -> Option<CommandDiagnostic> {
    let mut stores = Vec::new();
    let mut reasons = BTreeSet::new();
    if let Some(reason) = result.unavailable_reason {
        stores.push(PackageCacheStoreVersion::BUILD_CHECK_RESULT.as_str());
        reasons.insert(reason.as_str());
    }
    if let Some(reason) = support.and_then(|session| session.unavailable_reason) {
        stores.push(PackageCacheStoreVersion::TARGETED_AUTHORING_SUPPORT.as_str());
        reasons.insert(reason.as_str());
    }
    if stores.is_empty() {
        return None;
    }
    result.unavailable_reason = None;
    let reason = if reasons.len() == 1 {
        reasons.into_iter().next().unwrap_or("unknown")
    } else {
        "mixed"
    };
    Some(
        CommandDiagnostic::info(
            DiagnosticKind::GeneratedArtifact,
            "build_check_cache_unavailable",
        )
        .with_field("build_check_cache")
        .with_actual_value(format!(
            "mode={mode};stores={};reason={reason}",
            stores.join("|")
        )),
    )
}

/// One safely initialized targeted-authoring support-store session.
#[derive(Debug)]
pub(crate) struct TargetedAuthoringSupportCacheSession {
    cache: PackageBuildCache,
    toolchain: Option<TargetedAuthoringToolchainIdentity>,
    unavailable_reason: Option<PackageBuildCheckCacheUnavailableReason>,
    tool_identity_observation: PackageBuildCacheToolIdentityObservation,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct PackageBuildCacheToolIdentityObservation {
    pub(crate) attempted: bool,
    pub(crate) bytes: u64,
    pub(crate) elapsed_ns: u64,
}

#[derive(Clone, Copy, Debug)]
enum PackageBuildCheckCacheUnavailableReason {
    AnchorOrCapability,
    ToolIdentity,
    ResourceLimit,
}

pub(crate) fn prepare_targeted_authoring_support_cache_session(
    loaded: &LoadedPackageRoot,
    override_base: Option<&Path>,
    observe_tool_identity: bool,
) -> TargetedAuthoringSupportCacheSession {
    let namespace = package_build_check_cache_namespace_digest(&loaded.validated);
    let cache = open_package_build_cache(
        true,
        loaded,
        override_base,
        &namespace,
        &[PackageCacheStoreVersion::TARGETED_AUTHORING_SUPPORT],
    );
    complete_targeted_authoring_support_cache_session_observed(
        cache,
        observe_tool_identity,
        targeted_authoring_toolchain_identity_observed,
    )
}

pub(crate) fn prepare_package_build_check_and_support_cache_sessions_observed(
    loaded: &LoadedPackageRoot,
    override_base: Option<&Path>,
    observe_tool_identity: bool,
) -> (
    PackageBuildCheckCacheSession,
    TargetedAuthoringSupportCacheSession,
) {
    let namespace = package_build_check_cache_namespace_digest(&loaded.validated);
    let cache = open_package_build_cache(
        true,
        loaded,
        override_base,
        &namespace,
        &[
            PackageCacheStoreVersion::BUILD_CHECK_RESULT,
            PackageCacheStoreVersion::TARGETED_AUTHORING_SUPPORT,
        ],
    );
    let (mut result_cache, mut support_cache) = split_package_build_cache_stores(
        cache,
        PackageCacheStoreVersion::BUILD_CHECK_RESULT,
        PackageCacheStoreVersion::TARGETED_AUTHORING_SUPPORT,
    );
    let result_available = result_cache.availability() == PackageBuildCacheAvailability::Available;
    let support_available =
        support_cache.availability() == PackageBuildCacheAvailability::Available;
    let tool_started =
        (observe_tool_identity && (result_available || support_available)).then(Instant::now);
    let (toolchain, tool_build_hash, tool_bytes) = if result_available || support_available {
        let (toolchain, bytes) = targeted_authoring_toolchain_identity_observed();
        let toolchain = toolchain.map(Some);
        let tool_build_hash = toolchain
            .as_ref()
            .ok()
            .and_then(Option::as_ref)
            .map(package_build_check_tool_build_hash_from_toolchain);
        (toolchain, tool_build_hash, bytes)
    } else {
        (Ok(None), None, 0)
    };
    let tool_observation = PackageBuildCacheToolIdentityObservation {
        attempted: tool_started.is_some(),
        bytes: if tool_started.is_some() {
            u64::try_from(tool_bytes).unwrap_or(u64::MAX)
        } else {
            0
        },
        elapsed_ns: tool_started.map_or(0, elapsed_ns),
    };
    match toolchain {
        Ok(toolchain) => {
            let result = if result_available {
                PackageBuildCheckCacheSession {
                    cache: result_cache,
                    tool_build_hash,
                    unavailable_reason: None,
                    tool_identity_observation: tool_observation,
                }
            } else {
                PackageBuildCheckCacheSession {
                    cache: result_cache,
                    tool_build_hash: None,
                    unavailable_reason: Some(
                        PackageBuildCheckCacheUnavailableReason::AnchorOrCapability,
                    ),
                    tool_identity_observation: tool_observation,
                }
            };
            let support = if support_available {
                TargetedAuthoringSupportCacheSession {
                    cache: support_cache,
                    toolchain,
                    unavailable_reason: None,
                    tool_identity_observation: PackageBuildCacheToolIdentityObservation::default(),
                }
            } else {
                TargetedAuthoringSupportCacheSession {
                    cache: support_cache,
                    toolchain: None,
                    unavailable_reason: Some(
                        PackageBuildCheckCacheUnavailableReason::AnchorOrCapability,
                    ),
                    tool_identity_observation: PackageBuildCacheToolIdentityObservation::default(),
                }
            };
            (result, support)
        }
        Err(_) => {
            if result_available {
                result_cache.mark_unavailable();
            }
            if support_available {
                support_cache.mark_unavailable();
            }
            (
                PackageBuildCheckCacheSession {
                    cache: result_cache,
                    tool_build_hash: None,
                    unavailable_reason: Some(if result_available {
                        PackageBuildCheckCacheUnavailableReason::ToolIdentity
                    } else {
                        PackageBuildCheckCacheUnavailableReason::AnchorOrCapability
                    }),
                    tool_identity_observation: tool_observation,
                },
                TargetedAuthoringSupportCacheSession {
                    cache: support_cache,
                    toolchain: None,
                    unavailable_reason: Some(if support_available {
                        PackageBuildCheckCacheUnavailableReason::ToolIdentity
                    } else {
                        PackageBuildCheckCacheUnavailableReason::AnchorOrCapability
                    }),
                    tool_identity_observation: PackageBuildCacheToolIdentityObservation::default(),
                },
            )
        }
    }
}

fn split_package_build_cache_stores(
    cache: PackageBuildCache,
    first: PackageCacheStoreVersion,
    second: PackageCacheStoreVersion,
) -> (PackageBuildCache, PackageBuildCache) {
    let PackageBuildCache { state, .. } = cache;
    match state {
        PackageBuildCacheState::Available(mut available) => {
            let mut first_stores = Vec::new();
            let mut second_stores = Vec::new();
            for store in available.stores.drain(..) {
                if store.version == first {
                    first_stores.push(store);
                } else if store.version == second {
                    second_stores.push(store);
                }
            }
            let first_available = AvailableCache {
                namespace: available.namespace.clone(),
                #[cfg(test)]
                cache_base: available.cache_base.clone(),
                stores: first_stores,
            };
            let second_available = AvailableCache {
                namespace: available.namespace,
                #[cfg(test)]
                cache_base: available.cache_base,
                stores: second_stores,
            };
            (
                PackageBuildCache::new(PackageBuildCacheState::Available(first_available), 1),
                PackageBuildCache::new(PackageBuildCacheState::Available(second_available), 0),
            )
        }
        PackageBuildCacheState::Off => (
            PackageBuildCache::new(PackageBuildCacheState::Off, 0),
            PackageBuildCache::new(PackageBuildCacheState::Off, 0),
        ),
        PackageBuildCacheState::Unavailable => (
            PackageBuildCache::new(PackageBuildCacheState::Unavailable, 1),
            PackageBuildCache::new(PackageBuildCacheState::Unavailable, 0),
        ),
    }
}

fn complete_targeted_authoring_support_cache_session_observed(
    mut cache: PackageBuildCache,
    observe_tool_identity: bool,
    acquire_tool_identity: impl FnOnce() -> (io::Result<TargetedAuthoringToolchainIdentity>, usize),
) -> TargetedAuthoringSupportCacheSession {
    if cache.availability() != PackageBuildCacheAvailability::Available {
        return TargetedAuthoringSupportCacheSession {
            cache,
            toolchain: None,
            unavailable_reason: Some(PackageBuildCheckCacheUnavailableReason::AnchorOrCapability),
            tool_identity_observation: PackageBuildCacheToolIdentityObservation::default(),
        };
    }
    let started = observe_tool_identity.then(Instant::now);
    let (toolchain, bytes) = acquire_tool_identity();
    let observation = PackageBuildCacheToolIdentityObservation {
        attempted: observe_tool_identity,
        bytes: if observe_tool_identity {
            u64::try_from(bytes).unwrap_or(u64::MAX)
        } else {
            0
        },
        elapsed_ns: started.map_or(0, elapsed_ns),
    };
    match toolchain {
        Ok(toolchain) => TargetedAuthoringSupportCacheSession {
            cache,
            toolchain: Some(toolchain),
            unavailable_reason: None,
            tool_identity_observation: observation,
        },
        Err(_) => {
            cache.mark_unavailable();
            TargetedAuthoringSupportCacheSession {
                cache,
                toolchain: None,
                unavailable_reason: Some(PackageBuildCheckCacheUnavailableReason::ToolIdentity),
                tool_identity_observation: observation,
            }
        }
    }
}

#[cfg(test)]
fn complete_targeted_authoring_support_cache_session(
    cache: PackageBuildCache,
    acquire_tool_identity: impl FnOnce() -> io::Result<TargetedAuthoringToolchainIdentity>,
) -> TargetedAuthoringSupportCacheSession {
    complete_targeted_authoring_support_cache_session_observed(cache, false, || {
        (acquire_tool_identity(), 0)
    })
}

impl TargetedAuthoringSupportCacheSession {
    pub(crate) fn toolchain(&self) -> Option<&TargetedAuthoringToolchainIdentity> {
        self.toolchain.as_ref()
    }

    pub(crate) const fn tool_identity_observation(
        &self,
    ) -> PackageBuildCacheToolIdentityObservation {
        self.tool_identity_observation
    }

    #[cfg(test)]
    pub(crate) fn lookup(
        &mut self,
        cache_key: &str,
        budget: &mut TargetedAuthoringSupportContextStoreBudget,
    ) -> TargetedAuthoringSupportContextStoreLookup {
        self.lookup_observed(cache_key, budget, false).0
    }

    pub(crate) fn lookup_observed(
        &mut self,
        cache_key: &str,
        budget: &mut TargetedAuthoringSupportContextStoreBudget,
        observe_lookup: bool,
    ) -> (TargetedAuthoringSupportContextStoreLookup, u64) {
        if self.toolchain.is_none() {
            return (TargetedAuthoringSupportContextStoreLookup::Unavailable, 0);
        }
        let (lookup, elapsed_ns) = read_targeted_authoring_support_context_store_observed(
            &self.cache,
            cache_key,
            budget,
            observe_lookup,
        );
        if lookup == TargetedAuthoringSupportContextStoreLookup::Unavailable {
            self.cache.mark_unavailable();
            self.toolchain = None;
            self.unavailable_reason
                .get_or_insert(PackageBuildCheckCacheUnavailableReason::AnchorOrCapability);
        }
        (lookup, elapsed_ns)
    }

    pub(crate) fn namespace(&self) -> Option<&PackageCacheNamespaceDigest> {
        self.cache.namespace()
    }

    pub(crate) fn publish(
        &mut self,
        entry: &TargetedAuthoringSupportContextEntry,
        budget: &mut TargetedAuthoringSupportContextStoreBudget,
    ) -> TargetedAuthoringSupportContextPublishOutcome {
        if self.toolchain.is_none() {
            return TargetedAuthoringSupportContextPublishOutcome::Unavailable;
        }
        let outcome = publish_targeted_authoring_support_context_store(&self.cache, entry, budget);
        if outcome == TargetedAuthoringSupportContextPublishOutcome::Unavailable {
            self.cache.mark_unavailable();
            self.toolchain = None;
            self.unavailable_reason
                .get_or_insert(PackageBuildCheckCacheUnavailableReason::AnchorOrCapability);
        }
        outcome
    }

    pub(crate) fn unavailable_diagnostic(&self) -> Option<CommandDiagnostic> {
        self.unavailable_reason
            .map(targeted_authoring_support_cache_unavailable_diagnostic)
    }

    pub(crate) fn disable_for_resource_limit(&mut self) {
        self.cache.mark_unavailable();
        self.toolchain = None;
        self.unavailable_reason = Some(PackageBuildCheckCacheUnavailableReason::ResourceLimit);
    }
}

impl PackageBuildCheckCacheUnavailableReason {
    const fn as_str(self) -> &'static str {
        match self {
            Self::AnchorOrCapability => "anchor_or_capability",
            Self::ToolIdentity => "tool_identity",
            Self::ResourceLimit => "resource_limit",
        }
    }
}

#[derive(Debug)]
pub(crate) struct PackageBuildCheckCacheRun {
    cache: PackageBuildCache,
    keyed_entries: Vec<PackageBuildCheckKeyedEntry>,
    lookups: Vec<PackageBuildCheckCacheLookup>,
    summary: PackageBuildCheckCacheSummary,
    unavailable_reason: Option<PackageBuildCheckCacheUnavailableReason>,
    bytes_loaded: usize,
    bytes_written: usize,
    lookup_ns: u64,
}

#[derive(Clone, Debug)]
struct PackageBuildCheckCacheSummary {
    mode: PackageBuildCheckCacheMode,
    hits: usize,
    misses: usize,
    stale: usize,
    schema_misses: usize,
    written: usize,
    live_builds: usize,
    trusted: bool,
    build_evidence: bool,
    bytes_loaded: usize,
    bytes_written: usize,
}

/// Diagnostic result-store outcomes for entries whose live target build produced an identity.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct PackageBuildCheckCacheOutcomeCounts {
    pub(crate) hits: usize,
    pub(crate) misses: usize,
    pub(crate) stale: usize,
    pub(crate) schema_misses: usize,
    pub(crate) written: usize,
    pub(crate) bytes_loaded: usize,
    pub(crate) bytes_written: usize,
}

#[derive(Clone, Debug)]
struct PackageBuildCheckKeyedEntry {
    module: npa_cert::Name,
    key_input: PackageBuildCheckCacheKeyInput,
    cache_key: String,
}

#[derive(Clone, Debug)]
enum PackageBuildCheckCacheLookup {
    Hit(Box<PackageBuildCheckResultEntry>),
    Missing,
    SchemaMiss,
    Stale,
}

pub(crate) fn prepare_package_build_check_cache_session_observed(
    loaded: &LoadedPackageRoot,
    override_base: Option<&Path>,
    observe_tool_identity: bool,
) -> PackageBuildCheckCacheSession {
    let namespace = package_build_check_cache_namespace_digest(&loaded.validated);
    let cache = open_package_build_cache(
        true,
        loaded,
        override_base,
        &namespace,
        &[PackageCacheStoreVersion::BUILD_CHECK_RESULT],
    );
    complete_package_build_check_cache_session_observed(cache, observe_tool_identity, || {
        let (toolchain, bytes) = targeted_authoring_toolchain_identity_observed();
        (
            toolchain
                .map(|toolchain| package_build_check_tool_build_hash_from_toolchain(&toolchain)),
            bytes,
        )
    })
}

fn complete_package_build_check_cache_session_observed(
    mut cache: PackageBuildCache,
    observe_tool_identity: bool,
    acquire_tool_identity: impl FnOnce() -> (io::Result<PackageHash>, usize),
) -> PackageBuildCheckCacheSession {
    if cache.availability() != PackageBuildCacheAvailability::Available {
        return PackageBuildCheckCacheSession {
            cache,
            tool_build_hash: None,
            unavailable_reason: Some(PackageBuildCheckCacheUnavailableReason::AnchorOrCapability),
            tool_identity_observation: PackageBuildCacheToolIdentityObservation::default(),
        };
    }
    let started = observe_tool_identity.then(Instant::now);
    let (tool_build_hash, bytes) = acquire_tool_identity();
    let observation = PackageBuildCacheToolIdentityObservation {
        attempted: observe_tool_identity,
        bytes: if observe_tool_identity {
            u64::try_from(bytes).unwrap_or(u64::MAX)
        } else {
            0
        },
        elapsed_ns: started.map_or(0, elapsed_ns),
    };
    match tool_build_hash {
        Ok(tool_build_hash) => PackageBuildCheckCacheSession {
            cache,
            tool_build_hash: Some(tool_build_hash),
            unavailable_reason: None,
            tool_identity_observation: observation,
        },
        Err(_) => {
            cache.mark_unavailable();
            PackageBuildCheckCacheSession {
                cache,
                tool_build_hash: None,
                unavailable_reason: Some(PackageBuildCheckCacheUnavailableReason::ToolIdentity),
                tool_identity_observation: observation,
            }
        }
    }
}

impl PackageBuildCheckCacheSession {
    pub(crate) const fn tool_identity_observation(
        &self,
    ) -> PackageBuildCacheToolIdentityObservation {
        self.tool_identity_observation
    }

    pub(crate) fn unavailable_diagnostic(&self) -> Option<CommandDiagnostic> {
        self.unavailable_reason
            .map(package_build_check_cache_unavailable_diagnostic)
    }
}

pub(crate) fn prepare_package_build_check_cache_run(
    session: PackageBuildCheckCacheSession,
    loaded: &LoadedPackageRoot,
    certificates: &[PackageBuildCheckCertificateIdentity],
    observe_lookup: bool,
) -> PackageBuildCheckCacheRun {
    let mut summary = PackageBuildCheckCacheSummary::new(PackageBuildCheckCacheMode::ReadThrough);
    summary.live_builds = certificates.len();
    let keyed_entries = session
        .tool_build_hash
        .map_or_else(Vec::new, |tool_build_hash| {
            package_build_check_cache_key_inputs(loaded, certificates, tool_build_hash)
        });
    let mut bytes_loaded = 0;
    let mut lookup_ns = 0;
    let lookups = keyed_entries
        .iter()
        .map(|entry| {
            read_package_build_check_cache_lookup_observed(
                &session.cache,
                &entry.cache_key,
                &mut bytes_loaded,
                &mut lookup_ns,
                observe_lookup,
            )
        })
        .collect();
    PackageBuildCheckCacheRun {
        cache: session.cache,
        keyed_entries,
        lookups,
        summary,
        unavailable_reason: session.unavailable_reason,
        bytes_loaded,
        bytes_written: 0,
        lookup_ns,
    }
}

impl PackageBuildCheckCacheRun {
    pub(crate) fn unavailable_diagnostic(&self) -> Option<CommandDiagnostic> {
        self.unavailable_reason
            .map(package_build_check_cache_unavailable_diagnostic)
    }

    pub(crate) const fn lookup_ms(&self) -> u64 {
        self.lookup_ns / 1_000_000
    }
}

pub(crate) fn finalize_package_build_check_cache_run(
    run: PackageBuildCheckCacheRun,
    status: PackageBuildCheckCachedStatus,
    diagnostic_reason: Option<&str>,
) -> (CommandDiagnostic, PackageBuildCheckCacheOutcomeCounts) {
    let summary = finalize_package_build_check_cache_summary(run, status, diagnostic_reason);
    let outcomes = PackageBuildCheckCacheOutcomeCounts::from_summary(&summary);
    (
        package_build_check_cache_summary_diagnostic(&summary),
        outcomes,
    )
}

pub(crate) fn finalize_package_build_check_cache_run_outcomes(
    run: PackageBuildCheckCacheRun,
    status: PackageBuildCheckCachedStatus,
    diagnostic_reason: Option<&str>,
) -> PackageBuildCheckCacheOutcomeCounts {
    let summary = finalize_package_build_check_cache_summary(run, status, diagnostic_reason);
    PackageBuildCheckCacheOutcomeCounts::from_summary(&summary)
}

impl PackageBuildCheckCacheOutcomeCounts {
    fn from_summary(summary: &PackageBuildCheckCacheSummary) -> Self {
        Self {
            hits: summary.hits,
            misses: summary.misses,
            stale: summary.stale,
            schema_misses: summary.schema_misses,
            written: summary.written,
            bytes_loaded: summary.bytes_loaded,
            bytes_written: summary.bytes_written,
        }
    }
}

fn finalize_package_build_check_cache_summary(
    mut run: PackageBuildCheckCacheRun,
    status: PackageBuildCheckCachedStatus,
    diagnostic_reason: Option<&str>,
) -> PackageBuildCheckCacheSummary {
    for (keyed, lookup) in run.keyed_entries.iter().zip(run.lookups.iter()) {
        let expected_entry =
            package_build_check_cache_result_entry(keyed, status, diagnostic_reason);
        match lookup {
            PackageBuildCheckCacheLookup::Hit(entry)
                if package_build_check_cache_entries_equal(entry, &expected_entry) =>
            {
                run.summary.hits += 1;
            }
            PackageBuildCheckCacheLookup::Hit(_) | PackageBuildCheckCacheLookup::Stale => {
                run.summary.stale += 1;
                if write_package_build_check_cache_entry_observed(
                    &run.cache,
                    &expected_entry,
                    &mut run.bytes_loaded,
                    &mut run.bytes_written,
                ) {
                    run.summary.written += 1;
                }
            }
            PackageBuildCheckCacheLookup::Missing => {
                run.summary.misses += 1;
                if write_package_build_check_cache_entry_observed(
                    &run.cache,
                    &expected_entry,
                    &mut run.bytes_loaded,
                    &mut run.bytes_written,
                ) {
                    run.summary.written += 1;
                }
            }
            PackageBuildCheckCacheLookup::SchemaMiss => {
                run.summary.schema_misses += 1;
                if write_package_build_check_cache_entry_observed(
                    &run.cache,
                    &expected_entry,
                    &mut run.bytes_loaded,
                    &mut run.bytes_written,
                ) {
                    run.summary.written += 1;
                }
            }
        }
    }
    run.summary.bytes_loaded = run.bytes_loaded;
    run.summary.bytes_written = run.bytes_written;
    run.summary
}

fn package_build_check_cache_key_inputs(
    loaded: &LoadedPackageRoot,
    certificates: &[PackageBuildCheckCertificateIdentity],
    tool_build_hash: PackageHash,
) -> Vec<PackageBuildCheckKeyedEntry> {
    let manifest = loaded.validated.manifest();
    certificates
        .iter()
        .map(|certificate| {
            let module = &manifest.modules[certificate.module_index];
            let direct_imports = loaded.validated.graph().resolved_module_imports
                [certificate.module_index]
                .iter()
                .map(|import| PackageBuildCheckImportIdentity {
                    module: import.module.clone(),
                    export_hash: import.export_hash,
                    certificate_hash: import.certificate_hash,
                })
                .collect::<Vec<_>>();
            let key_input = PackageBuildCheckCacheKeyInput {
                schema: PACKAGE_BUILD_CHECK_CACHE_SCHEMA.to_owned(),
                tool_version: env!("CARGO_PKG_VERSION").to_owned(),
                tool_build_hash,
                package_core_profile: manifest.core_spec.clone(),
                package_certificate_profile: manifest.certificate_format.clone(),
                output_certificate_format: certificate.output_certificate_format.clone(),
                output_core_spec: certificate.output_core_spec.clone(),
                module: module.module.clone(),
                source_hash: certificate.source_hash,
                expected_source_hash: module.expected_source_hash,
                direct_imports,
                compiler_options: package_build_check_compiler_options(module),
                package_metadata_mode: "check".to_owned(),
                producer_profile: module.producer_profile.clone(),
                expected_certificate_file_hash: module.expected_certificate_file_hash,
                expected_export_hash: module.expected_export_hash,
                expected_axiom_report_hash: module.expected_axiom_report_hash,
                expected_certificate_hash: module.expected_certificate_hash,
            };
            let cache_key = package_build_check_cache_key(&key_input);
            PackageBuildCheckKeyedEntry {
                module: module.module.clone(),
                key_input,
                cache_key,
            }
        })
        .collect()
}

fn package_build_check_compiler_options(module: &PackageModule) -> Vec<String> {
    package_build_check_compiler_options_with_human(module, &HumanCompileOptions::default())
}

fn package_build_check_compiler_options_with_human(
    module: &PackageModule,
    human: &HumanCompileOptions,
) -> Vec<String> {
    let mut options = targeted_authoring_frontend_compiler_options(human);
    options.push(format!(
        "producer_profile={}",
        module.producer_profile.as_deref().unwrap_or("default")
    ));
    options.extend(targeted_authoring_resource_compiler_options());
    options
}

pub(crate) fn targeted_authoring_semantic_compiler_options() -> Vec<String> {
    targeted_authoring_semantic_compiler_options_with_human(&HumanCompileOptions::default())
}

fn targeted_authoring_semantic_compiler_options_with_human(
    human: &HumanCompileOptions,
) -> Vec<String> {
    let mut options = targeted_authoring_frontend_compiler_options(human);
    options.extend(targeted_authoring_resource_compiler_options());
    options
}

fn targeted_authoring_frontend_compiler_options(human: &HumanCompileOptions) -> Vec<String> {
    let typeclass = &human.typeclass_search_policy;
    vec![
        "frontend=human".to_owned(),
        format!("frontend_abi={HUMAN_AUTHORING_INTERFACE_ABI}"),
        format!("producer_abi={LOCAL_AUTHORING_PRODUCER_ABI}"),
        format!("kernel_abi={LOCAL_AUTHORING_CONTEXT_ABI}"),
        format!(
            "human.max_notation_candidates={}",
            human.max_notation_candidates
        ),
        format!("human.typeclass.max_depth={}", typeclass.max_depth),
        format!(
            "human.typeclass.max_candidates={}",
            typeclass.max_candidates
        ),
        format!("human.typeclass.timeout_ms={}", typeclass.timeout_ms),
        format!(
            "human.enable_equation_compiler={}",
            human.enable_equation_compiler
        ),
        "axiom_policy=package_namespace".to_owned(),
    ]
}

fn targeted_authoring_resource_compiler_options() -> Vec<String> {
    vec![
        "resource_policy=npa.cli.package_build_check.resource_policy.v1".to_owned(),
        format!("resource.external_imports={TARGETED_EXTERNAL_IMPORT_LIMIT}"),
        format!("resource.external_dependency_edges={TARGETED_EXTERNAL_DEPENDENCY_EDGE_LIMIT}"),
        format!("resource.external_certificate_bytes={TARGETED_EXTERNAL_CERTIFICATE_BYTES_LIMIT}"),
        format!("resource.certificate_bytes={MAX_CERTIFICATE_BYTES}"),
        format!("resource.certificate_expanded_nodes={MAX_CERTIFICATE_EXPANDED_NODES}"),
        format!("resource.closure_expanded_nodes={MAX_CLOSURE_EXPANDED_NODES}"),
        format!("resource.closure_modules={MAX_CLOSURE_MODULES}"),
        format!("resource.declarations={MAX_DECLARATIONS}"),
        format!("resource.exports={MAX_EXPORTS}"),
        format!("resource.imports={MAX_IMPORTS}"),
        format!("resource.level_table_nodes={MAX_LEVEL_TABLE_NODES}"),
        format!("resource.name_table_entries={MAX_NAME_TABLE_ENTRIES}"),
        format!("resource.nested_vector_entries={MAX_NESTED_VECTOR_ENTRIES}"),
        format!("resource.root_expanded_nodes={MAX_ROOT_EXPANDED_NODES}"),
        format!("resource.structural_depth={MAX_STRUCTURAL_DEPTH}"),
        format!("resource.term_table_nodes={MAX_TERM_TABLE_NODES}"),
    ]
}

#[cfg(test)]
fn package_build_check_tool_build_hash_from_reader(
    mut executable: impl Read,
    cli_abi: &str,
    frontend_abi: &str,
    producer_abi: &str,
    kernel_abi: &str,
) -> io::Result<PackageHash> {
    let executable_hash = bounded_executable_hash(&mut executable)?;
    Ok(package_build_check_tool_build_hash_from_executable_hash(
        executable_hash,
        cli_abi,
        frontend_abi,
        producer_abi,
        kernel_abi,
    ))
}

fn package_build_check_tool_build_hash_from_executable_hash(
    executable_hash: PackageHash,
    cli_abi: &str,
    frontend_abi: &str,
    producer_abi: &str,
    kernel_abi: &str,
) -> PackageHash {
    let material = format!(
        "schema={TOOL_IDENTITY_SCHEMA}\ncommand={COMMAND}\nversion={}\nexecutable_hash={}\ncli_abi={cli_abi}\nfrontend_abi={frontend_abi}\nproducer_abi={producer_abi}\nkernel_abi={kernel_abi}\n",
        env!("CARGO_PKG_VERSION"),
        format_package_hash(&executable_hash),
    );
    package_file_hash(material.as_bytes())
}

fn package_build_check_tool_build_hash_from_toolchain(
    toolchain: &TargetedAuthoringToolchainIdentity,
) -> PackageHash {
    package_build_check_tool_build_hash_from_executable_hash(
        toolchain.executable_hash,
        &toolchain.cli_authoring_abi,
        &toolchain.frontend_authoring_abi,
        &toolchain.producer_authoring_abi,
        &toolchain.kernel_authoring_abi,
    )
}

fn targeted_authoring_toolchain_identity_observed(
) -> (io::Result<TargetedAuthoringToolchainIdentity>, usize) {
    let path = match std::env::current_exe() {
        Ok(path) => path,
        Err(error) => return (Err(error), 0),
    };
    let executable = match crate::fs::read_bounded_regular_file(
        &path,
        TARGETED_AUTHORING_CACHE_LIMITS_V1.tool_identity_bytes as u64,
    ) {
        Ok(executable) => executable,
        Err(error) => return (Err(error), 0),
    };
    let bytes = executable.len();
    let mut observed_bytes = 0;
    let executable_hash =
        match bounded_executable_hash_observed(executable.as_slice(), &mut observed_bytes) {
            Ok(hash) => hash,
            Err(error) => return (Err(error), bytes),
        };
    debug_assert_eq!(observed_bytes, bytes);
    (
        Ok(TargetedAuthoringToolchainIdentity {
            executable_hash,
            cli_authoring_abi: TARGETED_AUTHORING_ABI.to_owned(),
            frontend_authoring_abi: HUMAN_AUTHORING_INTERFACE_ABI.to_owned(),
            producer_authoring_abi: LOCAL_AUTHORING_PRODUCER_ABI.to_owned(),
            kernel_authoring_abi: LOCAL_AUTHORING_CONTEXT_ABI.to_owned(),
        }),
        bytes,
    )
}

#[cfg(test)]
fn bounded_executable_hash(mut executable: impl Read) -> io::Result<PackageHash> {
    let mut bytes = 0;
    bounded_executable_hash_observed(&mut executable, &mut bytes)
}

fn bounded_executable_hash_observed(
    mut executable: impl Read,
    observed_bytes: &mut usize,
) -> io::Result<PackageHash> {
    let mut hasher = Sha256::new();
    let mut total = 0usize;
    let mut buffer = [0_u8; 64 * 1024];
    loop {
        let read = executable.read(&mut buffer)?;
        if read == 0 {
            break;
        }
        total = total
            .checked_add(read)
            .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "tool identity too large"))?;
        if total > TARGETED_AUTHORING_CACHE_LIMITS_V1.tool_identity_bytes {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "tool identity exceeds the bounded byte limit",
            ));
        }
        hasher.update(&buffer[..read]);
        *observed_bytes = total;
    }
    let executable_digest: [u8; 32] = hasher.finalize().into();
    Ok(PackageHash::new(executable_digest))
}

fn elapsed_ns(started: Instant) -> u64 {
    u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX)
}

fn read_package_build_check_cache_lookup_observed(
    cache: &PackageBuildCache,
    cache_key: &str,
    bytes_loaded: &mut usize,
    lookup_ns: &mut u64,
    observe_lookup: bool,
) -> PackageBuildCheckCacheLookup {
    let key = match PackageCacheKeyDigest::from_cache_key(cache_key) {
        Ok(key) => key,
        Err(_) => return PackageBuildCheckCacheLookup::Stale,
    };
    let started = observe_lookup.then(Instant::now);
    let lookup = read_package_build_check_cache_key(cache, cache_key, &key, bytes_loaded);
    if let Some(started) = started {
        *lookup_ns = lookup_ns.saturating_add(elapsed_ns(started));
    }
    lookup
}

fn read_package_build_check_cache_key(
    cache: &PackageBuildCache,
    cache_key: &str,
    key: &PackageCacheKeyDigest,
    bytes_loaded: &mut usize,
) -> PackageBuildCheckCacheLookup {
    let file = match cache.open_entry(PackageCacheStoreVersion::BUILD_CHECK_RESULT, key) {
        Ok(Some(file)) => file,
        Ok(None) => return PackageBuildCheckCacheLookup::Missing,
        Err(_) => return PackageBuildCheckCacheLookup::Stale,
    };
    let (read_result, read) = read_bytes_through_limit_observed(
        file,
        TARGETED_AUTHORING_CACHE_LIMITS_V1.result_entry_bytes,
    );
    *bytes_loaded = bytes_loaded.saturating_add(read);
    let bytes = match read_result {
        Ok(bytes) if bytes.len() <= TARGETED_AUTHORING_CACHE_LIMITS_V1.result_entry_bytes => bytes,
        Ok(_) | Err(_) => return PackageBuildCheckCacheLookup::Stale,
    };
    let source = match String::from_utf8(bytes) {
        Ok(source) => source,
        Err(_) => return PackageBuildCheckCacheLookup::Stale,
    };
    match parse_package_build_check_result_entry_json(&source) {
        Ok(entry) if entry.cache_key == cache_key => {
            PackageBuildCheckCacheLookup::Hit(Box::new(entry))
        }
        Ok(_) => PackageBuildCheckCacheLookup::Stale,
        Err(error)
            if error.reason_code == PackageArtifactErrorReason::UnsupportedSchema
                && error.path == "schema" =>
        {
            PackageBuildCheckCacheLookup::SchemaMiss
        }
        Err(_) => PackageBuildCheckCacheLookup::Stale,
    }
}

fn write_package_build_check_cache_entry_observed(
    cache: &PackageBuildCache,
    entry: &PackageBuildCheckResultEntry,
    bytes_loaded: &mut usize,
    bytes_written: &mut usize,
) -> bool {
    let key = match PackageCacheKeyDigest::from_cache_key(&entry.cache_key) {
        Ok(key) => key,
        Err(_) => return false,
    };
    let json = package_build_check_result_entry_json(entry);
    if json.len() > TARGETED_AUTHORING_CACHE_LIMITS_V1.result_entry_bytes {
        return false;
    }

    let (temporary, mut file) = match create_result_temporary(cache, &key) {
        Some(temporary) => temporary,
        None => return false,
    };
    let write_succeeded =
        std::io::Write::write_all(&mut file, json.as_bytes()).is_ok() && file.sync_all().is_ok();
    drop(file);
    if !write_succeeded {
        let _ =
            cache.remove_temporary_entry(PackageCacheStoreVersion::BUILD_CHECK_RESULT, &temporary);
        return false;
    }
    *bytes_written = bytes_written.saturating_add(json.len());
    match cache.publish_temporary_entry_no_replace(
        PackageCacheStoreVersion::BUILD_CHECK_RESULT,
        &temporary,
        &key,
    ) {
        Ok(()) => {}
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
            // Content-addressed entries are immutable. The readback below
            // decides whether the collision is the same entry or a conflict.
        }
        Err(_) => return false,
    }

    let mut ignored_lookup_ns = 0;
    matches!(
        read_package_build_check_cache_lookup_observed(
            cache,
            &entry.cache_key,
            bytes_loaded,
            &mut ignored_lookup_ns,
            false,
        ),
        PackageBuildCheckCacheLookup::Hit(actual)
            if package_build_check_cache_entries_equal(&actual, entry)
    )
}

fn create_result_temporary(
    cache: &PackageBuildCache,
    key: &PackageCacheKeyDigest,
) -> Option<(PackageCacheTemporaryName, File)> {
    for _ in 0..16 {
        let nonce = NEXT_RESULT_TEMPORARY.fetch_add(1, CacheOrdering::SeqCst);
        let unique = format!("{}-{nonce}", std::process::id());
        let temporary = PackageCacheTemporaryName::new(key, &unique).ok()?;
        match cache.create_temporary_entry(PackageCacheStoreVersion::BUILD_CHECK_RESULT, &temporary)
        {
            Ok(Some(file)) => return Some((temporary, file)),
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
            Ok(None) | Err(_) => return None,
        }
    }
    None
}

fn package_build_check_cache_entries_equal(
    actual: &PackageBuildCheckResultEntry,
    expected: &PackageBuildCheckResultEntry,
) -> bool {
    package_build_check_result_entry_json(actual) == package_build_check_result_entry_json(expected)
}

fn package_build_check_cache_result_entry(
    keyed: &PackageBuildCheckKeyedEntry,
    status: PackageBuildCheckCachedStatus,
    diagnostic_reason: Option<&str>,
) -> PackageBuildCheckResultEntry {
    PackageBuildCheckResultEntry {
        schema: PACKAGE_BUILD_CHECK_RESULT_SCHEMA.to_owned(),
        cache_key: keyed.cache_key.clone(),
        trusted: false,
        build_evidence: false,
        key_input: keyed.key_input.clone(),
        status,
        diagnostic_reason: diagnostic_reason.map(ToOwned::to_owned),
        trust_boundary: format!(
            "cache entry for {} is not proof evidence or build evidence; live build comparison dominates",
            keyed.module.as_dotted()
        ),
    }
}

impl PackageBuildCheckCacheSummary {
    fn new(mode: PackageBuildCheckCacheMode) -> Self {
        Self {
            mode,
            hits: 0,
            misses: 0,
            stale: 0,
            schema_misses: 0,
            written: 0,
            live_builds: 0,
            trusted: false,
            build_evidence: false,
            bytes_loaded: 0,
            bytes_written: 0,
        }
    }

    fn diagnostic_value(&self) -> String {
        format!(
            "mode={};hits={};misses={};stale={};schema_misses={};written={};live_builds={};trusted={};build_evidence={}",
            self.mode.as_str(),
            self.hits,
            self.misses,
            self.stale,
            self.schema_misses,
            self.written,
            self.live_builds,
            self.trusted,
            self.build_evidence
        )
    }
}

fn package_build_check_cache_summary_diagnostic(
    summary: &PackageBuildCheckCacheSummary,
) -> CommandDiagnostic {
    CommandDiagnostic::info(
        DiagnosticKind::GeneratedArtifact,
        "build_check_cache_summary",
    )
    .with_field("build_check_cache")
    .with_actual_value(summary.diagnostic_value())
}

fn package_build_check_cache_unavailable_diagnostic(
    reason: PackageBuildCheckCacheUnavailableReason,
) -> CommandDiagnostic {
    CommandDiagnostic::info(
        DiagnosticKind::GeneratedArtifact,
        "build_check_cache_unavailable",
    )
    .with_field("build_check_cache")
    .with_actual_value(format!(
        "mode=read-through;stores={};reason={}",
        PackageCacheStoreVersion::BUILD_CHECK_RESULT.as_str(),
        reason.as_str()
    ))
}

fn targeted_authoring_support_cache_unavailable_diagnostic(
    reason: PackageBuildCheckCacheUnavailableReason,
) -> CommandDiagnostic {
    CommandDiagnostic::info(
        DiagnosticKind::GeneratedArtifact,
        "build_check_cache_unavailable",
    )
    .with_field("build_check_cache")
    .with_actual_value(format!(
        "mode=local-hit;stores={};reason={}",
        PackageCacheStoreVersion::TARGETED_AUTHORING_SUPPORT.as_str(),
        reason.as_str()
    ))
}

fn read_bytes_through_limit_observed(
    mut reader: impl Read,
    limit: usize,
) -> (io::Result<Vec<u8>>, usize) {
    let take_limit = u64::try_from(limit).unwrap_or(u64::MAX).saturating_add(1);
    let mut bytes = Vec::new();
    let result = reader.by_ref().take(take_limit).read_to_end(&mut bytes);
    let observed = bytes.len();
    (result.map(|_| bytes), observed)
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct PackageBuildCacheTestCounters {
    pub(crate) root_resolutions: usize,
    pub(crate) cache_io_operations: usize,
}

#[derive(Debug)]
struct InspectedPath {
    absolute: PathBuf,
    existing_identities: Vec<Identity>,
    existing_components: usize,
    total_components: usize,
}

#[derive(Debug)]
struct GitCheckout {
    root: PathBuf,
    protected_metadata: Vec<InspectedPath>,
}

#[derive(Debug)]
enum CacheAnchorError {
    Unavailable,
}

fn resolve_and_open(
    loaded: &LoadedPackageRoot,
    override_base: Option<&Path>,
    namespace: &PackageCacheNamespaceDigest,
    requested_stores: &[PackageCacheStoreVersion],
) -> Result<AvailableCache, CacheAnchorError> {
    if !cfg!(unix) || requested_stores.is_empty() {
        return Err(CacheAnchorError::Unavailable);
    }

    let package_root = inspect_path(&loaded.root, true, true)?;
    let artifacts = inspect_manifest_paths(loaded, &package_root.absolute)?;
    let checkout = find_nearest_git_checkout(&package_root.absolute)?;

    let candidate_path = if let Some(override_base) = override_base {
        absolute_lexical_path(override_base)?
    } else if let Some(checkout) = &checkout {
        let repository_candidate = checkout
            .root
            .join(package_build_check_cache_default_base_relative_path());
        if paths_overlap(&repository_candidate, &package_root.absolute) {
            sibling_cache_base(&package_root.absolute)?
        } else {
            repository_candidate
        }
    } else {
        sibling_cache_base(&package_root.absolute)?
    };
    let candidate = inspect_path(&candidate_path, false, true)?;

    let mut protected = Vec::with_capacity(1 + artifacts.len() + 2);
    protected.push(&package_root);
    protected.extend(artifacts.iter());
    if let Some(checkout) = &checkout {
        protected.extend(checkout.protected_metadata.iter());
    }
    if protected
        .iter()
        .any(|path| inspected_paths_overlap(&candidate, path))
    {
        return Err(CacheAnchorError::Unavailable);
    }

    let base_directory = open_inspected_directory(&candidate)?;
    let packages = base_directory
        .open_or_create_directory(OsStr::new("packages"), true)
        .map_err(|_| CacheAnchorError::Unavailable)?;
    let namespace_directory = packages
        .open_or_create_directory(OsStr::new(namespace.as_str()), true)
        .map_err(|_| CacheAnchorError::Unavailable)?;

    let mut stores = Vec::with_capacity(requested_stores.len());
    for &version in requested_stores {
        if stores
            .iter()
            .any(|store: &StoreCapability| store.version == version)
        {
            continue;
        }
        let directory = namespace_directory
            .open_or_create_directory(OsStr::new(version.as_str()), true)
            .map_err(|_| CacheAnchorError::Unavailable)?;
        probe_store_writable(&directory)?;
        stores.push(StoreCapability { version, directory });
    }

    Ok(AvailableCache {
        namespace: namespace.clone(),
        #[cfg(test)]
        cache_base: candidate.absolute,
        stores,
    })
}

fn probe_store_writable(directory: &Directory) -> Result<(), CacheAnchorError> {
    for _ in 0..16 {
        let nonce = NEXT_CACHE_PROBE.fetch_add(1, CacheOrdering::SeqCst);
        let name = format!("cache-anchor-probe-{}-{nonce}", std::process::id());
        match directory.probe_writable(OsStr::new(&name)) {
            Ok(()) => return Ok(()),
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
            Err(_) => return Err(CacheAnchorError::Unavailable),
        }
    }
    Err(CacheAnchorError::Unavailable)
}

fn inspect_manifest_paths(
    loaded: &LoadedPackageRoot,
    package_root: &Path,
) -> Result<Vec<InspectedPath>, CacheAnchorError> {
    let manifest = loaded.validated.manifest();
    let mut paths = vec![package_root.join(loaded.manifest_path.as_str())];
    for module in &manifest.modules {
        paths.push(package_root.join(module.source.as_str()));
        paths.push(package_root.join(module.certificate.as_str()));
        if let Some(path) = &module.meta {
            paths.push(package_root.join(path.as_str()));
        }
        if let Some(path) = &module.replay {
            paths.push(package_root.join(path.as_str()));
        }
    }
    if let Some(imports) = &manifest.imports {
        paths.extend(
            imports
                .iter()
                .map(|import| package_root.join(import.certificate.as_str())),
        );
    }
    paths
        .iter()
        .map(|path| inspect_path(path, false, false))
        .collect()
}

fn find_nearest_git_checkout(package_root: &Path) -> Result<Option<GitCheckout>, CacheAnchorError> {
    for ancestor in package_root.ancestors() {
        let marker = ancestor.join(".git");
        let metadata = match fs::symlink_metadata(&marker) {
            Ok(metadata) => metadata,
            Err(error) if error.kind() == io::ErrorKind::NotFound => continue,
            Err(_) => return Err(CacheAnchorError::Unavailable),
        };
        if metadata.file_type().is_symlink() {
            return Err(CacheAnchorError::Unavailable);
        }
        if metadata.is_dir() {
            return Ok(Some(GitCheckout {
                root: ancestor.to_path_buf(),
                protected_metadata: vec![inspect_path(&marker, true, true)?],
            }));
        }
        if !metadata.is_file() {
            return Err(CacheAnchorError::Unavailable);
        }

        let marker_inspection = inspect_path(&marker, true, false)?;
        let source = read_small_inspected_file(&marker_inspection, 4096)?;
        let Some(git_dir) = source.trim().strip_prefix("gitdir:") else {
            return Err(CacheAnchorError::Unavailable);
        };
        let git_dir = git_dir.trim();
        if git_dir.is_empty() {
            return Err(CacheAnchorError::Unavailable);
        }
        let git_dir = Path::new(git_dir);
        let git_dir = if git_dir.is_absolute() {
            git_dir.to_path_buf()
        } else {
            ancestor.join(git_dir)
        };
        let git_dir = inspect_path(&git_dir, true, true)?;
        return Ok(Some(GitCheckout {
            root: ancestor.to_path_buf(),
            protected_metadata: vec![marker_inspection, git_dir],
        }));
    }
    Ok(None)
}

fn sibling_cache_base(package_root: &Path) -> Result<PathBuf, CacheAnchorError> {
    package_root
        .parent()
        .map(|parent| parent.join(package_build_check_cache_default_base_relative_path()))
        .ok_or(CacheAnchorError::Unavailable)
}

fn inspect_path(
    path: &Path,
    require_exists: bool,
    require_directory: bool,
) -> Result<InspectedPath, CacheAnchorError> {
    let absolute = absolute_lexical_path(path)?;
    let mut existing_identities = Vec::new();
    let root_metadata =
        fs::symlink_metadata(Path::new("/")).map_err(|_| CacheAnchorError::Unavailable)?;
    existing_identities.push(metadata_identity(&root_metadata)?);

    let components = normal_components(&absolute)?;
    let mut current = PathBuf::from("/");
    let mut existing_components = 0usize;
    let mut missing = false;
    for (index, component) in components.iter().enumerate() {
        current.push(component);
        if missing {
            continue;
        }
        let metadata = match fs::symlink_metadata(&current) {
            Ok(metadata) => metadata,
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                missing = true;
                continue;
            }
            Err(_) => return Err(CacheAnchorError::Unavailable),
        };
        if metadata.file_type().is_symlink() {
            return Err(CacheAnchorError::Unavailable);
        }
        let is_final = index + 1 == components.len();
        if !metadata.is_dir() && (!is_final || require_directory) {
            return Err(CacheAnchorError::Unavailable);
        }
        let canonical = fs::canonicalize(&current).map_err(|_| CacheAnchorError::Unavailable)?;
        if canonical != current {
            return Err(CacheAnchorError::Unavailable);
        }
        existing_identities.push(metadata_identity(&metadata)?);
        existing_components += 1;
    }
    if require_exists && missing {
        return Err(CacheAnchorError::Unavailable);
    }
    let total_components = components.len();
    Ok(InspectedPath {
        absolute,
        existing_identities,
        existing_components,
        total_components,
    })
}

fn open_inspected_directory(path: &InspectedPath) -> Result<Directory, CacheAnchorError> {
    let mut directory =
        Directory::open_filesystem_root().map_err(|_| CacheAnchorError::Unavailable)?;
    if directory
        .identity()
        .map_err(|_| CacheAnchorError::Unavailable)?
        != path.existing_identities[0]
    {
        return Err(CacheAnchorError::Unavailable);
    }
    for (index, component) in normal_components(&path.absolute)?.iter().enumerate() {
        let was_existing = index < path.existing_components;
        directory = directory
            .open_or_create_directory(component, !was_existing)
            .map_err(|_| CacheAnchorError::Unavailable)?;
        if was_existing
            && directory
                .identity()
                .map_err(|_| CacheAnchorError::Unavailable)?
                != path.existing_identities[index + 1]
        {
            return Err(CacheAnchorError::Unavailable);
        }
    }
    Ok(directory)
}

fn read_small_inspected_file(
    path: &InspectedPath,
    byte_limit: usize,
) -> Result<String, CacheAnchorError> {
    if path.existing_components != path.total_components || path.total_components == 0 {
        return Err(CacheAnchorError::Unavailable);
    }
    let components = normal_components(&path.absolute)?;
    let (filename, parent_components) = components
        .split_last()
        .ok_or(CacheAnchorError::Unavailable)?;
    let mut directory =
        Directory::open_filesystem_root().map_err(|_| CacheAnchorError::Unavailable)?;
    if directory
        .identity()
        .map_err(|_| CacheAnchorError::Unavailable)?
        != path.existing_identities[0]
    {
        return Err(CacheAnchorError::Unavailable);
    }
    for (index, component) in parent_components.iter().enumerate() {
        directory = directory
            .open_or_create_directory(component, false)
            .map_err(|_| CacheAnchorError::Unavailable)?;
        if directory
            .identity()
            .map_err(|_| CacheAnchorError::Unavailable)?
            != path.existing_identities[index + 1]
        {
            return Err(CacheAnchorError::Unavailable);
        }
    }
    let mut file = directory
        .open_regular_file(filename)
        .map_err(|_| CacheAnchorError::Unavailable)?
        .ok_or(CacheAnchorError::Unavailable)?;
    if metadata_identity(&file.metadata().map_err(|_| CacheAnchorError::Unavailable)?)?
        != path.existing_identities[path.total_components]
    {
        return Err(CacheAnchorError::Unavailable);
    }

    let take_limit = u64::try_from(byte_limit)
        .map_err(|_| CacheAnchorError::Unavailable)?
        .saturating_add(1);
    let mut bytes = Vec::with_capacity(byte_limit.min(4096));
    file.by_ref()
        .take(take_limit)
        .read_to_end(&mut bytes)
        .map_err(|_| CacheAnchorError::Unavailable)?;
    if bytes.len() > byte_limit {
        return Err(CacheAnchorError::Unavailable);
    }
    String::from_utf8(bytes).map_err(|_| CacheAnchorError::Unavailable)
}

fn absolute_lexical_path(path: &Path) -> Result<PathBuf, CacheAnchorError> {
    if path.is_absolute() {
        return absolute_lexical_path_from(path, Path::new("/"));
    }
    let current_dir = std::env::current_dir().map_err(|_| CacheAnchorError::Unavailable)?;
    absolute_lexical_path_from(path, &current_dir)
}

fn absolute_lexical_path_from(
    path: &Path,
    current_dir: &Path,
) -> Result<PathBuf, CacheAnchorError> {
    let path = if path.is_absolute() {
        path.to_path_buf()
    } else {
        current_dir.join(path)
    };
    let mut normalized = PathBuf::from("/");
    for component in path.components() {
        match component {
            Component::Prefix(_) => return Err(CacheAnchorError::Unavailable),
            Component::RootDir | Component::CurDir => {}
            Component::ParentDir => {
                if !normalized.pop() {
                    return Err(CacheAnchorError::Unavailable);
                }
            }
            Component::Normal(component) => normalized.push(component),
        }
    }
    Ok(normalized)
}

fn normal_components(path: &Path) -> Result<Vec<&OsStr>, CacheAnchorError> {
    if !path.is_absolute() {
        return Err(CacheAnchorError::Unavailable);
    }
    path.components()
        .filter_map(|component| match component {
            Component::RootDir => None,
            Component::Normal(component) => Some(Ok(component)),
            Component::Prefix(_) | Component::CurDir | Component::ParentDir => {
                Some(Err(CacheAnchorError::Unavailable))
            }
        })
        .collect()
}

fn paths_overlap(left: &Path, right: &Path) -> bool {
    left == right || left.starts_with(right) || right.starts_with(left)
}

fn inspected_paths_overlap(candidate: &InspectedPath, protected: &InspectedPath) -> bool {
    if paths_overlap(&candidate.absolute, &protected.absolute) {
        return true;
    }

    let protected_existing_target = protected.existing_identities.last();
    if protected_existing_target.is_some_and(|identity| {
        candidate
            .existing_identities
            .iter()
            .any(|candidate_identity| candidate_identity == identity)
    }) {
        return true;
    }

    candidate.existing_components == candidate.total_components
        && candidate
            .existing_identities
            .last()
            .is_some_and(|identity| {
                protected
                    .existing_identities
                    .iter()
                    .any(|protected_identity| protected_identity == identity)
            })
}

#[cfg(unix)]
fn metadata_identity(metadata: &fs::Metadata) -> Result<Identity, CacheAnchorError> {
    use std::os::unix::fs::MetadataExt;
    Ok(Identity {
        device: metadata.dev(),
        inode: metadata.ino(),
    })
}

#[cfg(not(unix))]
fn metadata_identity(_metadata: &fs::Metadata) -> Result<Identity, CacheAnchorError> {
    Err(CacheAnchorError::Unavailable)
}

#[cfg(test)]
mod tests {
    use std::{
        cell::Cell,
        io::{Cursor, Read},
        sync::{
            atomic::{AtomicU64, Ordering as AtomicOrdering},
            mpsc, Arc, Barrier,
        },
    };

    use npa_cert::Name;
    use npa_frontend::HumanKernelFuelReportMode;
    use npa_package::{
        package_build_check_cache_namespace_digest, package_file_hash,
        refresh_targeted_authoring_support_context_entry, targeted_authoring_module_identity,
        targeted_authoring_support_context_entry_json, PackageCacheKeyDigest,
        PackageCacheNamespaceDigest, PackageCacheStoreLayout, PackageCacheStoreVersion,
        PackageHash, PackageId, PackageModuleIdentity, PackageVersion,
        TargetedAuthoringAcceptedCertificateIdentity, TargetedAuthoringDefinitionReducibility,
        TargetedAuthoringHumanDeclaration, TargetedAuthoringHumanDeclarationKind,
        TargetedAuthoringHumanImportedSourceInterface, TargetedAuthoringHumanName,
        TargetedAuthoringHumanSourceInterface, TargetedAuthoringInterfaceProfile,
        TargetedAuthoringSourceIdentity, TargetedAuthoringSpan, TargetedAuthoringSpanOrigin,
        TargetedAuthoringSupportContextEntry, TargetedAuthoringSupportKeyInput,
        TargetedAuthoringToolchainIdentity, PACKAGE_TARGETED_AUTHORING_HUMAN_INTERFACE_SCHEMA,
        PACKAGE_TARGETED_AUTHORING_LIVE_CLOSURE_CLAIM, PACKAGE_TARGETED_AUTHORING_POLICY,
        PACKAGE_TARGETED_AUTHORING_SUPPORT_CONTEXT_SCHEMA,
        PACKAGE_TARGETED_AUTHORING_SUPPORT_TRUST_BOUNDARY,
    };

    use super::*;
    use crate::package::load_package_root;

    static NEXT_TEST_DIRECTORY: AtomicU64 = AtomicU64::new(0);
    const ZERO_HASH: &str =
        "sha256:0000000000000000000000000000000000000000000000000000000000000000";

    struct TestDirectory {
        path: PathBuf,
    }

    impl TestDirectory {
        fn new(label: &str) -> Self {
            let index = NEXT_TEST_DIRECTORY.fetch_add(1, AtomicOrdering::SeqCst);
            let raw = std::env::temp_dir().join(format!(
                "npa-package-build-cache-{label}-{}-{index}",
                std::process::id()
            ));
            fs::create_dir_all(&raw).unwrap();
            let path = fs::canonicalize(raw).unwrap();
            Self { path }
        }

        fn join(&self, path: impl AsRef<Path>) -> PathBuf {
            self.path.join(path)
        }
    }

    impl Drop for TestDirectory {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.path);
        }
    }

    fn write_package(root: &Path, with_module: bool) -> LoadedPackageRoot {
        fs::create_dir_all(root).unwrap();
        let modules = if with_module {
            format!(
                r#"
[[modules]]
module = "Fixture.A"
source = "Fixture/A/source.npa"
certificate = "Fixture/A/certificate.npcert"
imports = []
expected_source_hash = "{ZERO_HASH}"
expected_certificate_file_hash = "{ZERO_HASH}"
expected_export_hash = "{ZERO_HASH}"
expected_axiom_report_hash = "{ZERO_HASH}"
expected_certificate_hash = "{ZERO_HASH}"
meta = "Fixture/A/meta.json"
replay = "Fixture/A/replay.json"
"#
            )
        } else {
            "modules = []\n".to_owned()
        };
        let manifest = format!(
            r#"schema = "npa.package.v0.1"
package = "fixture-package"
version = "0.1.0"
core_spec = "npa.core.v0.1"
kernel_profile = "npa.kernel.v0.1"
certificate_format = "npa.certificate.canonical.v0.1"
checker_profile = "npa.checker.reference.v0.1"
{modules}
[policy]
allow_custom_axioms = false
allowed_axioms = []
"#
        );
        fs::write(root.join("npa-package.toml"), manifest).unwrap();
        load_package_root(root, "test").unwrap()
    }

    fn open_result_cache(
        enabled: bool,
        loaded: &LoadedPackageRoot,
        override_base: Option<&Path>,
    ) -> PackageBuildCache {
        let namespace = package_build_check_cache_namespace_digest(&loaded.validated);
        open_package_build_cache(
            enabled,
            loaded,
            override_base,
            &namespace,
            &[PackageCacheStoreVersion::BUILD_CHECK_RESULT],
        )
    }

    fn open_support_cache(
        loaded: &LoadedPackageRoot,
        override_base: &Path,
    ) -> (PackageBuildCache, PackageCacheNamespaceDigest) {
        let namespace = package_build_check_cache_namespace_digest(&loaded.validated);
        let cache = open_package_build_cache(
            true,
            loaded,
            Some(override_base),
            &namespace,
            &[PackageCacheStoreVersion::TARGETED_AUTHORING_SUPPORT],
        );
        (cache, namespace)
    }

    fn support_store_path(
        override_base: &Path,
        namespace: &PackageCacheNamespaceDigest,
    ) -> PathBuf {
        override_base
            .join(PackageCacheStoreLayout::targeted_authoring_support(namespace).relative_path())
    }

    fn fixture_hash(value: u8) -> PackageHash {
        PackageHash::new([value; 32])
    }

    fn support_context_entry(
        namespace: &PackageCacheNamespaceDigest,
        module_spelling: &str,
        include_declaration: bool,
    ) -> TargetedAuthoringSupportContextEntry {
        let package = PackageId::new("fixture-package");
        let version = PackageVersion::new("0.1.0");
        let module = Name::from_dotted(module_spelling);
        let source_hash = package_file_hash(b"a");
        let key_input = TargetedAuthoringSupportKeyInput {
            toolchain: TargetedAuthoringToolchainIdentity {
                executable_hash: fixture_hash(1),
                cli_authoring_abi: "npa.cli.targeted_authoring_abi.v1".to_owned(),
                frontend_authoring_abi: "npa.frontend.human_authoring_interface_abi.v2".to_owned(),
                producer_authoring_abi: "npa.cert.local_authoring_producer_abi.v1".to_owned(),
                kernel_authoring_abi: "npa.kernel.local_authoring_context_abi.v1".to_owned(),
            },
            package: package.clone(),
            version: version.clone(),
            core_spec: "npa.core.v0.1".to_owned(),
            kernel_profile: "npa.kernel.v0.1".to_owned(),
            certificate_format: "npa.certificate.canonical.v0.1".to_owned(),
            checker_profile: "npa.checker.reference.v0.1".to_owned(),
            producer_profile: "npa.producer.fixture.v0.1".to_owned(),
            semantic_compiler_options: vec!["frontend=human".to_owned()],
            axiom_policy_hash: fixture_hash(2),
            module: module.clone(),
            module_identity: targeted_authoring_module_identity(&PackageModuleIdentity {
                package: package.clone(),
                version: version.clone(),
                module: module.clone(),
            }),
            current_source_hash: source_hash,
            expected_source_hash: fixture_hash(3),
            current_certificate_file_hash: fixture_hash(4),
            expected_certificate_file_hash: fixture_hash(5),
            expected_export_hash: fixture_hash(6),
            expected_axiom_report_hash: fixture_hash(7),
            expected_certificate_hash: fixture_hash(8),
            actual_export_hash: fixture_hash(9),
            actual_axiom_report_hash: fixture_hash(10),
            actual_certificate_hash: fixture_hash(11),
            certificate_imports: Vec::new(),
            dependency_closure_commitment: fixture_hash(12),
            manifest_human_imports: Vec::new(),
            source_interface_schema: PACKAGE_TARGETED_AUTHORING_HUMAN_INTERFACE_SCHEMA.to_owned(),
            source_interface_reconstruction_version: "npa.reconstruct.v0.1".to_owned(),
        };
        let span = TargetedAuthoringSpan {
            origin: TargetedAuthoringSpanOrigin::CurrentModule,
            start: 0,
            end: 1,
        };
        let declarations = include_declaration
            .then(|| TargetedAuthoringHumanDeclaration {
                kind: TargetedAuthoringHumanDeclarationKind::Def,
                definition_reducibility: Some(TargetedAuthoringDefinitionReducibility::Reducible),
                name: TargetedAuthoringHumanName {
                    parts: format!("{module_spelling}.value")
                        .split('.')
                        .map(ToOwned::to_owned)
                        .collect(),
                    span,
                },
                universe_params: Vec::new(),
                binders: Vec::new(),
                decl_interface_hash: Some(fixture_hash(13)),
                span,
            })
            .into_iter()
            .collect();
        let source_interface = TargetedAuthoringHumanSourceInterface {
            module: module.clone(),
            declarations,
            notations: Vec::new(),
            generated_declarations: Vec::new(),
            typeclass_classes: Vec::new(),
            typeclass_instances: Vec::new(),
        };
        let entry = TargetedAuthoringSupportContextEntry {
            schema: PACKAGE_TARGETED_AUTHORING_SUPPORT_CONTEXT_SCHEMA.to_owned(),
            cache_key: String::new(),
            namespace: namespace.clone(),
            key_input: key_input.clone(),
            closure_commitment: key_input.dependency_closure_commitment,
            producer_profile: key_input.producer_profile.clone(),
            interface_profile: TargetedAuthoringInterfaceProfile::HumanSource,
            authoring_policy: PACKAGE_TARGETED_AUTHORING_POLICY.to_owned(),
            accepted_certificate: TargetedAuthoringAcceptedCertificateIdentity {
                module: module.clone(),
                certificate_file_hash: key_input.current_certificate_file_hash,
                export_hash: key_input.actual_export_hash,
                axiom_report_hash: key_input.actual_axiom_report_hash,
                certificate_hash: key_input.actual_certificate_hash,
            },
            source_interface: TargetedAuthoringHumanImportedSourceInterface {
                schema: PACKAGE_TARGETED_AUTHORING_HUMAN_INTERFACE_SCHEMA.to_owned(),
                module: module.clone(),
                export_hash: key_input.actual_export_hash,
                certificate_hash: key_input.actual_certificate_hash,
                source: TargetedAuthoringSourceIdentity {
                    package,
                    version,
                    module,
                    source_hash,
                },
                producer_profile: key_input.producer_profile.clone(),
                direct_imports: Vec::new(),
                source_interface,
            },
            integrity_digest: fixture_hash(0),
            trusted: false,
            build_evidence: false,
            proof_evidence: false,
            live_closure_eligibility: PACKAGE_TARGETED_AUTHORING_LIVE_CLOSURE_CLAIM.to_owned(),
            trust_boundary: PACKAGE_TARGETED_AUTHORING_SUPPORT_TRUST_BOUNDARY.to_owned(),
        };
        refresh_targeted_authoring_support_context_entry(&entry).unwrap()
    }

    fn support_entry_path(store: &Path, entry: &TargetedAuthoringSupportContextEntry) -> PathBuf {
        let key = PackageCacheKeyDigest::from_cache_key(&entry.cache_key).unwrap();
        store.join(format!("{}.json", key.as_str()))
    }

    fn entry_key() -> PackageCacheKeyDigest {
        PackageCacheKeyDigest::from_cache_key(&format!("sha256:{}", "1".repeat(64))).unwrap()
    }

    #[test]
    fn package_build_check_cache_tool_identity_commits_to_executable_bytes_and_each_abi() {
        let baseline = package_build_check_tool_build_hash_from_reader(
            Cursor::new(b"executable-a"),
            TARGETED_AUTHORING_ABI,
            HUMAN_AUTHORING_INTERFACE_ABI,
            LOCAL_AUTHORING_PRODUCER_ABI,
            LOCAL_AUTHORING_CONTEXT_ABI,
        )
        .unwrap();
        let replaced = package_build_check_tool_build_hash_from_reader(
            Cursor::new(b"executable-b"),
            TARGETED_AUTHORING_ABI,
            HUMAN_AUTHORING_INTERFACE_ABI,
            LOCAL_AUTHORING_PRODUCER_ABI,
            LOCAL_AUTHORING_CONTEXT_ABI,
        )
        .unwrap();
        assert_ne!(baseline, replaced);

        for identities in [
            (
                "cli.changed",
                HUMAN_AUTHORING_INTERFACE_ABI,
                LOCAL_AUTHORING_PRODUCER_ABI,
                LOCAL_AUTHORING_CONTEXT_ABI,
            ),
            (
                TARGETED_AUTHORING_ABI,
                "frontend.changed",
                LOCAL_AUTHORING_PRODUCER_ABI,
                LOCAL_AUTHORING_CONTEXT_ABI,
            ),
            (
                TARGETED_AUTHORING_ABI,
                HUMAN_AUTHORING_INTERFACE_ABI,
                "producer.changed",
                LOCAL_AUTHORING_CONTEXT_ABI,
            ),
            (
                TARGETED_AUTHORING_ABI,
                HUMAN_AUTHORING_INTERFACE_ABI,
                LOCAL_AUTHORING_PRODUCER_ABI,
                "kernel.changed",
            ),
        ] {
            let changed = package_build_check_tool_build_hash_from_reader(
                Cursor::new(b"executable-a"),
                identities.0,
                identities.1,
                identities.2,
                identities.3,
            )
            .unwrap();
            assert_ne!(baseline, changed);
        }
    }

    #[test]
    fn package_build_check_cache_compiler_identity_excludes_fuel_observation() {
        let tree = TestDirectory::new("compiler-identity");
        let loaded = write_package(&tree.join("package"), true);
        let module = &loaded.validated.manifest().modules[0];
        let baseline = HumanCompileOptions::default();
        let mut observed = baseline.clone();
        observed.kernel_fuel_report = HumanKernelFuelReportMode::Detailed;
        assert_eq!(
            package_build_check_compiler_options_with_human(module, &baseline),
            package_build_check_compiler_options_with_human(module, &observed)
        );

        let mut semantic_change = baseline.clone();
        semantic_change.max_notation_candidates += 1;
        assert_ne!(
            package_build_check_compiler_options_with_human(module, &baseline),
            package_build_check_compiler_options_with_human(module, &semantic_change)
        );
        assert!(
            package_build_check_compiler_options_with_human(module, &baseline)
                .iter()
                .all(|option| !option.contains("fuel"))
        );

        let certificates = [PackageBuildCheckCertificateIdentity {
            module_index: 0,
            source_hash: package_file_hash(b"source"),
            output_certificate_format: "npa.certificate.canonical.v0.1".to_owned(),
            output_core_spec: "npa.core.v0.1".to_owned(),
        }];
        let baseline_key = package_build_check_cache_key_inputs(
            &loaded,
            &certificates,
            package_file_hash(b"tool"),
        )
        .pop()
        .unwrap()
        .key_input;
        let baseline_digest = package_build_check_cache_key(&baseline_key);
        let mut semantic_key = baseline_key.clone();
        semantic_key.compiler_options =
            package_build_check_compiler_options_with_human(module, &semantic_change);
        assert_ne!(
            baseline_digest,
            package_build_check_cache_key(&semantic_key)
        );
        let mut schema_key = baseline_key;
        schema_key.schema = "npa.package.build_check_cache.v0.3".to_owned();
        assert_ne!(baseline_digest, package_build_check_cache_key(&schema_key));
    }

    #[test]
    fn package_build_check_cache_tool_identity_failure_targeted_authoring_diagnostics_disable_entry_io(
    ) {
        let tree = TestDirectory::new("tool-identity-failure");
        let loaded = write_package(&tree.join("package"), false);
        let cache = open_result_cache(true, &loaded, Some(&tree.join("cache")));
        let session = complete_package_build_check_cache_session_observed(cache, true, || {
            (
                Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "injected tool identity failure",
                )),
                17,
            )
        });

        assert_eq!(
            session.cache.availability(),
            PackageBuildCacheAvailability::Unavailable
        );
        assert_eq!(
            session
                .unavailable_diagnostic()
                .unwrap()
                .actual_value
                .as_deref(),
            Some("mode=read-through;stores=build-check-v0.2;reason=tool_identity")
        );
        assert!(session
            .cache
            .open_entry(PackageCacheStoreVersion::BUILD_CHECK_RESULT, &entry_key())
            .unwrap()
            .is_none());
        assert_eq!(session.cache.test_counters().cache_io_operations, 0);
        assert!(session.tool_identity_observation().attempted);
        assert_eq!(session.tool_identity_observation().bytes, 17);
    }

    #[test]
    fn package_build_check_cache_unavailable_anchor_skips_tool_identity() {
        let tree = TestDirectory::new("unavailable-skips-tool");
        let loaded = write_package(&tree.join("package"), false);
        let cache = open_result_cache(true, &loaded, Some(&loaded.root.join("unsafe-cache")));
        let called = Cell::new(false);

        let session = complete_package_build_check_cache_session_observed(cache, true, || {
            called.set(true);
            (Ok(package_file_hash(b"should not be acquired")), 31)
        });

        assert!(!called.get());
        assert_eq!(
            session.cache.availability(),
            PackageBuildCacheAvailability::Unavailable
        );
        assert_eq!(
            session.tool_identity_observation(),
            PackageBuildCacheToolIdentityObservation::default()
        );
        assert_eq!(session.cache.test_counters().cache_io_operations, 0);
    }

    #[test]
    fn targeted_authoring_diagnostics_coalesce_unavailable_store_set_without_tool_observation() {
        let tree = TestDirectory::new("coalesced-unavailable");
        let loaded = write_package(&tree.join("package"), false);
        let (mut result, support) = prepare_package_build_check_and_support_cache_sessions_observed(
            &loaded,
            Some(&loaded.root.join("unsafe-cache")),
            true,
        );

        assert_eq!(
            result.tool_identity_observation(),
            PackageBuildCacheToolIdentityObservation::default()
        );
        assert_eq!(
            coalesced_build_check_cache_unavailable_diagnostic(
                "read-through",
                &mut result,
                Some(&support),
            )
            .unwrap()
            .actual_value
            .as_deref(),
            Some(
                "mode=read-through;stores=build-check-v0.2|targeted-authoring-support-v0.1;reason=anchor_or_capability"
            )
        );
        assert!(result.unavailable_diagnostic().is_none());
    }

    #[test]
    fn targeted_authoring_lookup_unavailable_anchor_skips_tool_identity_and_entry_io() {
        let tree = TestDirectory::new("support-unavailable-skips-tool");
        let loaded = write_package(&tree.join("package"), false);
        let namespace = package_build_check_cache_namespace_digest(&loaded.validated);
        let cache = open_package_build_cache(
            true,
            &loaded,
            Some(&loaded.root.join("unsafe-cache")),
            &namespace,
            &[PackageCacheStoreVersion::TARGETED_AUTHORING_SUPPORT],
        );
        let called = Cell::new(false);

        let mut session =
            complete_targeted_authoring_support_cache_session_observed(cache, true, || {
                called.set(true);
                (
                    Ok(TargetedAuthoringToolchainIdentity {
                        executable_hash: package_file_hash(b"should not be acquired"),
                        cli_authoring_abi: "cli".to_owned(),
                        frontend_authoring_abi: "frontend".to_owned(),
                        producer_authoring_abi: "producer".to_owned(),
                        kernel_authoring_abi: "kernel".to_owned(),
                    }),
                    43,
                )
            });

        assert!(!called.get());
        assert_eq!(
            session.tool_identity_observation(),
            PackageBuildCacheToolIdentityObservation::default()
        );
        assert_eq!(
            session.lookup(
                &format!("sha256:{}", "1".repeat(64)),
                &mut TargetedAuthoringSupportContextStoreBudget::new(),
            ),
            TargetedAuthoringSupportContextStoreLookup::Unavailable
        );
        assert_eq!(session.cache.test_counters().cache_io_operations, 0);
        assert_eq!(
            session
                .unavailable_diagnostic()
                .unwrap()
                .actual_value
                .as_deref(),
            Some(
                "mode=local-hit;stores=targeted-authoring-support-v0.1;reason=anchor_or_capability"
            )
        );
    }

    #[test]
    fn targeted_authoring_lookup_unavailable_tool_identity_is_sticky() {
        let tree = TestDirectory::new("support-tool-identity-failure");
        let loaded = write_package(&tree.join("package"), false);
        let (cache, _) = open_support_cache(&loaded, &tree.join("cache"));
        let mut session = complete_targeted_authoring_support_cache_session(cache, || {
            Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "injected tool identity failure",
            ))
        });

        assert_eq!(
            session.lookup(
                &format!("sha256:{}", "1".repeat(64)),
                &mut TargetedAuthoringSupportContextStoreBudget::new(),
            ),
            TargetedAuthoringSupportContextStoreLookup::Unavailable
        );
        assert_eq!(session.cache.test_counters().cache_io_operations, 0);
        assert_eq!(
            session
                .unavailable_diagnostic()
                .unwrap()
                .actual_value
                .as_deref(),
            Some("mode=local-hit;stores=targeted-authoring-support-v0.1;reason=tool_identity")
        );
    }

    #[test]
    fn package_build_cache_nested_checkout_uses_one_cwd_independent_repository_anchor() {
        let tree = TestDirectory::new("nested-checkout");
        let checkout = tree.join("checkout");
        fs::create_dir_all(checkout.join(".git")).unwrap();
        let loaded = write_package(&checkout.join("proofs"), false);
        let tools = checkout.join("tools");
        fs::create_dir_all(&tools).unwrap();
        let mut loaded_from_checkout = loaded.clone();
        loaded_from_checkout.root =
            absolute_lexical_path_from(Path::new("proofs"), &checkout).unwrap();
        let mut loaded_from_tools = loaded;
        loaded_from_tools.root =
            absolute_lexical_path_from(Path::new("../proofs"), &tools).unwrap();

        let first = open_result_cache(true, &loaded_from_checkout, None);
        let second = open_result_cache(true, &loaded_from_tools, None);
        let expected = checkout.join("target/npa-package-audit-cache");

        assert_eq!(
            first.availability(),
            PackageBuildCacheAvailability::Available
        );
        assert_eq!(first.test_cache_base(), Some(expected.as_path()));
        assert_eq!(second.test_cache_base(), first.test_cache_base());
        assert_eq!(first.test_counters().root_resolutions, 1);
    }

    #[test]
    fn package_build_cache_nearest_nested_checkout_wins_even_without_head() {
        let tree = TestDirectory::new("nearest-checkout");
        let outer = tree.join("outer");
        let inner = outer.join("nested");
        fs::create_dir_all(outer.join(".git")).unwrap();
        fs::create_dir_all(inner.join(".git")).unwrap();
        let loaded = write_package(&inner.join("proofs"), false);

        let cache = open_result_cache(true, &loaded, None);

        assert_eq!(
            cache.test_cache_base(),
            Some(inner.join("target/npa-package-audit-cache").as_path())
        );
    }

    #[test]
    fn package_build_cache_checkout_root_and_no_git_use_sibling_anchor() {
        let checkout_tree = TestDirectory::new("checkout-root");
        let checkout = checkout_tree.join("package");
        fs::create_dir_all(checkout.join(".git")).unwrap();
        let checkout_package = write_package(&checkout, false);
        let checkout_cache = open_result_cache(true, &checkout_package, None);
        assert_eq!(
            checkout_cache.test_cache_base(),
            Some(
                checkout_tree
                    .join("target/npa-package-audit-cache")
                    .as_path()
            )
        );
        assert!(!checkout_cache
            .test_cache_base()
            .unwrap()
            .starts_with(&checkout));

        let detached_tree = TestDirectory::new("no-git");
        let package = detached_tree.join("package");
        let detached_package = write_package(&package, false);
        let detached_cache = open_result_cache(true, &detached_package, None);
        assert_eq!(
            detached_cache.test_cache_base(),
            Some(
                detached_tree
                    .join("target/npa-package-audit-cache")
                    .as_path()
            )
        );
    }

    #[test]
    fn package_build_cache_override_replaces_complete_base_and_creates_missing_suffix() {
        let tree = TestDirectory::new("override");
        let loaded = write_package(&tree.join("package"), false);
        let override_base = tree.join("injected-cache");
        let namespace = package_build_check_cache_namespace_digest(&loaded.validated);

        let cache = open_package_build_cache(
            true,
            &loaded,
            Some(&override_base),
            &namespace,
            &[
                PackageCacheStoreVersion::BUILD_CHECK_RESULT,
                PackageCacheStoreVersion::TARGETED_AUTHORING_SUPPORT,
            ],
        );
        let result_layout = PackageCacheStoreLayout::build_check_result(&namespace);
        let support_layout = PackageCacheStoreLayout::targeted_authoring_support(&namespace);

        assert_eq!(cache.test_cache_base(), Some(override_base.as_path()));
        let result_store = override_base.join(result_layout.relative_path());
        let support_store = override_base.join(support_layout.relative_path());
        assert!(result_store.is_dir());
        assert!(support_store.is_dir());
        assert_eq!(fs::read_dir(result_store).unwrap().count(), 0);
        assert_eq!(fs::read_dir(support_store).unwrap().count(), 0);
        assert!(!override_base
            .join("target/npa-package-audit-cache")
            .exists());
    }

    #[test]
    fn package_build_cache_git_file_protects_external_git_directory() {
        let tree = TestDirectory::new("git-file");
        let checkout = tree.join("checkout");
        let git_dir = tree.join("metadata/worktrees/checkout");
        fs::create_dir_all(&git_dir).unwrap();
        fs::create_dir_all(&checkout).unwrap();
        fs::write(
            checkout.join(".git"),
            format!("gitdir: {}\n", git_dir.display()),
        )
        .unwrap();
        let loaded = write_package(&checkout.join("proofs"), false);

        let cache = open_result_cache(true, &loaded, None);

        assert_eq!(
            cache.availability(),
            PackageBuildCacheAvailability::Available
        );
        assert_eq!(
            cache.test_cache_base(),
            Some(checkout.join("target/npa-package-audit-cache").as_path())
        );
    }

    #[test]
    fn package_build_cache_off_does_not_resolve_or_probe_any_root() {
        let tree = TestDirectory::new("off");
        let loaded = write_package(&tree.join("package"), false);
        let unsafe_override = loaded.root.join("source-owned-cache");

        let cache = open_result_cache(false, &loaded, Some(&unsafe_override));
        let counters = cache.test_counters();

        assert_eq!(cache.availability(), PackageBuildCacheAvailability::Off);
        assert_eq!(counters.root_resolutions, 0);
        assert_eq!(counters.cache_io_operations, 0);
        assert!(!unsafe_override.exists());
    }

    #[test]
    fn package_build_cache_unavailable_is_sticky_and_suppresses_entry_io() {
        let tree = TestDirectory::new("sticky-unavailable");
        let loaded = write_package(&tree.join("package"), false);
        let unsafe_override = loaded.root.join("artifact-cache");

        let cache = open_result_cache(true, &loaded, Some(&unsafe_override));
        assert_eq!(
            cache.availability(),
            PackageBuildCacheAvailability::Unavailable
        );
        assert!(cache
            .open_entry(PackageCacheStoreVersion::BUILD_CHECK_RESULT, &entry_key())
            .unwrap()
            .is_none());
        assert!(cache
            .open_entry(PackageCacheStoreVersion::BUILD_CHECK_RESULT, &entry_key())
            .unwrap()
            .is_none());
        assert_eq!(
            cache.test_counters(),
            PackageBuildCacheTestCounters {
                root_resolutions: 1,
                cache_io_operations: 0,
            }
        );
        assert!(!unsafe_override.exists());
    }

    #[cfg(unix)]
    #[test]
    fn package_build_cache_rejects_manifest_artifact_alias() {
        use std::os::unix::fs::symlink;

        let tree = TestDirectory::new("artifact-alias");
        let loaded = write_package(&tree.join("package"), true);
        let external_artifact = tree.join("external-source.npa");
        fs::write(&external_artifact, b"source").unwrap();
        let source = loaded.root.join("Fixture/A/source.npa");
        fs::create_dir_all(source.parent().unwrap()).unwrap();
        symlink(&external_artifact, &source).unwrap();
        let override_base = tree.join("cache");

        let cache = open_result_cache(true, &loaded, Some(&override_base));

        assert_eq!(
            cache.availability(),
            PackageBuildCacheAvailability::Unavailable
        );
        assert!(!override_base.exists());
    }

    #[cfg(unix)]
    #[test]
    fn package_build_cache_security_symlink_candidate_is_unavailable_without_fallback() {
        use std::os::unix::fs::symlink;

        let tree = TestDirectory::new("symlink-candidate");
        let loaded = write_package(&tree.join("package"), false);
        let real = tree.join("real-cache");
        let alias = tree.join("cache-alias");
        fs::create_dir_all(&real).unwrap();
        symlink(&real, &alias).unwrap();

        let cache = open_result_cache(true, &loaded, Some(&alias));

        assert_eq!(
            cache.availability(),
            PackageBuildCacheAvailability::Unavailable
        );
        assert!(!real.join("packages").exists());
    }

    #[cfg(unix)]
    #[test]
    fn package_build_cache_security_rejects_symlinked_layout_and_temporary_components() {
        use std::os::unix::fs::symlink;

        for component in ["packages", "namespace", "version"] {
            let tree = TestDirectory::new(&format!("symlink-layout-{component}"));
            let loaded = write_package(&tree.join("package"), false);
            let override_base = tree.join("cache");
            let namespace = package_build_check_cache_namespace_digest(&loaded.validated);
            let store = support_store_path(&override_base, &namespace);
            let link = match component {
                "packages" => override_base.join("packages"),
                "namespace" => store.parent().unwrap().to_path_buf(),
                "version" => store.clone(),
                _ => unreachable!(),
            };
            let escape = tree.join(format!("escape-{component}"));
            fs::create_dir_all(link.parent().unwrap()).unwrap();
            fs::create_dir_all(&escape).unwrap();
            symlink(&escape, &link).unwrap();

            let (cache, _) = open_support_cache(&loaded, &override_base);

            assert_eq!(
                cache.availability(),
                PackageBuildCacheAvailability::Unavailable,
                "symlinked {component} component was accepted"
            );
            assert_eq!(
                fs::read_dir(&escape).unwrap().count(),
                0,
                "symlinked {component} component redirected cache writes"
            );
        }

        assert_eq!(
            PackageCacheStoreLayout::targeted_authoring_support(
                &PackageCacheNamespaceDigest::parse(&"0".repeat(64)).unwrap(),
            )
            .relative_path()
            .components()
            .count(),
            3,
            "the typed packages/namespace/version layout has no shard component to swap"
        );

        let tree = TestDirectory::new("symlink-temporary");
        let loaded = write_package(&tree.join("package"), false);
        let override_base = tree.join("cache");
        let (cache, namespace) = open_support_cache(&loaded, &override_base);
        assert_eq!(
            cache.availability(),
            PackageBuildCacheAvailability::Available
        );
        let entry = support_context_entry(&namespace, "Fixture.Temporary", false);
        let key = PackageCacheKeyDigest::from_cache_key(&entry.cache_key).unwrap();
        let temporary = PackageCacheTemporaryName::new(&key, "security-symlink").unwrap();
        let temporary_path =
            support_store_path(&override_base, &namespace).join(temporary.as_str());
        let protected = loaded.root.join("npa-package.toml");
        let protected_before = fs::read(&protected).unwrap();
        symlink(&protected, &temporary_path).unwrap();

        assert!(cache
            .create_temporary_entry(
                PackageCacheStoreVersion::TARGETED_AUTHORING_SUPPORT,
                &temporary,
            )
            .is_err());
        assert_eq!(fs::read(&protected).unwrap(), protected_before);
        assert!(fs::symlink_metadata(temporary_path)
            .unwrap()
            .file_type()
            .is_symlink());
    }

    #[cfg(unix)]
    #[test]
    fn package_build_cache_symlink_git_marker_is_unavailable_without_sibling_fallback() {
        use std::os::unix::fs::symlink;

        let tree = TestDirectory::new("symlink-git-marker");
        let package = tree.join("package");
        let git_dir = tree.join("git-metadata");
        fs::create_dir_all(&package).unwrap();
        fs::create_dir_all(&git_dir).unwrap();
        symlink(&git_dir, package.join(".git")).unwrap();
        let loaded = write_package(&package, false);

        let cache = open_result_cache(true, &loaded, None);

        assert_eq!(
            cache.availability(),
            PackageBuildCacheAvailability::Unavailable
        );
        assert!(!tree.join("target/npa-package-audit-cache").exists());
    }

    #[cfg(unix)]
    #[test]
    fn package_build_cache_symlink_package_root_is_unavailable() {
        use std::os::unix::fs::symlink;

        let tree = TestDirectory::new("symlink-package-root");
        let real_package = tree.join("real-package");
        let loaded = write_package(&real_package, false);
        let alias = tree.join("package-alias");
        symlink(&real_package, &alias).unwrap();
        let mut aliased_loaded = loaded;
        aliased_loaded.root = alias;
        let override_base = tree.join("cache");

        let cache = open_result_cache(true, &aliased_loaded, Some(&override_base));

        assert_eq!(
            cache.availability(),
            PackageBuildCacheAvailability::Unavailable
        );
        assert!(!override_base.exists());
    }

    #[cfg(unix)]
    #[test]
    fn package_build_cache_security_symlink_swap_cannot_redirect_retained_store_handle() {
        use std::os::unix::fs::symlink;

        let tree = TestDirectory::new("symlink-swap");
        let loaded = write_package(&tree.join("package"), false);
        let override_base = tree.join("cache");
        let namespace = package_build_check_cache_namespace_digest(&loaded.validated);
        let cache = open_result_cache(true, &loaded, Some(&override_base));
        let store = override_base
            .join(PackageCacheStoreLayout::build_check_result(&namespace).relative_path());
        let entry = store.join(format!("{}.json", entry_key().as_str()));
        fs::write(&entry, b"retained-directory").unwrap();

        let packages = override_base.join("packages");
        let retained_packages = override_base.join("packages-retained");
        fs::rename(&packages, &retained_packages).unwrap();
        symlink(&loaded.root, &packages).unwrap();

        let mut opened = cache
            .open_entry(PackageCacheStoreVersion::BUILD_CHECK_RESULT, &entry_key())
            .unwrap()
            .unwrap();
        let mut contents = String::new();
        opened.read_to_string(&mut contents).unwrap();
        assert_eq!(contents, "retained-directory");
        assert!(!loaded.root.join(namespace.as_str()).exists());
    }

    #[cfg(unix)]
    #[test]
    fn package_build_cache_security_symlink_entry_is_never_followed() {
        use std::os::unix::fs::symlink;

        let tree = TestDirectory::new("symlink-entry");
        let loaded = write_package(&tree.join("package"), false);
        let override_base = tree.join("cache");
        let namespace = package_build_check_cache_namespace_digest(&loaded.validated);
        let cache = open_result_cache(true, &loaded, Some(&override_base));
        let store = override_base
            .join(PackageCacheStoreLayout::build_check_result(&namespace).relative_path());
        let protected = loaded.root.join("npa-package.toml");
        symlink(
            &protected,
            store.join(format!("{}.json", entry_key().as_str())),
        )
        .unwrap();

        assert!(cache
            .open_entry(PackageCacheStoreVersion::BUILD_CHECK_RESULT, &entry_key())
            .is_err());
    }

    #[cfg(unix)]
    #[test]
    fn package_build_cache_security_read_only_root_is_unavailable() {
        use std::os::unix::fs::PermissionsExt;

        let tree = TestDirectory::new("read-only");
        let loaded = write_package(&tree.join("package"), false);
        let parent = tree.join("read-only-parent");
        fs::create_dir_all(&parent).unwrap();
        fs::set_permissions(&parent, fs::Permissions::from_mode(0o500)).unwrap();

        let cache = open_result_cache(true, &loaded, Some(&parent.join("cache")));

        fs::set_permissions(&parent, fs::Permissions::from_mode(0o700)).unwrap();
        assert_eq!(
            cache.availability(),
            PackageBuildCacheAvailability::Unavailable
        );
        assert_eq!(cache.test_counters().cache_io_operations, 0);
    }

    #[cfg(unix)]
    #[test]
    fn package_build_cache_security_read_only_existing_store_fails_capability_probe() {
        use std::os::unix::fs::PermissionsExt;

        let tree = TestDirectory::new("read-only-store");
        let loaded = write_package(&tree.join("package"), false);
        let override_base = tree.join("cache");
        let namespace = package_build_check_cache_namespace_digest(&loaded.validated);
        let first = open_result_cache(true, &loaded, Some(&override_base));
        assert_eq!(
            first.availability(),
            PackageBuildCacheAvailability::Available
        );
        drop(first);
        let store = override_base
            .join(PackageCacheStoreLayout::build_check_result(&namespace).relative_path());
        fs::set_permissions(&store, fs::Permissions::from_mode(0o500)).unwrap();

        let second = open_result_cache(true, &loaded, Some(&override_base));

        fs::set_permissions(&store, fs::Permissions::from_mode(0o700)).unwrap();
        assert_eq!(
            second.availability(),
            PackageBuildCacheAvailability::Unavailable
        );
        assert_eq!(second.test_counters().cache_io_operations, 0);
    }

    #[test]
    fn package_build_cache_checkout_tree_is_ignored_and_sibling_is_outside_status_scope() {
        let ignore = include_str!("../../../../.gitignore");
        assert!(ignore.lines().any(|line| line == "/target/"));

        let tree = TestDirectory::new("status-scope");
        let checkout = tree.join("checkout");
        fs::create_dir_all(checkout.join(".git")).unwrap();
        let loaded = write_package(&checkout, false);
        let cache = open_result_cache(true, &loaded, None);

        assert!(!cache.test_cache_base().unwrap().starts_with(&checkout));
    }

    #[cfg(unix)]
    #[test]
    fn package_build_cache_security_hostile_support_entries_are_bounded() {
        use std::os::unix::fs::{symlink, PermissionsExt};

        let tree = TestDirectory::new("support-context-store");
        let loaded = write_package(&tree.join("package"), false);
        let override_base = tree.join("cache");
        let (cache, namespace) = open_support_cache(&loaded, &override_base);
        assert_eq!(
            cache.availability(),
            PackageBuildCacheAvailability::Available
        );
        let store = support_store_path(&override_base, &namespace);
        let entry = support_context_entry(&namespace, "Fixture.A", false);
        let other = support_context_entry(&namespace, "Fixture.B", false);

        let mut budget = TargetedAuthoringSupportContextStoreBudget::new();
        assert_eq!(
            read_targeted_authoring_support_context_store(&cache, &other.cache_key, &mut budget),
            TargetedAuthoringSupportContextStoreLookup::Missing
        );
        assert_eq!(budget.addressed_entries(), 1);

        let mut publish_budget = TargetedAuthoringSupportContextStoreBudget::new();
        assert_eq!(
            publish_targeted_authoring_support_context_store(&cache, &entry, &mut publish_budget,),
            TargetedAuthoringSupportContextPublishOutcome::Published
        );
        assert_eq!(publish_budget.addressed_entries(), 1);
        assert!(publish_budget.loaded_bytes() > 0);
        assert!(publish_budget.written_bytes() > 0);
        let entry_path = support_entry_path(&store, &entry);
        let installed = fs::read(&entry_path).unwrap();

        assert_eq!(
            read_targeted_authoring_support_context_store(
                &cache,
                &other.cache_key,
                &mut TargetedAuthoringSupportContextStoreBudget::new(),
            ),
            TargetedAuthoringSupportContextStoreLookup::Missing
        );

        let mut lookup_budget = TargetedAuthoringSupportContextStoreBudget::new();
        assert!(matches!(
            read_targeted_authoring_support_context_store(
                &cache,
                &entry.cache_key,
                &mut lookup_budget,
            ),
            TargetedAuthoringSupportContextStoreLookup::Hit(actual) if *actual == entry
        ));
        assert_eq!(lookup_budget.addressed_entries(), 1);

        let operations_before = cache.test_counters().cache_io_operations;
        let mut entry_limit_budget = TargetedAuthoringSupportContextStoreBudget::new();
        entry_limit_budget.exhaust_address_budget();
        assert_eq!(
            read_targeted_authoring_support_context_store(
                &cache,
                &entry.cache_key,
                &mut entry_limit_budget,
            ),
            TargetedAuthoringSupportContextStoreLookup::Invalid
        );
        assert_eq!(cache.test_counters().cache_io_operations, operations_before);

        let mut loaded_limit_budget = TargetedAuthoringSupportContextStoreBudget::new();
        loaded_limit_budget.exhaust_loaded_byte_budget();
        assert_eq!(
            read_targeted_authoring_support_context_store(
                &cache,
                &entry.cache_key,
                &mut loaded_limit_budget,
            ),
            TargetedAuthoringSupportContextStoreLookup::Invalid
        );
        assert_eq!(
            loaded_limit_budget.loaded_bytes(),
            TARGETED_AUTHORING_CACHE_LIMITS_V1.command_loaded_bytes
        );

        let budget_entry = support_context_entry(&namespace, "Fixture.WriteBudget", false);
        let mut written_limit_budget = TargetedAuthoringSupportContextStoreBudget::new();
        written_limit_budget.exhaust_written_byte_budget();
        assert_eq!(
            publish_targeted_authoring_support_context_store(
                &cache,
                &budget_entry,
                &mut written_limit_budget,
            ),
            TargetedAuthoringSupportContextPublishOutcome::Invalid
        );
        assert!(!support_entry_path(&store, &budget_entry).exists());

        let schema_marker =
            format!("\"schema\":\"{PACKAGE_TARGETED_AUTHORING_SUPPORT_CONTEXT_SCHEMA}\"");
        let schema_miss = String::from_utf8(installed.clone()).unwrap().replacen(
            &schema_marker,
            "\"schema\":\"future-schema\"",
            1,
        );
        fs::write(&entry_path, schema_miss).unwrap();
        assert_eq!(
            read_targeted_authoring_support_context_store(
                &cache,
                &entry.cache_key,
                &mut TargetedAuthoringSupportContextStoreBudget::new(),
            ),
            TargetedAuthoringSupportContextStoreLookup::SchemaMiss
        );

        fs::write(&entry_path, b"{").unwrap();
        assert_eq!(
            read_targeted_authoring_support_context_store(
                &cache,
                &entry.cache_key,
                &mut TargetedAuthoringSupportContextStoreBudget::new(),
            ),
            TargetedAuthoringSupportContextStoreLookup::Invalid
        );

        let oversized = File::create(&entry_path).unwrap();
        oversized
            .set_len(
                u64::try_from(TARGETED_AUTHORING_CACHE_LIMITS_V1.support_entry_bytes).unwrap() + 1,
            )
            .unwrap();
        drop(oversized);
        let mut oversized_budget = TargetedAuthoringSupportContextStoreBudget::new();
        assert_eq!(
            read_targeted_authoring_support_context_store(
                &cache,
                &entry.cache_key,
                &mut oversized_budget,
            ),
            TargetedAuthoringSupportContextStoreLookup::Invalid
        );
        assert_eq!(oversized_budget.loaded_bytes(), 0);

        fs::remove_file(&entry_path).unwrap();
        symlink(loaded.root.join("npa-package.toml"), &entry_path).unwrap();
        assert_eq!(
            read_targeted_authoring_support_context_store(
                &cache,
                &entry.cache_key,
                &mut TargetedAuthoringSupportContextStoreBudget::new(),
            ),
            TargetedAuthoringSupportContextStoreLookup::Invalid
        );
        fs::remove_file(&entry_path).unwrap();

        let other_namespace = PackageCacheNamespaceDigest::parse(&"f".repeat(64)).unwrap();
        let stale_namespace = support_context_entry(&other_namespace, "Fixture.A", false);
        assert_eq!(stale_namespace.cache_key, entry.cache_key);
        fs::write(
            &entry_path,
            targeted_authoring_support_context_entry_json(&stale_namespace)
                .unwrap()
                .as_bytes(),
        )
        .unwrap();
        assert_eq!(
            read_targeted_authoring_support_context_store(
                &cache,
                &entry.cache_key,
                &mut TargetedAuthoringSupportContextStoreBudget::new(),
            ),
            TargetedAuthoringSupportContextStoreLookup::Stale
        );

        fs::set_permissions(&entry_path, fs::Permissions::from_mode(0o000)).unwrap();
        assert_eq!(
            read_targeted_authoring_support_context_store(
                &cache,
                &entry.cache_key,
                &mut TargetedAuthoringSupportContextStoreBudget::new(),
            ),
            TargetedAuthoringSupportContextStoreLookup::Unavailable
        );
        fs::set_permissions(&entry_path, fs::Permissions::from_mode(0o600)).unwrap();
        fs::remove_file(&entry_path).unwrap();

        let key = PackageCacheKeyDigest::from_cache_key(&entry.cache_key).unwrap();
        let interrupted = PackageCacheTemporaryName::new(&key, "interrupted-1").unwrap();
        let interrupted_path = store.join(interrupted.as_str());
        fs::write(&interrupted_path, b"partial").unwrap();
        assert_eq!(
            read_targeted_authoring_support_context_store(
                &cache,
                &entry.cache_key,
                &mut TargetedAuthoringSupportContextStoreBudget::new(),
            ),
            TargetedAuthoringSupportContextStoreLookup::Missing
        );
        assert_eq!(
            publish_targeted_authoring_support_context_store(
                &cache,
                &entry,
                &mut TargetedAuthoringSupportContextStoreBudget::new(),
            ),
            TargetedAuthoringSupportContextPublishOutcome::Published
        );
        assert!(interrupted_path.exists());

        let conflicting = support_context_entry(&namespace, "Fixture.A", true);
        assert_eq!(conflicting.cache_key, entry.cache_key);
        assert_ne!(conflicting, entry);
        let mut conflict_budget = TargetedAuthoringSupportContextStoreBudget::new();
        assert_eq!(
            publish_targeted_authoring_support_context_store(
                &cache,
                &conflicting,
                &mut conflict_budget,
            ),
            TargetedAuthoringSupportContextPublishOutcome::Conflict(
                TargetedAuthoringSupportContextWriterValidation::Stale,
            )
        );
        assert!(conflict_budget.loaded_bytes() > 0);
        assert!(conflict_budget.written_bytes() > 0);
        assert_eq!(fs::read(&entry_path).unwrap(), installed);

        fs::write(&entry_path, b"{").unwrap();
        assert_eq!(
            publish_targeted_authoring_support_context_store(
                &cache,
                &entry,
                &mut TargetedAuthoringSupportContextStoreBudget::new(),
            ),
            TargetedAuthoringSupportContextPublishOutcome::Conflict(
                TargetedAuthoringSupportContextWriterValidation::Invalid,
            )
        );
        assert_eq!(fs::read(&entry_path).unwrap(), b"{");

        fs::remove_file(&entry_path).unwrap();
        fs::set_permissions(&store, fs::Permissions::from_mode(0o500)).unwrap();
        let mut failed_write_budget = TargetedAuthoringSupportContextStoreBudget::new();
        assert_eq!(
            publish_targeted_authoring_support_context_store(
                &cache,
                &entry,
                &mut failed_write_budget,
            ),
            TargetedAuthoringSupportContextPublishOutcome::Unavailable
        );
        assert_eq!(failed_write_budget.written_bytes(), 0);
        fs::set_permissions(&store, fs::Permissions::from_mode(0o700)).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn package_build_cache_security_retained_directory_rejects_parent_symlink_swap() {
        use std::os::unix::fs::symlink;

        let tree = TestDirectory::new("support-context-store-symlink-swap");
        let loaded = write_package(&tree.join("package"), false);
        let override_base = tree.join("cache");
        let (cache, namespace) = open_support_cache(&loaded, &override_base);
        let store = support_store_path(&override_base, &namespace);
        let retained_store = store.with_extension("retained");
        let redirected_store = tree.join("redirected-store");
        fs::create_dir_all(&redirected_store).unwrap();
        fs::rename(&store, &retained_store).unwrap();
        symlink(&redirected_store, &store).unwrap();

        let entry = support_context_entry(&namespace, "Fixture.Swap", false);
        assert_eq!(
            publish_targeted_authoring_support_context_store(
                &cache,
                &entry,
                &mut TargetedAuthoringSupportContextStoreBudget::new(),
            ),
            TargetedAuthoringSupportContextPublishOutcome::Published
        );
        assert!(support_entry_path(&retained_store, &entry).is_file());
        assert_eq!(fs::read_dir(&redirected_store).unwrap().count(), 0);
        assert!(matches!(
            read_targeted_authoring_support_context_store(
                &cache,
                &entry.cache_key,
                &mut TargetedAuthoringSupportContextStoreBudget::new(),
            ),
            TargetedAuthoringSupportContextStoreLookup::Hit(_)
        ));

        fs::remove_file(&store).unwrap();
        fs::rename(&retained_store, &store).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn package_build_cache_security_support_store_read_only_capability_is_unavailable() {
        use std::os::unix::fs::PermissionsExt;

        let tree = TestDirectory::new("support-context-store-read-only");
        let loaded = write_package(&tree.join("package"), false);
        let override_base = tree.join("cache");
        let (first, namespace) = open_support_cache(&loaded, &override_base);
        assert_eq!(
            first.availability(),
            PackageBuildCacheAvailability::Available
        );
        drop(first);
        let store = support_store_path(&override_base, &namespace);
        fs::set_permissions(&store, fs::Permissions::from_mode(0o500)).unwrap();

        let (second, _) = open_support_cache(&loaded, &override_base);

        fs::set_permissions(&store, fs::Permissions::from_mode(0o700)).unwrap();
        assert_eq!(
            second.availability(),
            PackageBuildCacheAvailability::Unavailable
        );
        assert_eq!(
            read_targeted_authoring_support_context_store(
                &second,
                &support_context_entry(&namespace, "Fixture.ReadOnly", false).cache_key,
                &mut TargetedAuthoringSupportContextStoreBudget::new(),
            ),
            TargetedAuthoringSupportContextStoreLookup::Unavailable
        );
    }

    #[cfg(unix)]
    #[test]
    fn support_context_store_concurrency_is_atomic_and_never_replaces() {
        let tree = TestDirectory::new("support-context-store-concurrency");
        let loaded = write_package(&tree.join("package"), false);
        let override_base = tree.join("cache");
        let (cache, namespace) = open_support_cache(&loaded, &override_base);
        let cache = Arc::new(cache);
        let equal_entry = Arc::new(support_context_entry(&namespace, "Fixture.Equal", false));
        let barrier = Arc::new(Barrier::new(3));
        let mut writers = Vec::new();
        for _ in 0..2 {
            let cache = Arc::clone(&cache);
            let entry = Arc::clone(&equal_entry);
            let barrier = Arc::clone(&barrier);
            writers.push(std::thread::spawn(move || {
                barrier.wait();
                publish_targeted_authoring_support_context_store(
                    &cache,
                    &entry,
                    &mut TargetedAuthoringSupportContextStoreBudget::new(),
                )
            }));
        }
        barrier.wait();
        let equal_outcomes = writers
            .into_iter()
            .map(|writer| writer.join().unwrap())
            .collect::<Vec<_>>();
        assert!(equal_outcomes.contains(&TargetedAuthoringSupportContextPublishOutcome::Published));
        assert!(
            equal_outcomes.contains(&TargetedAuthoringSupportContextPublishOutcome::ExistingEqual)
        );

        let distinct_a = Arc::new(support_context_entry(
            &namespace,
            "Fixture.DistinctA",
            false,
        ));
        let distinct_b = Arc::new(support_context_entry(
            &namespace,
            "Fixture.DistinctB",
            false,
        ));
        let barrier = Arc::new(Barrier::new(3));
        let mut distinct_writers = Vec::new();
        for entry in [distinct_a, distinct_b] {
            let cache = Arc::clone(&cache);
            let barrier = Arc::clone(&barrier);
            distinct_writers.push(std::thread::spawn(move || {
                barrier.wait();
                publish_targeted_authoring_support_context_store(
                    &cache,
                    &entry,
                    &mut TargetedAuthoringSupportContextStoreBudget::new(),
                )
            }));
        }
        barrier.wait();
        for writer in distinct_writers {
            assert_eq!(
                writer.join().unwrap(),
                TargetedAuthoringSupportContextPublishOutcome::Published
            );
        }

        let conflict_plain = Arc::new(support_context_entry(
            &namespace,
            "Fixture.ConcurrentConflict",
            false,
        ));
        let conflict_declaration = Arc::new(support_context_entry(
            &namespace,
            "Fixture.ConcurrentConflict",
            true,
        ));
        assert_eq!(conflict_plain.cache_key, conflict_declaration.cache_key);
        let barrier = Arc::new(Barrier::new(3));
        let mut conflict_writers = Vec::new();
        for entry in [conflict_plain, conflict_declaration] {
            let cache = Arc::clone(&cache);
            let barrier = Arc::clone(&barrier);
            conflict_writers.push(std::thread::spawn(move || {
                barrier.wait();
                publish_targeted_authoring_support_context_store(
                    &cache,
                    &entry,
                    &mut TargetedAuthoringSupportContextStoreBudget::new(),
                )
            }));
        }
        barrier.wait();
        let conflict_outcomes = conflict_writers
            .into_iter()
            .map(|writer| writer.join().unwrap())
            .collect::<Vec<_>>();
        assert!(
            conflict_outcomes.contains(&TargetedAuthoringSupportContextPublishOutcome::Published)
        );
        assert!(conflict_outcomes.contains(
            &TargetedAuthoringSupportContextPublishOutcome::Conflict(
                TargetedAuthoringSupportContextWriterValidation::Stale,
            )
        ));

        let reader_entry = Arc::new(support_context_entry(&namespace, "Fixture.Reader", false));
        let (ready_sender, ready_receiver) = mpsc::channel();
        let (release_sender, release_receiver) = mpsc::channel();
        let writer = {
            let cache = Arc::clone(&cache);
            let entry = Arc::clone(&reader_entry);
            std::thread::spawn(move || {
                publish_targeted_authoring_support_context_store_with_before_publish(
                    &cache,
                    &entry,
                    &mut TargetedAuthoringSupportContextStoreBudget::new(),
                    || {
                        ready_sender.send(()).unwrap();
                        release_receiver.recv().unwrap();
                    },
                )
            })
        };
        ready_receiver.recv().unwrap();
        assert_eq!(
            read_targeted_authoring_support_context_store(
                &cache,
                &reader_entry.cache_key,
                &mut TargetedAuthoringSupportContextStoreBudget::new(),
            ),
            TargetedAuthoringSupportContextStoreLookup::Missing
        );
        release_sender.send(()).unwrap();
        assert_eq!(
            writer.join().unwrap(),
            TargetedAuthoringSupportContextPublishOutcome::Published
        );
        assert!(matches!(
            read_targeted_authoring_support_context_store(
                &cache,
                &reader_entry.cache_key,
                &mut TargetedAuthoringSupportContextStoreBudget::new(),
            ),
            TargetedAuthoringSupportContextStoreLookup::Hit(_)
        ));
    }
}

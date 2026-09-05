//! Owned certificate artifacts and operation-local decoded retention.

use std::{collections::BTreeMap, sync::Arc};

use npa_cert::{
    AxiomReport, CertHeader, RetainedDecodedModuleCert, PACKAGE_SHARED_CACHE_RETAINED_BYTE_LIMIT_V1,
};

use crate::{PackageHash, PackageLockManifest, PackagePath};

/// Maximum decoded certificates retained by one prepared-artifact owner.
pub const PREPARED_ARTIFACT_RETAINED_ENTRY_LIMIT_V1: usize = 1_024;
/// Maximum logical decoded bytes retained by one prepared-artifact owner.
pub const PREPARED_ARTIFACT_RETAINED_BYTE_LIMIT_V1: u64 =
    PACKAGE_SHARED_CACHE_RETAINED_BYTE_LIMIT_V1;

/// Immutable package-relative path and certificate bytes owned by one operation.
#[derive(Clone, Debug)]
pub struct OwnedPackageLockArtifact {
    payload: Arc<OwnedPackageLockArtifactPayload>,
}

#[derive(Debug)]
struct OwnedPackageLockArtifactPayload {
    path: PackagePath,
    bytes: Vec<u8>,
}

impl OwnedPackageLockArtifact {
    /// Move certificate bytes into a shared immutable owner without copying the buffer.
    pub fn from_vec(path: PackagePath, bytes: Vec<u8>) -> Self {
        Self {
            payload: Arc::new(OwnedPackageLockArtifactPayload { path, bytes }),
        }
    }

    /// Return the package-relative certificate path.
    pub fn path(&self) -> &PackagePath {
        &self.payload.path
    }

    /// Return the exact certificate bytes.
    pub fn bytes(&self) -> &[u8] {
        &self.payload.bytes
    }
}

/// Owned certificate bytes paired with the file hash computed by lock derivation.
#[derive(Clone, Debug)]
pub struct HashedPackageLockArtifact {
    raw: OwnedPackageLockArtifact,
    file_hash: PackageHash,
}

impl HashedPackageLockArtifact {
    pub(crate) fn from_lock_derivation(
        raw: OwnedPackageLockArtifact,
        file_hash: PackageHash,
    ) -> Self {
        Self { raw, file_hash }
    }

    /// Return the package-relative certificate path.
    pub fn path(&self) -> &PackagePath {
        self.raw.path()
    }

    /// Return the exact certificate bytes.
    pub fn bytes(&self) -> &[u8] {
        self.raw.bytes()
    }

    /// Return the file hash already computed by lock derivation.
    pub fn file_hash(&self) -> PackageHash {
        self.file_hash
    }
}

/// One hashed certificate with an optional move-only retained decoded capability.
#[derive(Debug)]
pub struct PackageCertificateArtifactSnapshot {
    hashed: HashedPackageLockArtifact,
    decoded: Option<RetainedDecodedModuleCert>,
    decoded_charge: u64,
}

impl PackageCertificateArtifactSnapshot {
    pub(crate) fn from_lock_derivation(
        hashed: HashedPackageLockArtifact,
        decoded: Option<RetainedDecodedModuleCert>,
        decoded_charge: u64,
    ) -> Self {
        debug_assert_eq!(decoded.is_some(), decoded_charge > 0);
        Self {
            hashed,
            decoded,
            decoded_charge,
        }
    }

    /// Return the package-relative certificate path.
    pub fn path(&self) -> &PackagePath {
        self.hashed.path()
    }

    /// Return the exact certificate bytes.
    pub fn bytes(&self) -> &[u8] {
        self.hashed.bytes()
    }

    /// Return the file hash already computed by lock derivation.
    pub fn file_hash(&self) -> PackageHash {
        self.hashed.file_hash()
    }

    /// Borrow the retained decoded capability, when admission retained it.
    pub fn retained_decoded(&self) -> Option<&RetainedDecodedModuleCert> {
        self.decoded.as_ref()
    }

    /// Return the retained decoded header, when present.
    pub fn decoded_header(&self) -> Option<&CertHeader> {
        self.decoded.as_ref().map(RetainedDecodedModuleCert::header)
    }

    /// Return the retained decoded axiom report, when present.
    pub fn decoded_axiom_report(&self) -> Option<&AxiomReport> {
        self.decoded
            .as_ref()
            .map(RetainedDecodedModuleCert::axiom_report)
    }
}

/// Decoded retention policy selected before lock derivation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PreparedArtifactRetentionPolicy {
    /// Preserve only owned bytes and their derived file hashes.
    RawOnly,
    /// Retain decoded values within the deterministic v1 operation limits.
    FastCandidateV1,
}

/// Whether optional aggregate retention telemetry is collected.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PreparedArtifactObservationMode {
    /// Maintain only mandatory admission accounting.
    Off,
    /// Maintain mandatory accounting and an aggregate observation.
    Aggregate,
}

/// Work attempted by the owned lock builder.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PackageArtifactPreparationObservation {
    /// Certificate-byte file-hash attempts.
    pub artifact_file_hashes: u64,
    /// Full certificate-decode attempts.
    pub artifact_full_decodes: u64,
    /// Whether an observation counter saturated.
    pub overflowed: bool,
}

impl PackageArtifactPreparationObservation {
    pub(crate) fn observe_file_hash(&mut self) {
        saturating_increment(&mut self.artifact_file_hashes, &mut self.overflowed);
    }

    pub(crate) fn observe_full_decode(&mut self) {
        saturating_increment(&mut self.artifact_full_decodes, &mut self.overflowed);
    }
}

/// Aggregate decoded-retention observation for one prepared owner.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PreparedArtifactRetentionObservation {
    /// Successful decoded admissions.
    pub admissions: u64,
    /// Logical bytes admitted across all successful admissions.
    pub admitted_bytes: u64,
    /// Currently retained decoded entries.
    pub current_entries: u64,
    /// Peak retained decoded entries.
    pub peak_entries: u64,
    /// Currently retained decoded logical bytes.
    pub current_bytes: u64,
    /// Peak retained decoded logical bytes.
    pub peak_bytes: u64,
    /// Current candidate bytes observed during derivation.
    pub derivation_candidate_current_bytes: u64,
    /// Peak candidate bytes observed during derivation.
    pub derivation_candidate_peak_bytes: u64,
    /// Admissions rejected by the entry limit.
    pub entry_limit_fallbacks: u64,
    /// Admissions rejected by the byte limit.
    pub byte_limit_fallbacks: u64,
    /// Admissions rejected because charge arithmetic saturated.
    pub saturated_charge_fallbacks: u64,
    /// Charged prepared-to-raw releases.
    pub charged_releases: u64,
    /// Logical bytes released across charged releases.
    pub released_bytes: u64,
    /// Whether any observation arithmetic saturated.
    pub overflowed: bool,
}

#[derive(Debug)]
struct PreparedArtifactRetentionState {
    current_entries: usize,
    current_bytes: u64,
    observation: Option<PreparedArtifactRetentionObservation>,
}

impl PreparedArtifactRetentionState {
    fn new(mode: PreparedArtifactObservationMode) -> Self {
        Self {
            current_entries: 0,
            current_bytes: 0,
            observation: (mode == PreparedArtifactObservationMode::Aggregate)
                .then(PreparedArtifactRetentionObservation::default),
        }
    }

    fn admit(&mut self, charge: u64) -> bool {
        if let Some(observation) = &mut self.observation {
            observation.derivation_candidate_current_bytes = charge;
            observation.derivation_candidate_peak_bytes =
                observation.derivation_candidate_peak_bytes.max(charge);
        }
        if charge == u64::MAX {
            if let Some(observation) = &mut self.observation {
                saturating_increment(
                    &mut observation.saturated_charge_fallbacks,
                    &mut observation.overflowed,
                );
                observation.overflowed = true;
            }
            return false;
        }
        if self.current_entries >= PREPARED_ARTIFACT_RETAINED_ENTRY_LIMIT_V1 {
            if let Some(observation) = &mut self.observation {
                saturating_increment(
                    &mut observation.entry_limit_fallbacks,
                    &mut observation.overflowed,
                );
            }
            return false;
        }
        let Some(next_bytes) = self.current_bytes.checked_add(charge) else {
            if let Some(observation) = &mut self.observation {
                saturating_increment(
                    &mut observation.saturated_charge_fallbacks,
                    &mut observation.overflowed,
                );
                observation.overflowed = true;
            }
            return false;
        };
        if next_bytes > PREPARED_ARTIFACT_RETAINED_BYTE_LIMIT_V1 {
            if let Some(observation) = &mut self.observation {
                saturating_increment(
                    &mut observation.byte_limit_fallbacks,
                    &mut observation.overflowed,
                );
            }
            return false;
        }
        self.current_entries += 1;
        self.current_bytes = next_bytes;
        if let Some(observation) = &mut self.observation {
            saturating_increment(&mut observation.admissions, &mut observation.overflowed);
            saturating_add(
                &mut observation.admitted_bytes,
                charge,
                &mut observation.overflowed,
            );
            observation.current_entries = u64::try_from(self.current_entries).unwrap_or(u64::MAX);
            observation.peak_entries = observation.peak_entries.max(observation.current_entries);
            observation.current_bytes = self.current_bytes;
            observation.peak_bytes = observation.peak_bytes.max(self.current_bytes);
        }
        true
    }

    fn finish_derivation_candidate(&mut self) {
        if let Some(observation) = &mut self.observation {
            observation.derivation_candidate_current_bytes = 0;
        }
    }

    fn release(&mut self, charge: u64) {
        debug_assert!(self.current_entries > 0);
        debug_assert!(self.current_bytes >= charge);
        self.current_entries = self.current_entries.saturating_sub(1);
        self.current_bytes = self.current_bytes.saturating_sub(charge);
        if let Some(observation) = &mut self.observation {
            observation.current_entries = u64::try_from(self.current_entries).unwrap_or(u64::MAX);
            observation.current_bytes = self.current_bytes;
            saturating_increment(
                &mut observation.charged_releases,
                &mut observation.overflowed,
            );
            saturating_add(
                &mut observation.released_bytes,
                charge,
                &mut observation.overflowed,
            );
        }
    }

    fn observation(&self) -> Option<PreparedArtifactRetentionObservation> {
        self.observation
    }
}

/// Reason a coordinator no longer needs a retained decoded value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PreparedArtifactReleaseReason {
    /// The module is outside the fast execution closure.
    Unselected,
    /// A conclusive process-memo result was used.
    ProcessMemoHit,
    /// A conclusive local-audit cache result was used.
    LocalAuditCacheResult,
    /// A conclusive disk-memo result was used.
    DiskMemoResult,
    /// The module was blocked or skipped before live checking.
    BlockedOrSkippedResult,
    /// Live verification completed.
    LiveResult,
    /// The operation is releasing all remaining decoded values.
    OperationTeardown,
}

/// Result of one prepared-to-hashed-raw release attempt.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PreparedArtifactRelease {
    /// A charged retained decoded value was released.
    Charged {
        /// Logical bytes removed from current retention.
        released_bytes: u64,
    },
    /// An uncharged prepared fallback became an ordinary hashed-raw slot.
    RawFallbackTransition,
    /// The slot was already hashed raw.
    AlreadyRaw,
    /// The artifact owner has no slot for the requested path.
    NotFound,
}

#[derive(Debug)]
enum PackageArtifactSlot {
    Prepared(PackageCertificateArtifactSnapshot),
    HashedRaw(HashedPackageLockArtifact),
}

/// Read-only artifact view used by checker adapters.
#[derive(Clone, Copy, Debug)]
pub enum PreparedPackageArtifactView<'a> {
    /// Hashed raw bytes without a prepared decoded capability.
    Hashed(&'a HashedPackageLockArtifact),
    /// A prepared snapshot, possibly with a retained decoded capability.
    Prepared(&'a PackageCertificateArtifactSnapshot),
}

/// Layer-scoped read-only view of the canonical prepared-artifact owner.
///
/// The view keeps an immutable borrow of the owner for its complete lifetime,
/// so the coordinator cannot release decoded payloads until every worker view
/// has been dropped. Raw handles cloned through the view remain independent of
/// decoded-retention accounting.
#[derive(Clone, Copy, Debug)]
pub struct PreparedPackageArtifactWorkerView<'a> {
    artifacts: &'a PreparedPackageArtifacts,
}

impl<'a> PreparedPackageArtifactWorkerView<'a> {
    /// Borrow one worker input by package-relative artifact path.
    pub fn get(&self, path: &PackagePath) -> Option<PreparedPackageArtifactView<'a>> {
        self.artifacts.get(path)
    }

    /// Clone one immutable hashed-raw handle for an independent worker lane.
    pub fn clone_hashed_raw(&self, path: &PackagePath) -> Option<HashedPackageLockArtifact> {
        self.artifacts.clone_hashed_raw(path)
    }
}

/// Operation-local canonical owner of prepared and hashed-raw artifact slots.
#[derive(Debug)]
pub struct PreparedPackageArtifacts {
    slots: Vec<PackageArtifactSlot>,
    slot_by_path: BTreeMap<PackagePath, usize>,
    retention: PreparedArtifactRetentionState,
}

impl PreparedPackageArtifacts {
    pub(crate) fn new(mode: PreparedArtifactObservationMode) -> Self {
        Self {
            slots: Vec::new(),
            slot_by_path: BTreeMap::new(),
            retention: PreparedArtifactRetentionState::new(mode),
        }
    }

    pub(crate) fn push_derived(
        &mut self,
        hashed: HashedPackageLockArtifact,
        decoded: RetainedDecodedModuleCert,
        policy: PreparedArtifactRetentionPolicy,
    ) {
        let path = hashed.path().clone();
        debug_assert!(!self.slot_by_path.contains_key(&path));
        let slot = if policy == PreparedArtifactRetentionPolicy::FastCandidateV1 {
            let charge = decoded.logical_retained_bytes_v1();
            if self.retention.admit(charge) {
                PackageArtifactSlot::Prepared(
                    PackageCertificateArtifactSnapshot::from_lock_derivation(
                        hashed,
                        Some(decoded),
                        charge,
                    ),
                )
            } else {
                drop(decoded);
                PackageArtifactSlot::Prepared(
                    PackageCertificateArtifactSnapshot::from_lock_derivation(hashed, None, 0),
                )
            }
        } else {
            drop(decoded);
            PackageArtifactSlot::HashedRaw(hashed)
        };
        self.retention.finish_derivation_candidate();
        let index = self.slots.len();
        self.slots.push(slot);
        self.slot_by_path.insert(path, index);
    }

    /// Borrow a checker view for one owned artifact path.
    pub fn get(&self, path: &PackagePath) -> Option<PreparedPackageArtifactView<'_>> {
        let slot = self.slots.get(*self.slot_by_path.get(path)?)?;
        Some(match slot {
            PackageArtifactSlot::Prepared(snapshot) => {
                PreparedPackageArtifactView::Prepared(snapshot)
            }
            PackageArtifactSlot::HashedRaw(hashed) => PreparedPackageArtifactView::Hashed(hashed),
        })
    }

    /// Borrow a layer-scoped read-only view for worker dispatch.
    ///
    /// While the returned view is live, Rust's borrow rules prevent a caller
    /// from invoking [`Self::release_decoded`] on this owner.
    pub fn worker_view(&self) -> PreparedPackageArtifactWorkerView<'_> {
        PreparedPackageArtifactWorkerView { artifacts: self }
    }

    /// Clone the immutable hashed-raw handle for an independent checker lane.
    pub fn clone_hashed_raw(&self, path: &PackagePath) -> Option<HashedPackageLockArtifact> {
        match self.slots.get(*self.slot_by_path.get(path)?)? {
            PackageArtifactSlot::Prepared(snapshot) => Some(snapshot.hashed.clone()),
            PackageArtifactSlot::HashedRaw(hashed) => Some(hashed.clone()),
        }
    }

    /// Release one retained decoded value and preserve its bytes and file hash.
    pub fn release_decoded(
        &mut self,
        path: &PackagePath,
        _reason: PreparedArtifactReleaseReason,
    ) -> PreparedArtifactRelease {
        let Some(index) = self.slot_by_path.get(path).copied() else {
            return PreparedArtifactRelease::NotFound;
        };
        let PackageArtifactSlot::Prepared(snapshot) = &self.slots[index] else {
            return PreparedArtifactRelease::AlreadyRaw;
        };
        let hashed = snapshot.hashed.clone();
        let charge = snapshot.decoded_charge;
        let had_decoded = snapshot.decoded.is_some();
        self.slots[index] = PackageArtifactSlot::HashedRaw(hashed);
        if had_decoded {
            self.retention.release(charge);
            PreparedArtifactRelease::Charged {
                released_bytes: charge,
            }
        } else {
            PreparedArtifactRelease::RawFallbackTransition
        }
    }

    /// Release every remaining prepared slot in deterministic builder order.
    ///
    /// This is the non-fallible operation-teardown transition. Hashed-raw slots
    /// remain unchanged and every retained charge is removed exactly once.
    pub fn release_all_decoded(&mut self, reason: PreparedArtifactReleaseReason) {
        for index in 0..self.slots.len() {
            let path = match &self.slots[index] {
                PackageArtifactSlot::Prepared(snapshot) => snapshot.path().clone(),
                PackageArtifactSlot::HashedRaw(_) => continue,
            };
            let release = self.release_decoded(&path, reason);
            debug_assert!(!matches!(release, PreparedArtifactRelease::NotFound));
        }
    }

    /// Return the aggregate retention observation when enabled.
    pub fn retention_observation(&self) -> Option<PreparedArtifactRetentionObservation> {
        self.retention.observation()
    }

    /// Return the mandatory number of retained decoded values.
    pub fn retained_decoded_entries(&self) -> usize {
        self.retention.current_entries
    }

    /// Return the mandatory logical retained-byte total.
    pub fn retained_decoded_bytes(&self) -> u64 {
        self.retention.current_bytes
    }
}

/// Successful owned lock derivation and its canonical prepared-artifact owner.
#[derive(Debug)]
pub struct PackageLockArtifactSnapshots {
    lock: PackageLockManifest,
    artifacts: PreparedPackageArtifacts,
}

impl PackageLockArtifactSnapshots {
    pub(crate) fn new(lock: PackageLockManifest, artifacts: PreparedPackageArtifacts) -> Self {
        Self { lock, artifacts }
    }

    /// Move out the canonical lock and prepared artifact owner.
    pub fn into_parts(self) -> (PackageLockManifest, PreparedPackageArtifacts) {
        (self.lock, self.artifacts)
    }
}

fn saturating_increment(field: &mut u64, overflowed: &mut bool) {
    saturating_add(field, 1, overflowed);
}

fn saturating_add(field: &mut u64, value: u64, overflowed: &mut bool) {
    let (sum, overflow) = field.overflowing_add(value);
    *field = if overflow { u64::MAX } else { sum };
    *overflowed |= overflow;
}

#[cfg(test)]
mod tests {
    use super::*;
    use npa_cert::{AxiomReport, CertHeader, ModuleCert, ModuleCertParts, ModuleHashes, Name};

    fn decoded(path: &str) -> (HashedPackageLockArtifact, RetainedDecodedModuleCert) {
        let path = PackagePath::new(path);
        let owned = OwnedPackageLockArtifact::from_vec(path, vec![1, 2, 3]);
        let hashed = HashedPackageLockArtifact::from_lock_derivation(owned, PackageHash([4; 32]));
        let module = ModuleCert::from_parts(ModuleCertParts {
            header: CertHeader {
                format: "NPA-CERT-0.3.0".to_owned(),
                core_spec: "NPA-Core-0.3.0".to_owned(),
                module: Name::from_dotted("Snapshot.Test"),
            },
            imports: Vec::new(),
            name_table: Vec::new(),
            level_table: Vec::new(),
            term_table: Vec::new(),
            declarations: Vec::new(),
            export_block: Vec::new(),
            axiom_report: AxiomReport {
                per_declaration: Vec::new(),
                module_axioms: Vec::new(),
                core_features: Vec::new(),
            },
            hashes: ModuleHashes {
                export_hash: [5; 32],
                axiom_report_hash: [6; 32],
                certificate_hash: [7; 32],
            },
        });
        (hashed, RetainedDecodedModuleCert::from_decoded(module))
    }

    #[test]
    fn admission_and_release_update_mandatory_and_optional_state() {
        let (hashed, decoded) = decoded("proofs/test.npcert");
        let path = hashed.path().clone();
        let mut artifacts =
            PreparedPackageArtifacts::new(PreparedArtifactObservationMode::Aggregate);
        artifacts.push_derived(
            hashed,
            decoded,
            PreparedArtifactRetentionPolicy::FastCandidateV1,
        );
        let before = artifacts.retention_observation().expect("observation");
        assert_eq!(before.admissions, 1);
        assert_eq!(before.current_entries, 1);
        assert_eq!(before.derivation_candidate_current_bytes, 0);
        assert!(before.derivation_candidate_peak_bytes > 0);
        assert_eq!(artifacts.retained_decoded_entries(), 1);
        assert_eq!(artifacts.retained_decoded_bytes(), before.current_bytes);
        let released =
            artifacts.release_decoded(&path, PreparedArtifactReleaseReason::OperationTeardown);
        assert!(matches!(released, PreparedArtifactRelease::Charged { .. }));
        assert_eq!(
            artifacts.retention_observation().unwrap().current_entries,
            0
        );
        assert_eq!(artifacts.retained_decoded_entries(), 0);
        assert_eq!(artifacts.retained_decoded_bytes(), 0);
        assert_eq!(
            artifacts.release_decoded(&path, PreparedArtifactReleaseReason::OperationTeardown),
            PreparedArtifactRelease::AlreadyRaw
        );
    }

    #[test]
    fn raw_only_never_retains_decoded_payload() {
        let (hashed, decoded) = decoded("proofs/raw.npcert");
        let path = hashed.path().clone();
        let mut artifacts = PreparedPackageArtifacts::new(PreparedArtifactObservationMode::Off);
        artifacts.push_derived(hashed, decoded, PreparedArtifactRetentionPolicy::RawOnly);
        assert!(matches!(
            artifacts.get(&path),
            Some(PreparedPackageArtifactView::Hashed(_))
        ));
        assert_eq!(artifacts.retention_observation(), None);
    }

    #[test]
    fn owned_package_lock_artifact() {
        let bytes = vec![11, 22, 33, 44];
        let allocation = bytes.as_ptr();
        let artifact =
            OwnedPackageLockArtifact::from_vec(PackagePath::new("proofs/owned.npcert"), bytes);

        assert_eq!(artifact.path().as_str(), "proofs/owned.npcert");
        assert_eq!(artifact.bytes(), [11, 22, 33, 44]);
        assert_eq!(artifact.bytes().as_ptr(), allocation);

        let clone = artifact.clone();
        assert_eq!(clone.bytes().as_ptr(), allocation);
        assert!(Arc::ptr_eq(&artifact.payload, &clone.payload));
    }

    #[test]
    fn hashed_package_lock_artifact() {
        let path = PackagePath::new("proofs/hashed.npcert");
        let raw = OwnedPackageLockArtifact::from_vec(path.clone(), vec![1, 3, 5]);
        let bytes = raw.bytes().as_ptr();
        let expected_hash = PackageHash([9; 32]);
        let hashed = HashedPackageLockArtifact::from_lock_derivation(raw, expected_hash);

        assert_eq!(hashed.path(), &path);
        assert_eq!(hashed.bytes(), [1, 3, 5]);
        assert_eq!(hashed.file_hash(), expected_hash);
        assert_eq!(hashed.clone().bytes().as_ptr(), bytes);
    }

    #[test]
    fn package_certificate_artifact_snapshot() {
        let (hashed, decoded) = decoded("proofs/snapshot.npcert");
        let charge = decoded.logical_retained_bytes_v1();
        let expected_hash = hashed.file_hash();
        let snapshot =
            PackageCertificateArtifactSnapshot::from_lock_derivation(hashed, Some(decoded), charge);

        assert_eq!(snapshot.path().as_str(), "proofs/snapshot.npcert");
        assert_eq!(snapshot.bytes(), [1, 2, 3]);
        assert_eq!(snapshot.file_hash(), expected_hash);
        assert!(snapshot.retained_decoded().is_some());
        assert_eq!(
            snapshot.decoded_header().unwrap().module.as_dotted(),
            "Snapshot.Test"
        );
        assert!(snapshot
            .decoded_axiom_report()
            .unwrap()
            .module_axioms
            .is_empty());
    }

    #[test]
    fn prepared_package_artifact_lookup() {
        let (hashed, decoded) = decoded("proofs/lookup.npcert");
        let path = hashed.path().clone();
        let mut artifacts = PreparedPackageArtifacts::new(PreparedArtifactObservationMode::Off);
        artifacts.push_derived(
            hashed,
            decoded,
            PreparedArtifactRetentionPolicy::FastCandidateV1,
        );

        let Some(PreparedPackageArtifactView::Prepared(snapshot)) = artifacts.get(&path) else {
            panic!("prepared path should resolve to its canonical slot");
        };
        assert_eq!(snapshot.path(), &path);
        assert!(snapshot.retained_decoded().is_some());
        assert!(artifacts
            .get(&PackagePath::new("proofs/missing.npcert"))
            .is_none());
    }

    #[test]
    fn prepared_package_artifact_worker_view() {
        let (hashed, decoded) = decoded("proofs/worker.npcert");
        let path = hashed.path().clone();
        let mut artifacts =
            PreparedPackageArtifacts::new(PreparedArtifactObservationMode::Aggregate);
        artifacts.push_derived(
            hashed,
            decoded,
            PreparedArtifactRetentionPolicy::FastCandidateV1,
        );

        let cloned = {
            let view = artifacts.worker_view();
            assert!(matches!(
                view.get(&path),
                Some(PreparedPackageArtifactView::Prepared(_))
            ));
            view.clone_hashed_raw(&path).expect("worker raw clone")
        };
        assert_eq!(cloned.path(), &path);
        assert_eq!(cloned.bytes(), [1, 2, 3]);

        // This mutable transition compiles only after the immutable worker
        // view's final use, which is the scoped-borrow invariant under test.
        assert!(matches!(
            artifacts.release_decoded(&path, PreparedArtifactReleaseReason::LiveResult),
            PreparedArtifactRelease::Charged { .. }
        ));
    }

    #[test]
    fn prepared_package_artifact_clone_hashed_raw() {
        let (hashed, decoded) = decoded("proofs/clone.npcert");
        let path = hashed.path().clone();
        let mut artifacts =
            PreparedPackageArtifacts::new(PreparedArtifactObservationMode::Aggregate);
        artifacts.push_derived(
            hashed,
            decoded,
            PreparedArtifactRetentionPolicy::FastCandidateV1,
        );
        let before = artifacts.retention_observation().unwrap();
        let clone_before = artifacts.clone_hashed_raw(&path).expect("raw clone");
        assert_eq!(artifacts.retention_observation().unwrap(), before);

        artifacts.release_decoded(&path, PreparedArtifactReleaseReason::LiveResult);
        let clone_after = artifacts.clone_hashed_raw(&path).expect("raw clone");
        assert_eq!(clone_before.file_hash(), clone_after.file_hash());
        assert_eq!(clone_before.bytes(), clone_after.bytes());
        assert_eq!(clone_before.bytes().as_ptr(), clone_after.bytes().as_ptr());
        assert!(artifacts
            .clone_hashed_raw(&PackagePath::new("proofs/missing.npcert"))
            .is_none());
    }

    #[test]
    fn prepared_artifact_retention_observation() {
        let off = PreparedPackageArtifacts::new(PreparedArtifactObservationMode::Off);
        assert_eq!(off.retention_observation(), None);

        let (hashed, decoded) = decoded("proofs/observed.npcert");
        let charge = decoded.logical_retained_bytes_v1();
        let mut aggregate =
            PreparedPackageArtifacts::new(PreparedArtifactObservationMode::Aggregate);
        aggregate.push_derived(
            hashed,
            decoded,
            PreparedArtifactRetentionPolicy::FastCandidateV1,
        );
        let observed = aggregate.retention_observation().unwrap();
        assert_eq!(observed.admissions, 1);
        assert_eq!(observed.admitted_bytes, charge);
        assert_eq!(observed.current_entries, 1);
        assert_eq!(observed.peak_entries, 1);
        assert_eq!(observed.current_bytes, charge);
        assert_eq!(observed.peak_bytes, charge);
        assert_eq!(observed.derivation_candidate_current_bytes, 0);
        assert_eq!(observed.derivation_candidate_peak_bytes, charge);
        assert!(!observed.overflowed);
    }

    #[test]
    fn prepared_artifact_admission() {
        let mut exact =
            PreparedArtifactRetentionState::new(PreparedArtifactObservationMode::Aggregate);
        exact.current_entries = PREPARED_ARTIFACT_RETAINED_ENTRY_LIMIT_V1 - 1;
        exact.current_bytes = PREPARED_ARTIFACT_RETAINED_BYTE_LIMIT_V1 - 7;
        assert!(exact.admit(7));
        assert_eq!(
            exact.current_entries,
            PREPARED_ARTIFACT_RETAINED_ENTRY_LIMIT_V1
        );
        assert_eq!(
            exact.current_bytes,
            PREPARED_ARTIFACT_RETAINED_BYTE_LIMIT_V1
        );

        assert!(!exact.admit(1));
        let exact_observation = exact.observation().unwrap();
        assert_eq!(exact_observation.entry_limit_fallbacks, 1);
        assert_eq!(exact_observation.byte_limit_fallbacks, 0);

        let mut bytes =
            PreparedArtifactRetentionState::new(PreparedArtifactObservationMode::Aggregate);
        bytes.current_bytes = PREPARED_ARTIFACT_RETAINED_BYTE_LIMIT_V1;
        assert!(!bytes.admit(1));
        assert_eq!(bytes.observation().unwrap().byte_limit_fallbacks, 1);

        let mut saturated =
            PreparedArtifactRetentionState::new(PreparedArtifactObservationMode::Aggregate);
        assert!(!saturated.admit(u64::MAX));
        let saturated_observation = saturated.observation().unwrap();
        assert_eq!(saturated_observation.saturated_charge_fallbacks, 1);
        assert!(saturated_observation.overflowed);
    }

    #[test]
    fn prepared_artifact_release() {
        let (hashed, decoded) = decoded("proofs/release.npcert");
        let path = hashed.path().clone();
        let mut artifacts =
            PreparedPackageArtifacts::new(PreparedArtifactObservationMode::Aggregate);
        artifacts.push_derived(
            hashed,
            decoded,
            PreparedArtifactRetentionPolicy::FastCandidateV1,
        );
        let before = artifacts.retention_observation().unwrap();

        assert_eq!(
            artifacts.release_decoded(
                &PackagePath::new("proofs/missing.npcert"),
                PreparedArtifactReleaseReason::Unselected,
            ),
            PreparedArtifactRelease::NotFound
        );
        assert_eq!(artifacts.retention_observation().unwrap(), before);
        let release =
            artifacts.release_decoded(&path, PreparedArtifactReleaseReason::ProcessMemoHit);
        assert_eq!(
            release,
            PreparedArtifactRelease::Charged {
                released_bytes: before.current_bytes,
            }
        );
        assert_eq!(
            artifacts.release_decoded(&path, PreparedArtifactReleaseReason::LiveResult),
            PreparedArtifactRelease::AlreadyRaw
        );
        let after = artifacts.retention_observation().unwrap();
        assert_eq!(after.current_entries, 0);
        assert_eq!(after.current_bytes, 0);
        assert_eq!(after.charged_releases, 1);
        assert_eq!(after.released_bytes, before.current_bytes);
    }

    #[test]
    fn prepared_artifact_retention() {
        let mut artifacts =
            PreparedPackageArtifacts::new(PreparedArtifactObservationMode::Aggregate);
        let (first, first_decoded) = decoded("proofs/first.npcert");
        let first_path = first.path().clone();
        artifacts.push_derived(
            first,
            first_decoded,
            PreparedArtifactRetentionPolicy::FastCandidateV1,
        );

        // Force the next candidate to fall back without evicting the first.
        artifacts.retention.current_entries = PREPARED_ARTIFACT_RETAINED_ENTRY_LIMIT_V1;
        let (fallback, fallback_decoded) = decoded("proofs/fallback.npcert");
        let fallback_path = fallback.path().clone();
        artifacts.push_derived(
            fallback,
            fallback_decoded,
            PreparedArtifactRetentionPolicy::FastCandidateV1,
        );
        assert!(matches!(
            artifacts.get(&first_path),
            Some(PreparedPackageArtifactView::Prepared(snapshot))
                if snapshot.retained_decoded().is_some()
        ));
        assert!(matches!(
            artifacts.get(&fallback_path),
            Some(PreparedPackageArtifactView::Prepared(snapshot))
                if snapshot.retained_decoded().is_none()
        ));
        assert_eq!(
            artifacts.release_decoded(
                &fallback_path,
                PreparedArtifactReleaseReason::BlockedOrSkippedResult,
            ),
            PreparedArtifactRelease::RawFallbackTransition
        );

        // Restore the mandatory count to its real charged value before the
        // teardown transition; releasing capacity cannot revisit the fallback.
        artifacts.retention.current_entries = 1;
        artifacts.release_all_decoded(PreparedArtifactReleaseReason::OperationTeardown);
        assert_eq!(artifacts.retained_decoded_entries(), 0);
        assert_eq!(artifacts.retained_decoded_bytes(), 0);
        assert!(matches!(
            artifacts.get(&fallback_path),
            Some(PreparedPackageArtifactView::Hashed(_))
        ));
        let observation = artifacts.retention_observation().unwrap();
        assert_eq!(observation.entry_limit_fallbacks, 1);
        assert_eq!(observation.charged_releases, 1);
    }
}

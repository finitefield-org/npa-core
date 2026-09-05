use std::{
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use npa_kernel::{is_canonical_name_component, Decl, Reducibility, UniverseConstraintRelation};

/// SHA-256 digest used for canonical certificate objects.
pub type Hash = [u8; 32];

/// Index into a certificate name table.
pub type NameId = usize;

/// Index into a certificate level table.
pub type LevelId = usize;

/// Index into a certificate term table.
pub type TermId = usize;

/// Dotted module, declaration, or axiom name represented as canonical path components.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Name(
    /// Canonical name components.
    pub Vec<String>,
);

impl Name {
    /// Build a name from a dotted string, preserving empty path components for validation.
    pub fn from_dotted(name: impl AsRef<str>) -> Self {
        Self(name.as_ref().split('.').map(ToOwned::to_owned).collect())
    }

    /// Render the name as a dot-separated string.
    pub fn as_dotted(&self) -> String {
        self.0.join(".")
    }

    /// Return whether this name is canonical for trusted certificate payloads.
    ///
    /// The grammar is `Component ("." Component)*`, where `Component` is
    /// `[A-Za-z_][A-Za-z0-9_']*`.
    pub fn is_canonical(&self) -> bool {
        !self.0.is_empty()
            && self
                .0
                .iter()
                .all(|component| is_canonical_name_component(component))
    }
}

/// Canonical module name.
pub type ModuleName = Name;

/// Canonical axiom name.
pub type AxiomName = Name;

/// Input module made of already elaborated kernel declarations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoreModule {
    /// Module name stored in the certificate header.
    pub name: ModuleName,
    /// Kernel declarations to canonicalize into certificate declarations.
    pub declarations: Vec<Decl>,
}

/// Import trust mode used by certificate verification.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TrustMode {
    /// Resolve imports by module and export hash; certificate hash may be omitted.
    Normal,
    /// Require imports to be verified in-session by module, export hash, and certificate hash.
    HighTrust,
}

impl TrustMode {
    /// Stable policy profile name used by axiom-policy identity hashing.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Normal => "normal",
            Self::HighTrust => "high_trust",
        }
    }
}

/// Optional core feature profile committed by a certificate.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum CoreFeature {}

impl CoreFeature {
    /// Stable certificate feature name.
    pub const fn as_str(self) -> &'static str {
        match self {}
    }

    /// Parse a stable certificate feature name.
    pub fn from_name(_name: &str) -> Option<Self> {
        None
    }
}

/// Axiom admission policy enforced while verifying certificates and imports.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AxiomPolicy {
    /// Import trust mode for the verification run.
    pub mode: TrustMode,
    /// Exact set of allowed axioms. In normal mode an empty set permits every non-sorry axiom.
    /// In high-trust mode every axiom must be allowlisted.
    pub allowlisted_axioms: BTreeSet<AxiomName>,
    /// Reject declarations that depend on `sorry`.
    pub deny_sorry: bool,
    /// Core feature profiles supported by this checker run.
    pub supported_core_features: BTreeSet<CoreFeature>,
}

impl AxiomPolicy {
    /// Return the default normal-mode policy.
    pub fn normal() -> Self {
        Self {
            mode: TrustMode::Normal,
            allowlisted_axioms: BTreeSet::new(),
            deny_sorry: true,
            supported_core_features: BTreeSet::new(),
        }
    }

    /// Return the default high-trust policy.
    pub fn high_trust() -> Self {
        Self {
            mode: TrustMode::HighTrust,
            allowlisted_axioms: BTreeSet::new(),
            deny_sorry: true,
            supported_core_features: BTreeSet::new(),
        }
    }

    /// Return this policy with one additional supported core feature.
    pub fn with_core_feature(mut self, feature: CoreFeature) -> Self {
        self.supported_core_features.insert(feature);
        self
    }

    /// Return deterministic canonical bytes for this verification policy.
    ///
    /// These bytes are a verifier/candidate identity input only. They are not
    /// encoded into module certificates and do not participate in certificate hashes.
    pub fn canonical_bytes(&self) -> Vec<u8> {
        crate::hash::axiom_policy_canonical_bytes_impl(self)
    }

    /// Return the domain-separated SHA-256 identity hash for this policy.
    pub fn policy_hash(&self) -> Hash {
        crate::hash::axiom_policy_hash_impl(self)
    }
}

/// Lookup key for a verified import inside a verifier session.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ImportKey {
    /// Imported module name.
    pub module: Name,
    /// Export hash required by the import entry.
    pub export_hash: Hash,
    /// Certificate hash required by high-trust imports.
    pub certificate_hash: Option<Hash>,
}

/// In-memory registry of modules already verified during this trust session.
#[derive(Clone, Debug, Default)]
pub struct VerifierSession {
    index: Arc<SessionIndex>,
}

/// Operation-local observations for immutable certificate payload ownership.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CertificatePayloadObservation {
    /// Newly allocated immutable certificate payloads.
    pub payloads_frozen: u64,
    /// Logical retained bytes of newly allocated certificate payloads.
    pub payload_unique_bytes: u64,
    /// Explicit verifier-session snapshot clones.
    pub session_snapshot_clones: u64,
    /// Copy-on-write session-index copies that actually occurred.
    pub session_index_cow_copies: u64,
    /// Session entries copied by actual copy-on-write events.
    pub session_index_cow_entries: u64,
    /// Whether any observation arithmetic saturated.
    pub overflowed: bool,
}

impl CertificatePayloadObservation {
    fn add(field: &mut u64, value: u64, overflowed: &mut bool) {
        let (sum, overflow) = field.overflowing_add(value);
        *field = if overflow { u64::MAX } else { sum };
        *overflowed |= overflow;
    }

    pub(crate) fn observe_payload_frozen(&mut self, logical_bytes: u64) {
        Self::add(&mut self.payloads_frozen, 1, &mut self.overflowed);
        Self::add(
            &mut self.payload_unique_bytes,
            logical_bytes,
            &mut self.overflowed,
        );
    }

    fn observe_session_snapshot(&mut self) {
        Self::add(&mut self.session_snapshot_clones, 1, &mut self.overflowed);
    }

    fn observe_session_cow(&mut self, entries: usize) {
        Self::add(&mut self.session_index_cow_copies, 1, &mut self.overflowed);
        Self::add(
            &mut self.session_index_cow_entries,
            u64::try_from(entries).unwrap_or(u64::MAX),
            &mut self.overflowed,
        );
    }

    /// Merge another operation-local observation using saturating arithmetic.
    pub fn merge(&mut self, other: Self) {
        Self::add(
            &mut self.payloads_frozen,
            other.payloads_frozen,
            &mut self.overflowed,
        );
        Self::add(
            &mut self.payload_unique_bytes,
            other.payload_unique_bytes,
            &mut self.overflowed,
        );
        Self::add(
            &mut self.session_snapshot_clones,
            other.session_snapshot_clones,
            &mut self.overflowed,
        );
        Self::add(
            &mut self.session_index_cow_copies,
            other.session_index_cow_copies,
            &mut self.overflowed,
        );
        Self::add(
            &mut self.session_index_cow_entries,
            other.session_index_cow_entries,
            &mut self.overflowed,
        );
        self.overflowed |= other.overflowed;
    }
}

/// Operation-local observations for certificate term-DAG materialization.
///
/// These counters describe physical acceleration work only. They are not
/// certificate evidence and never participate in verifier lane selection.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CertificateTermMaterializationObservation {
    /// Successful handoffs of one materialized root expression.
    pub root_requests: u64,
    /// Selected certificate term nodes materialized into a stored `Arc`.
    pub unique_nodes_materialized: u64,
    /// Child edges belonging to successfully materialized compound nodes.
    pub selected_edges: u64,
    /// Stored child `Arc` values cloned into materialized parent nodes.
    pub reused_child_arcs: u64,
    /// Materialized roots handed to owned kernel declaration fields.
    pub owned_root_handoffs: u64,
    /// Root handoffs that cloned an owned leaf payload.
    pub leaf_root_clones: u64,
    /// Root handoffs that shallow-cloned a compound expression.
    pub compound_root_clones: u64,
    /// Reserved option-table slots initialized by ready materializers.
    pub materialization_slots: u64,
    /// Deterministic logical bytes committed by admitted materializers.
    pub materialization_charged_bytes: u64,
    /// Materialization attempts rejected by a logical or reservation capacity stop.
    pub materialization_capacity_stops: u64,
    /// Authoritative recursive conversions selected after a speculative stop.
    pub materialization_legacy_fallbacks: u64,
    /// Whether any counter arithmetic saturated.
    pub overflowed: bool,
}

impl CertificateTermMaterializationObservation {
    fn add(field: &mut u64, value: u64, overflowed: &mut bool) {
        if value == 0 {
            return;
        }
        let (sum, overflow) = field.overflowing_add(value);
        *field = if overflow { u64::MAX } else { sum };
        *overflowed |= overflow;
    }

    pub(crate) fn observe_root_request(&mut self, leaf: bool) {
        Self::add(&mut self.root_requests, 1, &mut self.overflowed);
        Self::add(&mut self.owned_root_handoffs, 1, &mut self.overflowed);
        if leaf {
            Self::add(&mut self.leaf_root_clones, 1, &mut self.overflowed);
        } else {
            Self::add(&mut self.compound_root_clones, 1, &mut self.overflowed);
        }
    }

    pub(crate) fn observe_unique_nodes(&mut self, value: u64) {
        Self::add(
            &mut self.unique_nodes_materialized,
            value,
            &mut self.overflowed,
        );
    }

    pub(crate) fn observe_selected_edges(&mut self, value: u64) {
        Self::add(&mut self.selected_edges, value, &mut self.overflowed);
    }

    pub(crate) fn observe_reused_child_arcs(&mut self, value: u64) {
        Self::add(&mut self.reused_child_arcs, value, &mut self.overflowed);
    }

    pub(crate) fn observe_slots(&mut self, value: u64) {
        Self::add(&mut self.materialization_slots, value, &mut self.overflowed);
    }

    pub(crate) fn observe_charged_bytes(&mut self, value: u64) {
        Self::add(
            &mut self.materialization_charged_bytes,
            value,
            &mut self.overflowed,
        );
    }

    pub(crate) fn observe_capacity_stop(&mut self) {
        Self::add(
            &mut self.materialization_capacity_stops,
            1,
            &mut self.overflowed,
        );
    }

    pub(crate) fn observe_legacy_fallback(&mut self) {
        Self::add(
            &mut self.materialization_legacy_fallbacks,
            1,
            &mut self.overflowed,
        );
    }

    pub(crate) fn observe_overflow(&mut self) {
        self.overflowed = true;
    }

    /// Merge another operation-local observation with saturating arithmetic.
    pub fn merge(&mut self, other: Self) {
        macro_rules! merge_field {
            ($field:ident) => {
                Self::add(&mut self.$field, other.$field, &mut self.overflowed)
            };
        }
        merge_field!(root_requests);
        merge_field!(unique_nodes_materialized);
        merge_field!(selected_edges);
        merge_field!(reused_child_arcs);
        merge_field!(owned_root_handoffs);
        merge_field!(leaf_root_clones);
        merge_field!(compound_root_clones);
        merge_field!(materialization_slots);
        merge_field!(materialization_charged_bytes);
        merge_field!(materialization_capacity_stops);
        merge_field!(materialization_legacy_fallbacks);
        self.overflowed |= other.overflowed;
    }
}

/// Additive operation-local observation sinks for certificate verification.
///
/// All fields are private so new diagnostic sinks can be added without
/// changing existing verifier signatures. An empty bundle has no semantic or
/// allocation effect.
pub struct CertificateVerificationObservationSinks<'a> {
    pub(crate) kernel: Option<&'a mut npa_kernel::KernelWorkCounters>,
    pub(crate) term: Option<&'a mut CertificateTermMaterializationObservation>,
    pub(crate) payload: Option<&'a mut CertificatePayloadObservation>,
}

impl<'a> CertificateVerificationObservationSinks<'a> {
    /// Create an empty observation bundle.
    pub fn new() -> Self {
        Self {
            kernel: None,
            term: None,
            payload: None,
        }
    }

    /// Install the deterministic kernel-work sink.
    pub fn with_kernel(mut self, sink: &'a mut npa_kernel::KernelWorkCounters) -> Self {
        self.kernel = Some(sink);
        self
    }

    /// Install the certificate term-materialization sink.
    pub fn with_term(mut self, sink: &'a mut CertificateTermMaterializationObservation) -> Self {
        self.term = Some(sink);
        self
    }

    /// Install the immutable certificate-payload ownership sink.
    pub fn with_payload(mut self, sink: &'a mut CertificatePayloadObservation) -> Self {
        self.payload = Some(sink);
        self
    }
}

impl Default for CertificateVerificationObservationSinks<'_> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone, Debug, Default)]
struct SessionIndex {
    checked: BTreeMap<ImportKey, SessionEntry>,
}

#[derive(Clone, Debug)]
struct SessionEntry {
    module: VerifiedModule,
    mode: TrustMode,
}

impl VerifierSession {
    /// Create an empty verifier session.
    pub fn new() -> Self {
        Self::default()
    }

    /// Create an immutable snapshot of the current verified-import index.
    ///
    /// This operation clones only an `Arc`. A later registration uses
    /// copy-on-write and cannot mutate the returned snapshot.
    pub fn snapshot(&self) -> Self {
        self.snapshot_observed(None)
    }

    /// Create a session snapshot and optionally record the handle clone.
    pub fn snapshot_observed(
        &self,
        observation: Option<&mut CertificatePayloadObservation>,
    ) -> Self {
        if let Some(observation) = observation {
            observation.observe_session_snapshot();
        }
        self.clone()
    }

    /// Register an already verified module as a normal-trust import for later verification.
    ///
    /// This is intended for callers that persist `VerifiedModule` values returned by
    /// `verify_module_cert` and need to verify a downstream certificate without re-reading the
    /// imported certificate bytes.
    pub fn register_verified_module(&mut self, module: VerifiedModule) {
        self.insert_verified(module, TrustMode::Normal);
    }

    /// Register an already verified module with the provided trust mode.
    ///
    /// This does not verify certificate bytes. It is intended for orchestrators
    /// that verified modules in independent workers and need to merge those
    /// `VerifiedModule` values back into one deterministic session.
    pub fn register_verified_module_with_trust(&mut self, module: VerifiedModule, mode: TrustMode) {
        self.register_verified_module_with_trust_observed(module, mode, None);
    }

    /// Register a verified module and optionally observe an actual session-index copy.
    pub fn register_verified_module_with_trust_observed(
        &mut self,
        module: VerifiedModule,
        mode: TrustMode,
        observation: Option<&mut CertificatePayloadObservation>,
    ) {
        self.insert_verified_observed(module, mode, observation);
    }

    pub(crate) fn insert_verified(&mut self, module: VerifiedModule, mode: TrustMode) {
        self.insert_verified_observed(module, mode, None);
    }

    fn insert_verified_observed(
        &mut self,
        module: VerifiedModule,
        mode: TrustMode,
        observation: Option<&mut CertificatePayloadObservation>,
    ) {
        let key = ImportKey {
            module: module.module().clone(),
            export_hash: module.export_hash(),
            certificate_hash: Some(module.certificate_hash()),
        };
        let entry = SessionEntry { module, mode };
        if Arc::get_mut(&mut self.index).is_none() {
            if let Some(observation) = observation {
                observation.observe_session_cow(self.index.checked.len());
            }
            self.index = Arc::new((*self.index).clone());
        }
        let checked = &mut Arc::get_mut(&mut self.index)
            .expect("session index must be unique after copy-on-write")
            .checked;
        match checked.get_mut(&key) {
            Some(existing) if existing.mode == TrustMode::HighTrust => {
                if mode == TrustMode::HighTrust {
                    *existing = entry;
                }
            }
            Some(existing) => *existing = entry,
            None => {
                checked.insert(key, entry);
            }
        }
    }

    pub(crate) fn find_import(
        &self,
        entry: &ImportEntry,
        mode: TrustMode,
    ) -> Result<&VerifiedModule> {
        let module_export_matches = self.index.checked.values().any(|checked| {
            checked.module.module() == &entry.module
                && checked.module.export_hash() == entry.export_hash
        });
        let high_trust_module_export_matches = self.index.checked.values().any(|checked| {
            checked.mode == TrustMode::HighTrust
                && checked.module.module() == &entry.module
                && checked.module.export_hash() == entry.export_hash
        });

        let found = self.index.checked.values().find(|checked| {
            (mode == TrustMode::Normal || checked.mode == TrustMode::HighTrust)
                && checked.module.module() == &entry.module
                && checked.module.export_hash() == entry.export_hash
                && match (mode, entry.certificate_hash) {
                    (TrustMode::Normal, None) => true,
                    (_, Some(hash)) => checked.module.certificate_hash() == hash,
                    (TrustMode::HighTrust, None) => false,
                }
        });

        if let Some(checked) = found {
            return Ok(&checked.module);
        }

        if mode == TrustMode::HighTrust && !high_trust_module_export_matches {
            return Err(CertError::ImportNotVerifiedInSession {
                module: entry.module.clone(),
            });
        }

        if entry.certificate_hash.is_some() && module_export_matches {
            return Err(CertError::ImportCertificateHashMismatch {
                module: entry.module.clone(),
            });
        }

        Err(CertError::ImportHashMismatch {
            module: entry.module.clone(),
        })
    }
}

#[derive(Clone)]
pub(crate) struct VerifiedModuleParts {
    /// Immutable syntactic certificate accepted by live verification.
    pub(crate) certificate: ModuleCert,
    /// Unique structural cost summary for this verified import closure.
    pub(crate) structural_closure: crate::structural::StructuralClosureSummary,
    pub(crate) logical_retained_bytes_v1: u64,
}

impl PartialEq for VerifiedModuleParts {
    fn eq(&self, other: &Self) -> bool {
        self.certificate == other.certificate && self.structural_closure == other.structural_closure
    }
}

impl Eq for VerifiedModuleParts {}

impl std::fmt::Debug for VerifiedModuleParts {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("VerifiedModule")
            .field("certificate_format", &self.certificate.header().format)
            .field("core_spec", &self.certificate.header().core_spec)
            .field("module", &self.certificate.header().module)
            .field("imports", &self.certificate.imports())
            .field("name_table", &self.certificate.name_table())
            .field("level_table", &self.certificate.level_table())
            .field("term_table", &self.certificate.term_table())
            .field("declarations", &self.certificate.declarations())
            .field("export_hash", &self.certificate.hashes().export_hash)
            .field(
                "certificate_hash",
                &self.certificate.hashes().certificate_hash,
            )
            .field("export_block", &self.certificate.export_block())
            .field("axiom_report", &self.certificate.axiom_report())
            .field("structural_closure", &self.structural_closure)
            .finish()
    }
}

/// Verified module payload that can be imported by later certificate verification.
#[derive(Clone)]
pub struct VerifiedModule {
    payload: Arc<VerifiedModuleParts>,
}

impl PartialEq for VerifiedModule {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.payload, &other.payload) || self.payload == other.payload
    }
}

impl Eq for VerifiedModule {}

impl std::fmt::Debug for VerifiedModule {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.payload.fmt(formatter)
    }
}

impl VerifiedModule {
    pub(crate) fn from_parts(parts: VerifiedModuleParts) -> Self {
        Self {
            payload: Arc::new(parts),
        }
    }

    /// Return the exact certificate format accepted from the input header.
    pub fn certificate_format(&self) -> &str {
        &self.payload.certificate.header().format
    }

    /// Return the exact core specification accepted from the input header.
    pub fn core_spec(&self) -> &str {
        &self.payload.certificate.header().core_spec
    }

    /// Return the verified module name.
    pub fn module(&self) -> &Name {
        &self.payload.certificate.header().module
    }

    /// Return the canonical import list from the verified certificate.
    pub fn imports(&self) -> &[ImportEntry] {
        self.payload.certificate.imports()
    }

    /// Return the canonical name table from the verified certificate.
    pub fn name_table(&self) -> &[Name] {
        self.payload.certificate.name_table()
    }

    /// Return the canonical level table from the verified certificate.
    pub fn level_table(&self) -> &[LevelNode] {
        self.payload.certificate.level_table()
    }

    /// Return the canonical term table from the verified certificate.
    pub fn term_table(&self) -> &[TermNode] {
        self.payload.certificate.term_table()
    }

    /// Return the verified declaration certificates.
    pub fn declarations(&self) -> &[DeclCert] {
        self.payload.certificate.declarations()
    }

    /// Return the module export hash used by downstream imports.
    pub fn export_hash(&self) -> Hash {
        self.payload.certificate.hashes().export_hash
    }

    /// Return the full certificate hash used by high-trust imports.
    pub fn certificate_hash(&self) -> Hash {
        self.payload.certificate.hashes().certificate_hash
    }

    /// Return the public export interface derived from declarations.
    pub fn export_block(&self) -> &[ExportEntry] {
        self.payload.certificate.export_block()
    }

    /// Return the axiom report recomputed during verification.
    pub fn axiom_report(&self) -> &AxiomReport {
        self.payload.certificate.axiom_report()
    }

    /// Return the target-independent v1 logical retained-size charge for the
    /// complete verified certificate and structural closure.
    pub fn logical_retained_bytes_v1(&self) -> u64 {
        self.payload.logical_retained_bytes_v1
    }

    pub(crate) fn structural_closure(&self) -> &crate::structural::StructuralClosureSummary {
        &self.payload.structural_closure
    }

    #[cfg(test)]
    pub(crate) fn mutate_certificate_parts_for_test(
        &mut self,
        mutate: impl FnOnce(&mut ModuleCertParts),
    ) {
        let payload = Arc::make_mut(&mut self.payload);
        payload.certificate.mutate_parts_for_test(mutate);
        payload.logical_retained_bytes_v1 =
            crate::logical_charge::verified_module_logical_retained_bytes_v1(
                payload.certificate.logical_retained_bytes_v1(),
                &payload.structural_closure,
            );
    }
}

/// Owned construction form for a syntactic module certificate.
///
/// Certificate decoders and builders use this type while assembling a value,
/// then hand it to [`ModuleCert::from_parts`].  Keeping the mutable construction
/// form separate from the runtime certificate lets the latter use immutable
/// shared ownership without exposing a mutable shared payload.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModuleCertParts {
    /// Certificate format, core spec, and module identity.
    pub header: CertHeader,
    /// Canonical import list.
    pub imports: Vec<ImportEntry>,
    /// Canonical table of all names referenced by the certificate.
    pub name_table: Vec<Name>,
    /// Canonical DAG table of levels.
    pub level_table: Vec<LevelNode>,
    /// Canonical DAG table of core terms.
    pub term_table: Vec<TermNode>,
    /// Declaration certificates in canonical dependency order.
    pub declarations: Vec<DeclCert>,
    /// Public export interface derived from declarations.
    pub export_block: ExportBlock,
    /// Direct and transitive axiom dependencies.
    pub axiom_report: AxiomReport,
    /// Export, axiom-report, and full-certificate hashes.
    pub hashes: ModuleHashes,
}

#[derive(Clone)]
struct ModuleCertPayload {
    parts: ModuleCertParts,
    logical_retained_bytes_v1: u64,
}

impl PartialEq for ModuleCertPayload {
    fn eq(&self, other: &Self) -> bool {
        self.parts == other.parts
    }
}

impl Eq for ModuleCertPayload {}

impl std::fmt::Debug for ModuleCertPayload {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("ModuleCert")
            .field("header", &self.parts.header)
            .field("imports", &self.parts.imports)
            .field("name_table", &self.parts.name_table)
            .field("level_table", &self.parts.level_table)
            .field("term_table", &self.parts.term_table)
            .field("declarations", &self.parts.declarations)
            .field("export_block", &self.parts.export_block)
            .field("axiom_report", &self.parts.axiom_report)
            .field("hashes", &self.parts.hashes)
            .finish()
    }
}

/// Syntactic module certificate as represented after canonical binary decoding.
#[derive(Clone)]
pub struct ModuleCert {
    payload: Arc<ModuleCertPayload>,
}

impl PartialEq for ModuleCert {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.payload, &other.payload) || self.payload == other.payload
    }
}

impl Eq for ModuleCert {}

impl std::fmt::Debug for ModuleCert {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.payload.fmt(formatter)
    }
}

impl ModuleCert {
    /// Freeze an owned construction payload into a certificate value.
    pub fn from_parts(parts: ModuleCertParts) -> Self {
        Self::from_parts_observed(parts, None)
    }

    /// Freeze an owned construction payload and optionally observe its logical allocation.
    pub fn from_parts_observed(
        parts: ModuleCertParts,
        observation: Option<&mut CertificatePayloadObservation>,
    ) -> Self {
        let logical_retained_bytes_v1 =
            crate::logical_charge::module_cert_logical_retained_bytes_v1(&parts);
        let certificate = Self {
            payload: Arc::new(ModuleCertPayload {
                parts,
                logical_retained_bytes_v1,
            }),
        };
        if let Some(observation) = observation {
            observation.observe_payload_frozen(logical_retained_bytes_v1);
        }
        certificate
    }

    /// Consume this certificate and return its owned construction payload.
    pub fn into_parts(self) -> ModuleCertParts {
        match Arc::try_unwrap(self.payload) {
            Ok(payload) => payload.parts,
            Err(payload) => payload.parts.clone(),
        }
    }

    pub(crate) fn parts(&self) -> &ModuleCertParts {
        &self.payload.parts
    }

    /// Mutate an owned construction payload in crate-local tests, then refreeze
    /// it so cached logical accounting is recomputed from the resulting value.
    #[cfg(test)]
    pub(crate) fn mutate_parts_for_test(&mut self, mutate: impl FnOnce(&mut ModuleCertParts)) {
        let mut parts = self.clone().into_parts();
        mutate(&mut parts);
        *self = Self::from_parts(parts);
    }

    /// Return the certificate header.
    pub fn header(&self) -> &CertHeader {
        &self.payload.parts.header
    }

    /// Return the canonical import list.
    pub fn imports(&self) -> &[ImportEntry] {
        &self.payload.parts.imports
    }

    /// Return the canonical name table.
    pub fn name_table(&self) -> &[Name] {
        &self.payload.parts.name_table
    }

    /// Return the canonical level table.
    pub fn level_table(&self) -> &[LevelNode] {
        &self.payload.parts.level_table
    }

    /// Return the canonical term table.
    pub fn term_table(&self) -> &[TermNode] {
        &self.payload.parts.term_table
    }

    /// Return the declaration certificates.
    pub fn declarations(&self) -> &[DeclCert] {
        &self.payload.parts.declarations
    }

    /// Return the public export block.
    pub fn export_block(&self) -> &[ExportEntry] {
        &self.payload.parts.export_block
    }

    /// Return the module axiom report.
    pub fn axiom_report(&self) -> &AxiomReport {
        &self.payload.parts.axiom_report
    }

    /// Return the committed certificate hashes.
    pub fn hashes(&self) -> &ModuleHashes {
        &self.payload.parts.hashes
    }

    /// Return the target-independent v1 logical retained-size charge.
    ///
    /// This value is cache-accounting metadata only; it is not encoded into a
    /// certificate and does not participate in equality or hashing.
    pub fn logical_retained_bytes_v1(&self) -> u64 {
        self.payload.logical_retained_bytes_v1
    }
}

/// Maximum number of per-declaration rows returned by retained-certificate
/// detailed measurement projection.
pub const RETAINED_CERTIFICATE_MEASUREMENT_DETAIL_LIMIT: usize = 2_048;

/// Detail requested from a retained decoded-certificate measurement summary.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CertificateMeasurementDetail {
    /// Return only aggregate declaration counts.
    Summary,
    /// Return aggregate counts and a bounded declaration prefix.
    Detailed,
}

/// One bounded declaration row projected from a retained decoded certificate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertificateDeclarationMeasurementSummary {
    /// Zero-based declaration index in certificate order.
    pub declaration_index: u64,
    /// Resolved dotted declaration name, or the stable index fallback.
    pub declaration: String,
    /// Number of distinct term-table nodes reachable from this declaration.
    ///
    /// This is `u64::MAX` when the operation-wide detailed-projection work budget was exhausted;
    /// [`CertificateMeasurementSummary::overflowed`] is also set in that case.
    pub term_nodes: u64,
}

/// Bounded measurement projection for a retained decoded certificate.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CertificateMeasurementSummary {
    /// Total declaration count, including rows omitted from detailed output.
    pub declaration_count: u64,
    /// Bounded declaration rows in certificate order.
    pub declarations: Vec<CertificateDeclarationMeasurementSummary>,
    /// Whether integer conversion saturated or the bounded detailed reachability projection was
    /// truncated.
    pub overflowed: bool,
}

/// Move-only capability for a decoded certificate retained by an artifact owner.
///
/// The capability intentionally exposes neither `Clone` nor a raw certificate
/// reference. This keeps prepared-artifact accounting aligned with physical
/// ownership while still allowing verification and bounded projections inside
/// this crate.
#[derive(Debug)]
pub struct RetainedDecodedModuleCert {
    module: ModuleCert,
}

impl RetainedDecodedModuleCert {
    /// Move a decoded certificate into an opaque retained capability.
    pub fn from_decoded(module: ModuleCert) -> Self {
        Self { module }
    }

    /// Return the decoded certificate header.
    pub fn header(&self) -> &CertHeader {
        self.module.header()
    }

    /// Return the committed decoded certificate hashes.
    pub fn hashes(&self) -> &ModuleHashes {
        self.module.hashes()
    }

    /// Return the decoded certificate axiom report.
    pub fn axiom_report(&self) -> &AxiomReport {
        self.module.axiom_report()
    }

    /// Return the target-independent logical retained-size charge.
    pub fn logical_retained_bytes_v1(&self) -> u64 {
        self.module.logical_retained_bytes_v1()
    }

    /// Project bounded measurement metadata without exposing certificate tables.
    pub fn measurement_summary(
        &self,
        detail: CertificateMeasurementDetail,
    ) -> CertificateMeasurementSummary {
        retained_certificate_measurement_summary(&self.module, detail)
    }

    /// Borrow the private decoded value for verifier implementations inside this crate.
    pub(crate) fn module(&self) -> &ModuleCert {
        &self.module
    }
}

fn retained_certificate_measurement_summary(
    certificate: &ModuleCert,
    detail: CertificateMeasurementDetail,
) -> CertificateMeasurementSummary {
    let (declaration_count, mut overflowed) = match u64::try_from(certificate.declarations().len())
    {
        Ok(count) => (count, false),
        Err(_) => (u64::MAX, true),
    };
    if detail == CertificateMeasurementDetail::Summary {
        return CertificateMeasurementSummary {
            declaration_count,
            declarations: Vec::new(),
            overflowed,
        };
    }
    let mut reachability = RetainedTermReachability::new(
        certificate.term_table(),
        crate::MAX_CERTIFICATE_EXPANDED_NODES,
    );
    let mut declarations = Vec::with_capacity(
        certificate
            .declarations()
            .len()
            .min(RETAINED_CERTIFICATE_MEASUREMENT_DETAIL_LIMIT),
    );
    for (index, declaration) in certificate
        .declarations()
        .iter()
        .take(RETAINED_CERTIFICATE_MEASUREMENT_DETAIL_LIMIT)
        .enumerate()
    {
        let term_nodes = match reachability.count(declaration) {
            Some(count) => count,
            None => {
                overflowed = true;
                u64::MAX
            }
        };
        declarations.push(CertificateDeclarationMeasurementSummary {
            declaration_index: u64::try_from(index).unwrap_or(u64::MAX),
            declaration: retained_declaration_name(certificate.name_table(), declaration, index),
            term_nodes,
        });
    }
    CertificateMeasurementSummary {
        declaration_count,
        declarations,
        overflowed,
    }
}

fn retained_declaration_name(
    names: &[Name],
    declaration: &DeclCert,
    declaration_index: usize,
) -> String {
    let name = match &declaration.decl {
        DeclPayload::Axiom { name, .. }
        | DeclPayload::AxiomConstrained { name, .. }
        | DeclPayload::Def { name, .. }
        | DeclPayload::DefConstrained { name, .. }
        | DeclPayload::Theorem { name, .. }
        | DeclPayload::TheoremConstrained { name, .. }
        | DeclPayload::Inductive { name, .. }
        | DeclPayload::InductiveConstrained { name, .. }
        | DeclPayload::MutualInductiveBlock { name, .. } => *name,
    };
    names
        .get(name)
        .map(Name::as_dotted)
        .unwrap_or_else(|| format!("declaration[{declaration_index}]"))
}

struct RetainedTermReachability<'a> {
    terms: &'a [TermNode],
    seen_generation: Vec<u32>,
    generation: u32,
    pending: Vec<TermId>,
    remaining_work: usize,
    root_set_counts: BTreeMap<Vec<TermId>, u64>,
}

impl<'a> RetainedTermReachability<'a> {
    fn new(terms: &'a [TermNode], work_budget: usize) -> Self {
        Self {
            terms,
            seen_generation: vec![0; terms.len()],
            generation: 0,
            pending: Vec::new(),
            remaining_work: work_budget,
            root_set_counts: BTreeMap::new(),
        }
    }

    fn count(&mut self, declaration: &DeclCert) -> Option<u64> {
        let roots = retained_declaration_term_roots(&declaration.decl);
        if let Some(count) = self.root_set_counts.get(&roots).copied() {
            return Some(count);
        }
        if self.remaining_work == 0 {
            return None;
        }
        self.generation = self.generation.checked_add(1)?;
        self.pending.clear();
        self.pending.extend(roots.iter().copied());
        let mut count = 0_u64;
        while let Some(term_id) = self.pending.pop() {
            self.remaining_work = self.remaining_work.checked_sub(1)?;
            let Some(generation) = self.seen_generation.get_mut(term_id) else {
                continue;
            };
            if *generation == self.generation {
                continue;
            }
            *generation = self.generation;
            count = count.checked_add(1)?;
            let Some(node) = self.terms.get(term_id) else {
                continue;
            };
            match node {
                TermNode::App(function, argument) => {
                    self.pending.push(*function);
                    self.pending.push(*argument);
                }
                TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => {
                    self.pending.push(*ty);
                    self.pending.push(*body);
                }
                TermNode::Sort(_) | TermNode::BVar(_) | TermNode::Const { .. } => {}
            }
        }
        self.root_set_counts.insert(roots, count);
        Some(count)
    }
}

fn retained_declaration_term_roots(declaration: &DeclPayload) -> Vec<TermId> {
    match declaration {
        DeclPayload::Axiom { ty, .. } | DeclPayload::AxiomConstrained { ty, .. } => vec![*ty],
        DeclPayload::Def { ty, value, .. } | DeclPayload::DefConstrained { ty, value, .. } => {
            vec![*ty, *value]
        }
        DeclPayload::Theorem { ty, proof, .. }
        | DeclPayload::TheoremConstrained { ty, proof, .. } => vec![*ty, *proof],
        DeclPayload::Inductive {
            params,
            indices,
            constructors,
            recursor,
            ..
        }
        | DeclPayload::InductiveConstrained {
            params,
            indices,
            constructors,
            recursor,
            ..
        } => params
            .iter()
            .chain(indices)
            .map(|binder| binder.ty)
            .chain(constructors.iter().map(|constructor| constructor.ty))
            .chain(recursor.iter().map(|recursor| recursor.ty))
            .collect(),
        DeclPayload::MutualInductiveBlock { inductives, .. } => inductives
            .iter()
            .flat_map(|inductive| {
                inductive
                    .params
                    .iter()
                    .chain(&inductive.indices)
                    .map(|binder| binder.ty)
                    .chain(
                        inductive
                            .constructors
                            .iter()
                            .map(|constructor| constructor.ty),
                    )
                    .chain(inductive.recursor.iter().map(|recursor| recursor.ty))
            })
            .collect(),
    }
}

#[cfg(test)]
mod retained_measurement_tests {
    use super::*;

    fn axiom(root: TermId) -> DeclCert {
        DeclCert {
            decl: DeclPayload::Axiom {
                name: 0,
                universe_params: Vec::new(),
                ty: root,
            },
            dependencies: Vec::new(),
            axiom_dependencies: Vec::new(),
            hashes: DeclHashes {
                decl_interface_hash: [0; 32],
                decl_certificate_hash: [0; 32],
            },
        }
    }

    fn shared_chain(length: usize) -> Vec<TermNode> {
        let mut terms = vec![TermNode::BVar(0)];
        for index in 1..length {
            terms.push(TermNode::App(index - 1, index - 1));
        }
        terms
    }

    #[test]
    fn retained_measurement_reuses_identical_root_sets_after_budget_is_spent() {
        let terms = shared_chain(100);
        let declaration = axiom(99);
        let mut reachability = RetainedTermReachability::new(&terms, 199);

        assert_eq!(reachability.count(&declaration), Some(100));
        assert_eq!(reachability.remaining_work, 0);
        assert_eq!(reachability.count(&declaration), Some(100));
    }

    #[test]
    fn retained_measurement_stops_before_repeating_unbounded_dag_work() {
        let terms = shared_chain(100);
        let declaration = axiom(99);
        let mut reachability = RetainedTermReachability::new(&terms, 64);

        assert_eq!(reachability.count(&declaration), None);
        assert_eq!(reachability.remaining_work, 0);
        assert_eq!(reachability.count(&declaration), None);
    }
}

/// Certificate header identifying the certificate and core specification versions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertHeader {
    /// Certificate format version string.
    pub format: String,
    /// Core specification version string.
    pub core_spec: String,
    /// Module name carried by the certificate.
    pub module: Name,
}

/// Import dependency declared by a module certificate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImportEntry {
    /// Imported module name.
    pub module: Name,
    /// Required export hash for the imported module.
    pub export_hash: Hash,
    /// Optional full certificate hash, mandatory in high-trust verification.
    pub certificate_hash: Option<Hash>,
}

/// Hashes committed by a module certificate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModuleHashes {
    /// Hash of the derived export block.
    pub export_hash: Hash,
    /// Hash of the derived axiom report.
    pub axiom_report_hash: Hash,
    /// Hash of the full certificate with this field zeroed.
    pub certificate_hash: Hash,
}

/// Canonical binary level node.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LevelNode {
    /// Universe level zero.
    Zero,
    /// Successor of a previous level table entry.
    Succ(LevelId),
    /// Maximum of two previous level table entries.
    Max(LevelId, LevelId),
    /// Impredicative maximum of two previous level table entries.
    IMax(LevelId, LevelId),
    /// Universe parameter stored in the name table.
    Param(NameId),
}

/// Canonical binary core term node.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TermNode {
    /// Sort at a level table entry.
    Sort(LevelId),
    /// De Bruijn bound variable.
    BVar(u32),
    /// Constant reference with universe instantiation.
    Const {
        /// Imported, local, or generated declaration reference.
        global_ref: GlobalRef,
        /// Universe level arguments.
        levels: Vec<LevelId>,
    },
    /// Application node.
    App(TermId, TermId),
    /// Lambda abstraction.
    Lam {
        /// Binder type.
        ty: TermId,
        /// Body under one additional binder.
        body: TermId,
    },
    /// Dependent function type.
    Pi {
        /// Binder type.
        ty: TermId,
        /// Body under one additional binder.
        body: TermId,
    },
}

/// Canonical declaration reference used by terms, dependencies, and axiom reports.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GlobalRef {
    /// Declaration provided by the checker builtin profile.
    Builtin {
        /// Name table index for the builtin declaration.
        name: NameId,
        /// Interface hash expected for the builtin declaration.
        decl_interface_hash: Hash,
    },
    /// Declaration exported by an imported module.
    Imported {
        /// Index into the import table.
        import_index: usize,
        /// Name table index for the imported declaration.
        name: NameId,
        /// Interface hash expected for the imported declaration.
        decl_interface_hash: Hash,
    },
    /// Local source declaration by declaration index.
    Local {
        /// Index into the local declaration table.
        decl_index: usize,
    },
    /// Local generated declaration such as an inductive constructor or recursor.
    LocalGenerated {
        /// Index of the source inductive declaration.
        decl_index: usize,
        /// Name table index for the generated declaration.
        name: NameId,
    },
}

impl Ord for GlobalRef {
    fn cmp(&self, other: &Self) -> Ordering {
        global_ref_order_key(self).cmp(&global_ref_order_key(other))
    }
}

impl PartialOrd for GlobalRef {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Certificate data for one source declaration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeclCert {
    /// Canonical declaration payload.
    pub decl: DeclPayload,
    /// Direct declaration dependencies with interface hashes.
    pub dependencies: Vec<DependencyEntry>,
    /// Transitive axiom dependencies for this declaration.
    pub axiom_dependencies: Vec<AxiomRef>,
    /// Declaration interface and certificate hashes.
    pub hashes: DeclHashes,
}

/// Canonical declaration payload.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DeclPayload {
    /// Assumed axiom declaration.
    Axiom {
        /// Name table index of the declaration.
        name: NameId,
        /// Universe parameter name ids.
        universe_params: Vec<NameId>,
        /// Type term id.
        ty: TermId,
    },
    /// Assumed axiom declaration with a non-empty universe constraint set.
    AxiomConstrained {
        /// Name table index of the declaration.
        name: NameId,
        /// Universe parameter name ids.
        universe_params: Vec<NameId>,
        /// Canonical universe constraints over the declaration parameters.
        universe_constraints: Vec<UniverseConstraintSpec>,
        /// Type term id.
        ty: TermId,
    },
    /// Definition declaration.
    Def {
        /// Name table index of the declaration.
        name: NameId,
        /// Universe parameter name ids.
        universe_params: Vec<NameId>,
        /// Type term id.
        ty: TermId,
        /// Value term id.
        value: TermId,
        /// Reducibility exported for downstream checking.
        reducibility: CertReducibility,
    },
    /// Definition declaration with a non-empty universe constraint set.
    DefConstrained {
        /// Name table index of the declaration.
        name: NameId,
        /// Universe parameter name ids.
        universe_params: Vec<NameId>,
        /// Canonical universe constraints over the declaration parameters.
        universe_constraints: Vec<UniverseConstraintSpec>,
        /// Type term id.
        ty: TermId,
        /// Value term id.
        value: TermId,
        /// Reducibility exported for downstream checking.
        reducibility: CertReducibility,
    },
    /// Opaque theorem declaration.
    Theorem {
        /// Name table index of the declaration.
        name: NameId,
        /// Universe parameter name ids.
        universe_params: Vec<NameId>,
        /// Proposition type term id.
        ty: TermId,
        /// Proof term id checked by the kernel but not exported as body.
        proof: TermId,
        /// Theorem opacity marker.
        opacity: Opacity,
    },
    /// Opaque theorem declaration with a non-empty universe constraint set.
    TheoremConstrained {
        /// Name table index of the declaration.
        name: NameId,
        /// Universe parameter name ids.
        universe_params: Vec<NameId>,
        /// Canonical universe constraints over the declaration parameters.
        universe_constraints: Vec<UniverseConstraintSpec>,
        /// Proposition type term id.
        ty: TermId,
        /// Proof term id checked by the kernel but not exported as body.
        proof: TermId,
        /// Theorem opacity marker.
        opacity: Opacity,
    },
    /// Inductive declaration with generated constructors and optional recursor.
    Inductive {
        /// Name table index of the inductive declaration.
        name: NameId,
        /// Universe parameter name ids.
        universe_params: Vec<NameId>,
        /// Parameter telescope.
        params: Vec<BinderType>,
        /// Index telescope.
        indices: Vec<BinderType>,
        /// Result sort level.
        sort: LevelId,
        /// Generated constructor specifications.
        constructors: Vec<ConstructorSpec>,
        /// Generated recursor specification when present.
        recursor: Option<RecursorSpec>,
    },
    /// Inductive declaration with generated artifacts and a non-empty universe constraint set.
    InductiveConstrained {
        /// Name table index of the inductive declaration.
        name: NameId,
        /// Universe parameter name ids.
        universe_params: Vec<NameId>,
        /// Canonical universe constraints over the declaration parameters.
        universe_constraints: Vec<UniverseConstraintSpec>,
        /// Parameter telescope.
        params: Vec<BinderType>,
        /// Index telescope.
        indices: Vec<BinderType>,
        /// Result sort level.
        sort: LevelId,
        /// Generated constructor specifications.
        constructors: Vec<ConstructorSpec>,
        /// Generated recursor specification when present.
        recursor: Option<RecursorSpec>,
    },
    /// Mutual inductive block with generated artifacts.
    MutualInductiveBlock {
        /// Name table index of the mutual block declaration.
        name: NameId,
        /// Shared universe parameter name ids.
        universe_params: Vec<NameId>,
        /// Canonical universe constraints over the block parameters.
        universe_constraints: Vec<UniverseConstraintSpec>,
        /// Inductives declared by this block in canonical block order.
        inductives: Vec<MutualInductiveSpec>,
    },
}

/// Canonical universe constraint in certificate-level ids.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct UniverseConstraintSpec {
    /// Left-hand side level table id.
    pub lhs: LevelId,
    /// Constraint relation.
    pub relation: UniverseConstraintRelation,
    /// Right-hand side level table id.
    pub rhs: LevelId,
}

/// Binder type in an inductive telescope.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BinderType {
    /// Type term for the binder.
    pub ty: TermId,
}

/// Generated inductive constructor certificate entry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstructorSpec {
    /// Constructor name table index.
    pub name: NameId,
    /// Constructor type term id.
    pub ty: TermId,
}

/// Generated inductive recursor certificate entry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecursorSpec {
    /// Recursor name table index.
    pub name: NameId,
    /// Universe parameter name ids.
    pub universe_params: Vec<NameId>,
    /// Recursor type term id.
    pub ty: TermId,
    /// Recursor rule-shape metadata.
    pub rules: RecursorRulesSpec,
}

/// Canonical recursor rule-shape metadata.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RecursorRulesSpec {
    /// Index of the first minor premise argument.
    pub minor_start: usize,
    /// Index of the major premise argument.
    pub major_index: usize,
}

/// One inductive family inside a mutual inductive block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MutualInductiveSpec {
    /// Inductive family name table index.
    pub name: NameId,
    /// Parameter telescope.
    pub params: Vec<BinderType>,
    /// Index telescope.
    pub indices: Vec<BinderType>,
    /// Result sort level.
    pub sort: LevelId,
    /// Generated constructor specifications.
    pub constructors: Vec<ConstructorSpec>,
    /// Generated recursor specification when present.
    pub recursor: Option<RecursorSpec>,
}

/// Reducibility exported by a definition certificate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CertReducibility {
    /// Definition body is transparent to downstream checking.
    Reducible,
    /// Definition body is opaque outside the local proof check.
    Opaque,
}

impl From<&Reducibility> for CertReducibility {
    fn from(value: &Reducibility) -> Self {
        match value {
            Reducibility::Reducible => Self::Reducible,
            Reducibility::Opaque => Self::Opaque,
        }
    }
}

impl From<CertReducibility> for Reducibility {
    fn from(value: CertReducibility) -> Self {
        match value {
            CertReducibility::Reducible => Self::Reducible,
            CertReducibility::Opaque => Self::Opaque,
        }
    }
}

/// Opacity marker for theorem exports.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Opacity {
    /// Theorem proofs are not exported as reducible bodies.
    Opaque,
}

/// Kind of declaration dependency carried by a certificate entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DependencyEntryKind {
    /// Dependency on a declaration's public interface only.
    Interface,
    /// Dependency on an earlier local opaque definition's checked implementation.
    LocalImplementation,
}

/// Stable reason for rejecting a local implementation dependency.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LocalImplementationDependencyErrorReason {
    /// The entry does not reference a plain local declaration.
    WrongReferenceKind,
    /// The local target is missing, current, or later than the dependent declaration.
    TargetNotEarlier,
    /// The target is not an opaque definition.
    TargetNotOpaque,
    /// The entry's interface hash does not match the target declaration.
    InterfaceHashMismatch,
    /// The entry's certificate hash does not match the target declaration.
    CertificateHashMismatch,
    /// A semantic local-transparency target has no implementation entry.
    MissingImplementationDependency,
    /// An implementation entry names a target outside the semantic closure.
    SurplusImplementationDependency,
}

impl LocalImplementationDependencyErrorReason {
    /// Return the stable snake-case reason used by diagnostics and fixtures.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::WrongReferenceKind => "wrong_reference_kind",
            Self::TargetNotEarlier => "target_not_earlier",
            Self::TargetNotOpaque => "target_not_opaque",
            Self::InterfaceHashMismatch => "interface_hash_mismatch",
            Self::CertificateHashMismatch => "certificate_hash_mismatch",
            Self::MissingImplementationDependency => "missing_implementation_dependency",
            Self::SurplusImplementationDependency => "surplus_implementation_dependency",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum DependencyEntryPayload {
    Interface {
        global_ref: GlobalRef,
        decl_interface_hash: Hash,
    },
    LocalImplementation {
        global_ref: GlobalRef,
        decl_interface_hash: Hash,
        decl_certificate_hash: Hash,
    },
}

/// Read-only dependency on a declaration interface or earlier local implementation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DependencyEntry {
    payload: DependencyEntryPayload,
}

impl DependencyEntry {
    /// Return the dependency variant.
    pub fn kind(&self) -> DependencyEntryKind {
        match self.payload {
            DependencyEntryPayload::Interface { .. } => DependencyEntryKind::Interface,
            DependencyEntryPayload::LocalImplementation { .. } => {
                DependencyEntryKind::LocalImplementation
            }
        }
    }

    /// Return the referenced declaration.
    pub fn global_ref(&self) -> &GlobalRef {
        match &self.payload {
            DependencyEntryPayload::Interface { global_ref, .. }
            | DependencyEntryPayload::LocalImplementation { global_ref, .. } => global_ref,
        }
    }

    /// Return the expected interface hash for the referenced declaration.
    pub fn decl_interface_hash(&self) -> Hash {
        match self.payload {
            DependencyEntryPayload::Interface {
                decl_interface_hash,
                ..
            }
            | DependencyEntryPayload::LocalImplementation {
                decl_interface_hash,
                ..
            } => decl_interface_hash,
        }
    }

    /// Return the expected declaration-certificate hash for an implementation dependency.
    pub fn decl_certificate_hash(&self) -> Option<Hash> {
        match self.payload {
            DependencyEntryPayload::Interface { .. } => None,
            DependencyEntryPayload::LocalImplementation {
                decl_certificate_hash,
                ..
            } => Some(decl_certificate_hash),
        }
    }

    pub(crate) fn from_decoded_interface(global_ref: GlobalRef, decl_interface_hash: Hash) -> Self {
        Self {
            payload: DependencyEntryPayload::Interface {
                global_ref,
                decl_interface_hash,
            },
        }
    }

    pub(crate) fn from_decoded_local_implementation(
        global_ref: GlobalRef,
        decl_interface_hash: Hash,
        decl_certificate_hash: Hash,
    ) -> Self {
        Self {
            payload: DependencyEntryPayload::LocalImplementation {
                global_ref,
                decl_interface_hash,
                decl_certificate_hash,
            },
        }
    }

    pub(crate) fn checked_interface(
        global_ref: GlobalRef,
        decl_interface_hash: Hash,
    ) -> Result<Self> {
        let embedded_hash = match &global_ref {
            GlobalRef::Builtin {
                decl_interface_hash,
                ..
            }
            | GlobalRef::Imported {
                decl_interface_hash,
                ..
            } => Some(*decl_interface_hash),
            GlobalRef::Local { .. } | GlobalRef::LocalGenerated { .. } => None,
        };
        if let Some(embedded_hash) = embedded_hash {
            if embedded_hash != decl_interface_hash {
                return Err(CertError::HashMismatch {
                    object: HashObject::DeclInterface,
                    expected: embedded_hash,
                    actual: decl_interface_hash,
                });
            }
        }
        Ok(Self {
            payload: DependencyEntryPayload::Interface {
                global_ref,
                decl_interface_hash,
            },
        })
    }

    pub(crate) fn checked_local_implementation(
        global_ref: GlobalRef,
        current_decl_index: usize,
        declarations: &[DeclCert],
    ) -> Result<Self> {
        let GlobalRef::Local { decl_index } = global_ref else {
            return Err(CertError::DecodeError);
        };
        if decl_index >= current_decl_index {
            return Err(CertError::DependencyCycle {
                name: Name::from_dotted(format!("local.{decl_index}")),
            });
        }
        let target = declarations.get(decl_index).ok_or(CertError::DecodeError)?;
        if !matches!(
            target.decl,
            DeclPayload::Def {
                reducibility: CertReducibility::Opaque,
                ..
            } | DeclPayload::DefConstrained {
                reducibility: CertReducibility::Opaque,
                ..
            }
        ) {
            return Err(CertError::DecodeError);
        }
        Ok(Self {
            payload: DependencyEntryPayload::LocalImplementation {
                global_ref: GlobalRef::Local { decl_index },
                decl_interface_hash: target.hashes.decl_interface_hash,
                decl_certificate_hash: target.hashes.decl_certificate_hash,
            },
        })
    }
}

impl Ord for DependencyEntry {
    fn cmp(&self, other: &Self) -> Ordering {
        dependency_entry_order_key(self).cmp(&dependency_entry_order_key(other))
    }
}

impl PartialOrd for DependencyEntry {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Canonical reference to an axiom dependency.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AxiomRef {
    /// Referenced axiom declaration.
    pub global_ref: GlobalRef,
    /// Axiom name table index.
    pub name: NameId,
    /// Expected interface hash for the axiom declaration.
    pub decl_interface_hash: Hash,
}

impl Ord for AxiomRef {
    fn cmp(&self, other: &Self) -> Ordering {
        axiom_ref_order_key(self).cmp(&axiom_ref_order_key(other))
    }
}

impl PartialOrd for AxiomRef {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

fn dependency_entry_order_key(entry: &DependencyEntry) -> Vec<u8> {
    let mut out = vec![match entry.kind() {
        DependencyEntryKind::Interface => 0x00,
        DependencyEntryKind::LocalImplementation => 0x01,
    }];
    out.extend(global_ref_order_key(entry.global_ref()));
    out.extend(entry.decl_interface_hash());
    if let Some(decl_certificate_hash) = entry.decl_certificate_hash() {
        out.extend(decl_certificate_hash);
    }
    out
}

fn axiom_ref_order_key(axiom: &AxiomRef) -> Vec<u8> {
    let mut out = global_ref_order_key(&axiom.global_ref);
    encode_order_uvar_to(&mut out, axiom.name as u64);
    out.extend(axiom.decl_interface_hash);
    out
}

fn global_ref_order_key(global_ref: &GlobalRef) -> Vec<u8> {
    let mut out = Vec::new();
    // Keep these tags aligned with binary::encode_global_ref_to so BTreeSet order is the same as
    // canonical GlobalRef byte order required by certificate serialization.
    match global_ref {
        GlobalRef::Builtin {
            name,
            decl_interface_hash,
        } => {
            out.push(0x03);
            encode_order_uvar_to(&mut out, *name as u64);
            out.extend(decl_interface_hash);
        }
        GlobalRef::Imported {
            import_index,
            name,
            decl_interface_hash,
        } => {
            out.push(0x00);
            encode_order_uvar_to(&mut out, *import_index as u64);
            encode_order_uvar_to(&mut out, *name as u64);
            out.extend(decl_interface_hash);
        }
        GlobalRef::Local { decl_index } => {
            out.push(0x01);
            encode_order_uvar_to(&mut out, *decl_index as u64);
        }
        GlobalRef::LocalGenerated { decl_index, name } => {
            out.push(0x02);
            encode_order_uvar_to(&mut out, *decl_index as u64);
            encode_order_uvar_to(&mut out, *name as u64);
        }
    }
    out
}

fn encode_order_uvar_to(out: &mut Vec<u8>, mut value: u64) {
    loop {
        let mut byte = (value & 0x7f) as u8;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        out.push(byte);
        if value == 0 {
            break;
        }
    }
}

/// Hash pair associated with a declaration certificate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeclHashes {
    /// Public interface hash for downstream imports and dependency checks.
    pub decl_interface_hash: Hash,
    /// Full declaration certificate hash.
    pub decl_certificate_hash: Hash,
}

/// Canonical public export entries for a verified module.
pub type ExportBlock = Vec<ExportEntry>;

/// One exported declaration interface.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExportEntry {
    /// Exported name table index.
    pub name: NameId,
    /// Kind of exported declaration.
    pub kind: ExportKind,
    /// Universe parameter name ids.
    pub universe_params: Vec<NameId>,
    /// Declaration universe constraints exported as part of the public signature.
    pub universe_constraints: Vec<UniverseConstraintSpec>,
    /// Exported type term id.
    pub ty: TermId,
    /// Optional exported body term id for transparent definitions.
    pub body: Option<TermId>,
    /// Structural hash of the exported type.
    pub type_hash: Hash,
    /// Structural hash of the exported body when present.
    pub body_hash: Option<Hash>,
    /// Reducibility metadata for definitions.
    pub reducibility: Option<CertReducibility>,
    /// Opacity metadata for theorems.
    pub opacity: Option<Opacity>,
    /// Interface hash of the exported declaration.
    pub decl_interface_hash: Hash,
    /// Transitive axiom dependencies for the export.
    pub axiom_dependencies: Vec<AxiomRef>,
}

/// Kind of an exported declaration interface.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExportKind {
    /// Axiom export.
    Axiom,
    /// Definition export.
    Def,
    /// Theorem export.
    Theorem,
    /// Inductive type export.
    Inductive,
    /// Generated constructor export.
    Constructor,
    /// Generated recursor export.
    Recursor,
}

/// Module-level axiom dependency report.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AxiomReport {
    /// Per-declaration axiom dependency reports.
    pub per_declaration: Vec<DeclAxiomReport>,
    /// Union of all transitive axiom dependencies in the module.
    pub module_axioms: Vec<AxiomRef>,
    /// Core feature profiles required by direct builtin primitive usage.
    pub core_features: Vec<CoreFeature>,
}

/// Axiom dependency report for a single declaration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeclAxiomReport {
    /// Declaration index in the certificate declaration table.
    pub decl_index: usize,
    /// Direct axioms referenced by this declaration.
    pub direct_axioms: Vec<AxiomRef>,
    /// Transitive axioms reachable from this declaration.
    pub transitive_axioms: Vec<AxiomRef>,
}

/// Hash role used in structured certificate hash mismatch errors.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HashObject {
    /// Level table hash.
    Level,
    /// Term table hash.
    Term,
    /// Declaration interface hash.
    DeclInterface,
    /// Declaration certificate hash.
    DeclCertificate,
    /// Export block hash.
    ExportBlock,
    /// Axiom report hash.
    AxiomReport,
    /// Full module certificate hash.
    ModuleCertificate,
}

/// Producer-side deterministic limit that rejected a candidate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProducerLimitKind {
    /// Candidate count exceeded `ProducerLimits.max_declarations`.
    MaxDeclarations,
    /// Core expression node count exceeded `ProducerLimits.max_expr_nodes`.
    MaxExprNodes,
    /// Universe level node count exceeded `ProducerLimits.max_level_nodes`.
    MaxLevelNodes,
    /// Dotted name component count exceeded `ProducerLimits.max_name_components`.
    MaxNameComponents,
    /// Reduction step budget could not be represented for kernel fuel.
    MaxReductionSteps,
    /// Conversion step budget could not be represented for kernel fuel.
    MaxConversionSteps,
}

/// Producer token hash field checked during prior-token validation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProducerTokenHashField {
    /// Token `pre_env_fingerprint` field.
    PreEnvFingerprint,
    /// Token `post_env_fingerprint` field.
    PostEnvFingerprint,
    /// Token `prior_chain_fingerprint` field.
    PriorChainFingerprint,
    /// Token dependency-selective fingerprint.
    DependencyFingerprint,
    /// Token `limit_profile_hash` field.
    LimitProfileHash,
    /// Token private declaration interface hash.
    DeclInterfaceHash,
    /// Token private declaration certificate hash.
    DeclCertificateHash,
}

/// Fixed structural certificate resource dimension.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum StructuralLimitKind {
    /// Encoded certificate byte length.
    CertificateBytes,
    /// Direct import count.
    Imports,
    /// Canonical name-table entry count.
    NameTableEntries,
    /// Canonical level-table node count.
    LevelTableNodes,
    /// Canonical term-table node count.
    TermTableNodes,
    /// Declaration count.
    Declarations,
    /// Public export count.
    Exports,
    /// Count of an encoded vector without a more specific limit.
    NestedVectorEntries,
    /// Combined term/level structural depth.
    StructuralDepth,
    /// Unfolded nodes requested by one semantic root.
    RootExpandedNodes,
    /// Sum of unfolded nodes requested by one certificate.
    CertificateExpandedNodes,
    /// Unique certificate identities in one resolved closure.
    ClosureModules,
    /// Sum of certificate expansion across one resolved closure.
    ClosureExpandedNodes,
}

impl StructuralLimitKind {
    /// Return the stable raw diagnostic name.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::CertificateBytes => "certificate_bytes",
            Self::Imports => "imports",
            Self::NameTableEntries => "name_table_entries",
            Self::LevelTableNodes => "level_table_nodes",
            Self::TermTableNodes => "term_table_nodes",
            Self::Declarations => "declarations",
            Self::Exports => "exports",
            Self::NestedVectorEntries => "nested_vector_entries",
            Self::StructuralDepth => "structural_depth",
            Self::RootExpandedNodes => "root_expanded_nodes",
            Self::CertificateExpandedNodes => "certificate_expanded_nodes",
            Self::ClosureModules => "closure_modules",
            Self::ClosureExpandedNodes => "closure_expanded_nodes",
        }
    }
}

/// Structured certificate construction, decoding, and verification error.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CertError {
    /// Generic malformed binary or invalid table reference.
    DecodeError,
    /// Certificate format or core spec version is unsupported.
    UnsupportedFormat {
        /// Found certificate format.
        format: String,
        /// Found core spec version.
        core_spec: String,
    },
    /// Certificate requires a core feature not supported by the active checker profile.
    UnsupportedCoreFeature {
        /// Unsupported feature name.
        feature: String,
    },
    /// Source or certificate declaration collides with a reserved core primitive name.
    ReservedCorePrimitive {
        /// Reserved primitive name.
        name: ModuleName,
    },
    /// Unknown canonical binary tag.
    UnsupportedEncoding {
        /// Unsupported byte tag.
        tag: u8,
    },
    /// Bytes decode but are not in canonical form.
    NonCanonicalEncoding {
        /// Object whose canonical encoding was violated.
        object: &'static str,
    },
    /// Old certificate/export format cannot represent non-empty public constraints.
    ConstrainedExportRequiresFormatUpgrade {
        /// Exported declaration requiring the newer public-interface layout.
        name: ModuleName,
    },
    /// A pre-v0.3 certificate format cannot encode a local implementation dependency.
    LocalImplementationDependencyRequiresFormatUpgrade,
    /// Recomputed hash did not match the committed value.
    HashMismatch {
        /// Hash role that mismatched.
        object: HashObject,
        /// Expected committed hash.
        expected: Hash,
        /// Recomputed actual hash.
        actual: Hash,
    },
    /// No verified import matched the required module/export hash.
    ImportHashMismatch {
        /// Imported module.
        module: ModuleName,
    },
    /// High-trust mode requires an import certificate hash.
    MissingImportCertificateHash {
        /// Imported module.
        module: ModuleName,
    },
    /// Import export hash matched but certificate hash differed.
    ImportCertificateHashMismatch {
        /// Imported module.
        module: ModuleName,
    },
    /// Candidate producer imports contain duplicate public environment keys.
    DuplicateImportEnvKey {
        /// Duplicated imported module.
        module: ModuleName,
        /// Duplicated imported export hash.
        export_hash: Hash,
    },
    /// High-trust mode could not find the import in the current verifier session.
    ImportNotVerifiedInSession {
        /// Imported module.
        module: ModuleName,
    },
    /// Duplicate canonical declaration or generated name.
    DuplicateName {
        /// Duplicated name.
        name: ModuleName,
    },
    /// Canonical emission selected a reference lane or identity that disagrees with its binding.
    ReferenceOriginMismatch {
        /// Declaration or generated declaration name.
        name: ModuleName,
        /// Stable expected reference-origin description.
        expected: &'static str,
        /// Stable emitted reference-origin description.
        actual: &'static str,
    },
    /// Referenced dependency could not be resolved.
    UnknownDependency {
        /// Unknown dependency name.
        name: ModuleName,
    },
    /// Source declarations contain a dependency cycle.
    DependencyCycle {
        /// Name participating in the cycle.
        name: ModuleName,
    },
    /// A v0.3 local implementation dependency failed semantic validation.
    InvalidLocalImplementationDependency {
        /// Dependent declaration index.
        decl_index: usize,
        /// Reference carried by, omitted from, or unexpectedly added to the dependency vector.
        global_ref: GlobalRef,
        /// Stable validation reason.
        reason: LocalImplementationDependencyErrorReason,
    },
    /// Certificate axiom report does not match recomputation.
    AxiomReportMismatch {
        /// Declaration whose report mismatched, or none for module-level mismatch.
        decl: Option<ModuleName>,
    },
    /// Axiom is not allowed by the active policy.
    ForbiddenAxiom {
        /// Forbidden axiom name.
        axiom: ModuleName,
    },
    /// `sorry` is denied by the active policy.
    SorryDenied {
        /// Denied axiom name.
        axiom: ModuleName,
    },
    /// Certificate input still contains an unresolved metavariable.
    UnresolvedMetavariable,
    /// De Bruijn index is out of scope.
    InvalidBVar {
        /// Invalid variable index.
        index: u32,
    },
    /// Inductive generated constructor or recursor payload is not derivable.
    InductiveGeneratedArtifactMismatch {
        /// Generated declaration name.
        name: ModuleName,
    },
    /// Inductive wrapper fields disagree with the checked inductive payload.
    InductiveWrapperMismatch {
        /// Inductive declaration name.
        name: ModuleName,
    },
    /// Producer candidate exceeded a deterministic schema limit.
    ProducerLimitExceeded {
        /// Limit that was exceeded.
        limit: ProducerLimitKind,
    },
    /// Opaque producer prior token committed a stale or forged hash.
    ProducerTokenHashMismatch {
        /// Prior-token index in `CandidateBatch.prior_current_decls`.
        token_index: usize,
        /// Token hash field that mismatched.
        field: ProducerTokenHashField,
        /// Recomputed expected hash.
        expected: Hash,
        /// Hash stored in the token.
        actual: Hash,
    },
    /// Opaque producer prior token was checked under looser limits than the current batch allows.
    ProducerTokenLimitTooLoose {
        /// Prior-token index in `CandidateBatch.prior_current_decls`.
        token_index: usize,
    },
    /// Certificate structure exceeded a fixed verifier admission limit.
    StructuralLimitExceeded {
        /// Resource dimension that was exceeded.
        kind: StructuralLimitKind,
        /// Fixed inclusive maximum.
        limit: usize,
        /// Exact count, or `limit + 1` for saturated expansion arithmetic.
        observed: usize,
    },
    /// Underlying Rust kernel rejected a declaration.
    Kernel(npa_kernel::Error),
}

/// Result type returned by certificate APIs.
pub type Result<T> = std::result::Result<T, CertError>;

impl From<npa_kernel::Error> for CertError {
    fn from(value: npa_kernel::Error) -> Self {
        Self::Kernel(value)
    }
}

#[cfg(test)]
mod shared_payload_tests {
    use super::*;

    fn certificate(module: &str) -> ModuleCert {
        ModuleCert::from_parts(ModuleCertParts {
            header: CertHeader {
                format: "NPA-CERT-0.4.0".to_owned(),
                core_spec: "NPA-Core-0.4.0".to_owned(),
                module: Name::from_dotted(module),
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
                export_hash: [1; 32],
                axiom_report_hash: [2; 32],
                certificate_hash: [3; 32],
            },
        })
    }

    fn verified(module: &str, seed: u8) -> VerifiedModule {
        let certificate = ModuleCert::from_parts(ModuleCertParts {
            header: CertHeader {
                format: "NPA-CERT-0.4.0".to_owned(),
                core_spec: "NPA-Core-0.4.0".to_owned(),
                module: Name::from_dotted(module),
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
                export_hash: [seed; 32],
                axiom_report_hash: [0; 32],
                certificate_hash: [seed.wrapping_add(1); 32],
            },
        });
        let structural_closure = crate::structural::StructuralClosureSummary::default();
        let logical_retained_bytes_v1 =
            crate::logical_charge::verified_module_logical_retained_bytes_v1(
                certificate.logical_retained_bytes_v1(),
                &structural_closure,
            );
        VerifiedModule::from_parts(VerifiedModuleParts {
            certificate,
            structural_closure,
            logical_retained_bytes_v1,
        })
    }

    #[test]
    fn verifier_session_snapshot_is_cow_isolated() {
        let first = verified("Shared.First", 1);
        let second = verified("Shared.Second", 2);
        let mut session = VerifierSession::new();
        session.register_verified_module(first);

        let mut observation = CertificatePayloadObservation::default();
        let snapshot = session.snapshot_observed(Some(&mut observation));
        session.register_verified_module_with_trust_observed(
            second.clone(),
            TrustMode::Normal,
            Some(&mut observation),
        );

        let import = ImportEntry {
            module: second.module().clone(),
            export_hash: second.export_hash(),
            certificate_hash: None,
        };
        assert!(session.find_import(&import, TrustMode::Normal).is_ok());
        assert!(matches!(
            snapshot.find_import(&import, TrustMode::Normal),
            Err(CertError::ImportHashMismatch { .. })
        ));
        assert_eq!(observation.session_snapshot_clones, 1);
        assert_eq!(observation.session_index_cow_copies, 1);
        assert_eq!(observation.session_index_cow_entries, 1);
        assert!(!observation.overflowed);
    }

    #[test]
    fn certificate_payload_observation_merge_saturates() {
        let mut observation = CertificatePayloadObservation {
            payloads_frozen: u64::MAX,
            ..CertificatePayloadObservation::default()
        };
        observation.merge(CertificatePayloadObservation {
            payloads_frozen: 1,
            session_index_cow_entries: 9,
            ..CertificatePayloadObservation::default()
        });
        assert_eq!(observation.payloads_frozen, u64::MAX);
        assert_eq!(observation.session_index_cow_entries, 9);
        assert!(observation.overflowed);
    }

    #[test]
    fn module_cert_clone_and_verified_module_clone_share_immutable_payloads() {
        let certificate = certificate("Shared.Certificate");
        assert_eq!(Arc::strong_count(&certificate.payload), 1);
        let certificate_clone = certificate.clone();
        assert_eq!(Arc::strong_count(&certificate.payload), 2);
        assert!(Arc::ptr_eq(
            &certificate.payload,
            &certificate_clone.payload
        ));

        let module = verified("Shared.Module", 7);
        assert_eq!(Arc::strong_count(&module.payload), 1);
        let module_clone = module.clone();
        assert_eq!(Arc::strong_count(&module.payload), 2);
        assert!(Arc::ptr_eq(&module.payload, &module_clone.payload));
    }

    #[test]
    fn module_cert_equality_and_verified_module_equality_ignore_cached_charge() {
        let certificate = certificate("Shared.Equality");
        let mut certificate_with_other_charge = certificate.clone();
        Arc::make_mut(&mut certificate_with_other_charge.payload).logical_retained_bytes_v1 =
            certificate.logical_retained_bytes_v1().saturating_add(1);
        assert_eq!(certificate, certificate_with_other_charge);

        let module = verified("Shared.Equality.Module", 9);
        let mut module_with_other_charge = module.clone();
        Arc::make_mut(&mut module_with_other_charge.payload).logical_retained_bytes_v1 = 1;
        assert_eq!(module, module_with_other_charge);
    }

    #[test]
    fn module_cert_debug_and_verified_module_debug_are_logical_and_deterministic() {
        let certificate_value = certificate("Shared.Debug.Certificate");
        let separately_frozen = certificate("Shared.Debug.Certificate");
        let certificate_debug = format!("{certificate_value:?}");
        assert_eq!(certificate_debug, format!("{separately_frozen:?}"));
        assert!(certificate_debug.starts_with("ModuleCert {"));
        assert!(certificate_debug.contains("header:"));

        let module = verified("Shared.Debug.Module", 13);
        let separately_verified = verified("Shared.Debug.Module", 13);
        let module_debug = format!("{module:?}");
        assert_eq!(module_debug, format!("{separately_verified:?}"));
        assert!(module_debug.starts_with("VerifiedModule {"));
        assert!(module_debug.contains("certificate_format:"));
        assert!(module_debug.contains("structural_closure:"));

        for forbidden in [
            "ModuleCertParts",
            "VerifiedModuleParts",
            "logical_retained_bytes_v1",
            "strong_count",
            "capacity",
            "0x",
        ] {
            assert!(!certificate_debug.contains(forbidden));
            assert!(!module_debug.contains(forbidden));
        }
    }

    #[test]
    fn test_only_verified_module_mutation_refreezes_all_cached_charges() {
        let mut module = verified("Shared.Mutation", 17);
        let untouched_clone = module.clone();
        let old_charge = module.logical_retained_bytes_v1();

        module.mutate_certificate_parts_for_test(|parts| {
            parts
                .name_table
                .push(Name::from_dotted("Shared.Mutation.AddedName"));
        });

        let expected_charge = crate::logical_charge::verified_module_logical_retained_bytes_v1(
            module.payload.certificate.logical_retained_bytes_v1(),
            &module.payload.structural_closure,
        );
        assert_eq!(module.logical_retained_bytes_v1(), expected_charge);
        assert!(module.logical_retained_bytes_v1() > old_charge);
        assert!(untouched_clone.name_table().is_empty());
        assert_eq!(untouched_clone.logical_retained_bytes_v1(), old_charge);
    }

    #[test]
    fn public_shared_payload_handles_are_send_sync() {
        fn assert_send_sync<T: Send + Sync>() {}

        assert_send_sync::<ModuleCert>();
        assert_send_sync::<VerifiedModule>();
        assert_send_sync::<VerifierSession>();
    }
}

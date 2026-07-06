use std::{
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet},
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
        self.insert_verified(module, mode);
    }

    pub(crate) fn insert_verified(&mut self, module: VerifiedModule, mode: TrustMode) {
        let key = ImportKey {
            module: module.module.clone(),
            export_hash: module.export_hash,
            certificate_hash: Some(module.certificate_hash),
        };
        let entry = SessionEntry { module, mode };
        match self.checked.get_mut(&key) {
            Some(existing) if existing.mode == TrustMode::HighTrust => {
                if mode == TrustMode::HighTrust {
                    *existing = entry;
                }
            }
            Some(existing) => *existing = entry,
            None => {
                self.checked.insert(key, entry);
            }
        }
    }

    pub(crate) fn find_import(
        &self,
        entry: &ImportEntry,
        mode: TrustMode,
    ) -> Result<&VerifiedModule> {
        let module_export_matches = self.checked.values().any(|checked| {
            checked.module.module == entry.module && checked.module.export_hash == entry.export_hash
        });
        let high_trust_module_export_matches = self.checked.values().any(|checked| {
            checked.mode == TrustMode::HighTrust
                && checked.module.module == entry.module
                && checked.module.export_hash == entry.export_hash
        });

        let found = self.checked.values().find(|checked| {
            (mode == TrustMode::Normal || checked.mode == TrustMode::HighTrust)
                && checked.module.module == entry.module
                && checked.module.export_hash == entry.export_hash
                && match (mode, entry.certificate_hash) {
                    (TrustMode::Normal, None) => true,
                    (_, Some(hash)) => checked.module.certificate_hash == hash,
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

/// Verified module payload that can be imported by later certificate verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedModule {
    /// Module name from the verified certificate.
    pub(crate) module: Name,
    /// Canonical import list from the verified certificate.
    pub(crate) imports: Vec<ImportEntry>,
    /// Canonical name table from the verified certificate.
    pub(crate) name_table: Vec<Name>,
    /// Canonical level table from the verified certificate.
    pub(crate) level_table: Vec<LevelNode>,
    /// Canonical term table from the verified certificate.
    pub(crate) term_table: Vec<TermNode>,
    /// Verified declaration certificates.
    pub(crate) declarations: Vec<DeclCert>,
    /// Module export hash used by downstream imports.
    pub(crate) export_hash: Hash,
    /// Full certificate hash used by high-trust imports.
    pub(crate) certificate_hash: Hash,
    /// Public export interface derived from declarations.
    pub(crate) export_block: ExportBlock,
    /// Axiom report recomputed during verification.
    pub(crate) axiom_report: AxiomReport,
}

impl VerifiedModule {
    /// Return the verified module name.
    pub fn module(&self) -> &Name {
        &self.module
    }

    /// Return the canonical import list from the verified certificate.
    pub fn imports(&self) -> &[ImportEntry] {
        &self.imports
    }

    /// Return the canonical name table from the verified certificate.
    pub fn name_table(&self) -> &[Name] {
        &self.name_table
    }

    /// Return the canonical level table from the verified certificate.
    pub fn level_table(&self) -> &[LevelNode] {
        &self.level_table
    }

    /// Return the canonical term table from the verified certificate.
    pub fn term_table(&self) -> &[TermNode] {
        &self.term_table
    }

    /// Return the verified declaration certificates.
    pub fn declarations(&self) -> &[DeclCert] {
        &self.declarations
    }

    /// Return the module export hash used by downstream imports.
    pub fn export_hash(&self) -> Hash {
        self.export_hash
    }

    /// Return the full certificate hash used by high-trust imports.
    pub fn certificate_hash(&self) -> Hash {
        self.certificate_hash
    }

    /// Return the public export interface derived from declarations.
    pub fn export_block(&self) -> &[ExportEntry] {
        &self.export_block
    }

    /// Return the axiom report recomputed during verification.
    pub fn axiom_report(&self) -> &AxiomReport {
        &self.axiom_report
    }
}

/// Syntactic module certificate as represented after canonical binary decoding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModuleCert {
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
    /// Let binding.
    Let {
        /// Bound value type.
        ty: TermId,
        /// Bound value.
        value: TermId,
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

/// Direct dependency on another declaration interface.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DependencyEntry {
    /// Referenced declaration.
    pub global_ref: GlobalRef,
    /// Expected interface hash for the referenced declaration.
    pub decl_interface_hash: Hash,
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
    let mut out = global_ref_order_key(&entry.global_ref);
    out.extend(entry.decl_interface_hash);
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
    /// Token `limit_profile_hash` field.
    LimitProfileHash,
    /// Token private declaration interface hash.
    DeclInterfaceHash,
    /// Token private declaration certificate hash.
    DeclCertificateHash,
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

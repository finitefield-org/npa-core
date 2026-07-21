//! Small reference-checker API boundary for Phase 8.
//!
//! This crate is intentionally independent from `npa-api`, `npa-tactic`,
//! `npa-frontend`, and the fast `npa-cert` verifier. The public entry point
//! accepts only canonical certificate bytes, an import store, and a checker
//! policy. It cannot receive `.npa` source, tactic scripts, AI traces, or a
//! theorem-search index.
//!
//! P8H-08 adds source-free axiom-report recomputation and deterministic axiom
//! policy gates.

#![deny(missing_docs)]
#![forbid(unsafe_code)]
// The public structured rejection intentionally retains complete bounded
// reference identities; keeping that API value-owned is more important than
// optimizing the cold error path's enum size.
#![allow(clippy::result_large_err)]

mod decode;

use std::collections::BTreeSet;
use std::sync::Arc;

use sha2::{Digest, Sha256};

/// Stable checker identifier emitted by the standalone raw-result contract.
pub const REFERENCE_CHECKER_ID: &str = "npa-checker-ref";

/// Crate version of the built-in reference checker.
pub const REFERENCE_CHECKER_VERSION: &str = env!("CARGO_PKG_VERSION");

/// Canonical certificate format tag accepted by the reference checker.
pub const REFERENCE_CERTIFICATE_FORMAT: &str = "NPA-CERT-0.2.0";

/// Canonical core spec tag accepted by the reference checker.
pub const REFERENCE_CORE_SPEC: &str = "NPA-Core-0.2.0";

/// Return the deterministic logical build identity used by the standalone checker.
///
/// This hashes the checker id, crate version, core specification, and certificate
/// format. It is not a hash of the compiled executable.
pub fn reference_checker_build_hash() -> ReferenceHash {
    let digest = Sha256::digest(
        format!(
            "{REFERENCE_CHECKER_ID}:{REFERENCE_CHECKER_VERSION}:{REFERENCE_CORE_SPEC}:{REFERENCE_CERTIFICATE_FORMAT}"
        )
        .as_bytes(),
    );
    let mut hash = [0_u8; 32];
    hash.copy_from_slice(&digest);
    hash
}

pub(crate) const REFERENCE_PREVIOUS_CERTIFICATE_FORMAT: &str = "NPA-CERT-0.1.2";
pub(crate) const REFERENCE_PREVIOUS_CORE_SPEC: &str = "NPA-Core-0.1.2";
pub(crate) const REFERENCE_LEGACY_CERTIFICATE_FORMAT: &str = "NPA-CERT-0.1";
pub(crate) const REFERENCE_LEGACY_CORE_SPEC: &str = "NPA-Core-0.1";
pub(crate) const REFERENCE_MODULE_EXPORT_DOMAIN: &[u8] = b"NPA-MODULE-EXPORT-0.2.0";
pub(crate) const REFERENCE_MODULE_CERT_DOMAIN: &[u8] = b"NPA-MODULE-CERT-0.2.0";
pub(crate) const REFERENCE_PREVIOUS_MODULE_EXPORT_DOMAIN: &[u8] = b"NPA-MODULE-EXPORT-0.1.2";
pub(crate) const REFERENCE_PREVIOUS_MODULE_CERT_DOMAIN: &[u8] = b"NPA-MODULE-CERT-0.1.2";
pub(crate) const REFERENCE_LEGACY_MODULE_EXPORT_DOMAIN: &[u8] = b"NPA-MODULE-EXPORT-0.1";
pub(crate) const REFERENCE_LEGACY_MODULE_CERT_DOMAIN: &[u8] = b"NPA-MODULE-CERT-0.1";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ReferenceCertificateFormatVersion {
    Current,
    Previous,
    Legacy,
}

impl ReferenceCertificateFormatVersion {
    pub(crate) fn encodes_export_universe_constraints(self) -> bool {
        self != Self::Legacy
    }
}

/// A SHA-256 hash stored in canonical certificate-facing artifacts.
pub type ReferenceHash = [u8; 32];

/// Certificate-only import environment supplied to the reference checker.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ReferenceImportStore {
    entries: Vec<ReferenceImportEntry>,
}

impl ReferenceImportStore {
    /// Builds an import store from explicit source-free certificate bytes.
    ///
    /// The certificates are decoded and hash-verified, but they are not marked
    /// as high-trust checked modules because semantic checking is a later
    /// milestone. No filesystem, package discovery, network, or remote import
    /// lookup is performed.
    pub fn from_source_free_certificates<I, B>(certificates: I) -> Result<Self, ReferenceCheckError>
    where
        I: IntoIterator<Item = B>,
        B: AsRef<[u8]>,
    {
        let entries = certificates
            .into_iter()
            .map(|bytes| decode::import_entry_from_source_free_certificate_impl(bytes.as_ref()))
            .collect::<Result<Vec<_>, _>>()?;
        Self::from_entries(entries)
    }

    /// Builds an import store from modules already checked by this checker.
    pub fn from_checked_modules<I>(modules: I) -> Result<Self, ReferenceCheckError>
    where
        I: IntoIterator<Item = ReferenceCheckedModule>,
    {
        let entries = modules
            .into_iter()
            .map(ReferenceCheckedModule::into_import_entry)
            .collect();
        Self::from_entries(entries)
    }

    /// Returns the available import module interfaces.
    pub fn entries(&self) -> &[ReferenceImportEntry] {
        &self.entries
    }

    /// Returns the number of available import module interfaces.
    pub const fn len(&self) -> usize {
        self.entries.len()
    }

    /// Returns true when the store has no import module interfaces.
    pub const fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    fn from_entries(entries: Vec<ReferenceImportEntry>) -> Result<Self, ReferenceCheckError> {
        validate_unique_import_store_entries(&entries)?;
        Ok(Self { entries })
    }
}

/// One import entry available to a reference checker run.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReferenceImportEntry {
    module: ReferenceModuleName,
    export_hash: ReferenceHash,
    axiom_report_hash: ReferenceHash,
    certificate_hash: ReferenceHash,
    public_environment: Arc<ReferencePublicEnvironment>,
    checked_by_reference_checker: bool,
}

impl ReferenceImportEntry {
    pub(crate) fn new(
        module: ReferenceModuleName,
        export_hash: ReferenceHash,
        axiom_report_hash: ReferenceHash,
        certificate_hash: ReferenceHash,
        public_environment: Arc<ReferencePublicEnvironment>,
        checked_by_reference_checker: bool,
    ) -> Self {
        Self {
            module,
            export_hash,
            axiom_report_hash,
            certificate_hash,
            public_environment,
            checked_by_reference_checker,
        }
    }

    /// Returns the imported module name.
    pub const fn module(&self) -> &ReferenceModuleName {
        &self.module
    }

    /// Returns the imported module export hash.
    pub const fn export_hash(&self) -> &ReferenceHash {
        &self.export_hash
    }

    /// Returns the imported module axiom-report hash.
    pub const fn axiom_report_hash(&self) -> &ReferenceHash {
        &self.axiom_report_hash
    }

    /// Returns the imported module certificate hash.
    pub const fn certificate_hash(&self) -> &ReferenceHash {
        &self.certificate_hash
    }

    /// Returns the imported module public environment.
    pub fn public_environment(&self) -> &ReferencePublicEnvironment {
        &self.public_environment
    }

    /// Returns true when this module was checked by this reference checker.
    pub const fn checked_by_reference_checker(&self) -> bool {
        self.checked_by_reference_checker
    }
}

fn validate_unique_import_store_entries(
    entries: &[ReferenceImportEntry],
) -> Result<(), ReferenceCheckError> {
    let mut seen = BTreeSet::new();
    for (index, entry) in entries.iter().enumerate() {
        if !seen.insert((entry.module.clone(), entry.export_hash)) {
            return Err(ReferenceCheckError::import_resolution(
                ReferenceCertificateSection::ImportStore,
                index,
                ReferenceCheckReason::DuplicateImport,
            ));
        }
    }
    Ok(())
}

/// Public environment exported by one imported certificate.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ReferencePublicEnvironment {
    imports: Vec<ReferencePublicImport>,
    exports: Vec<ReferencePublicExport>,
    module_axioms: Vec<ReferenceAxiomDependency>,
    core_features: Vec<ReferenceCoreFeature>,
    inductive_groups: Vec<ReferencePublicInductiveGroup>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ReferencePublicImport {
    module: ReferenceModuleName,
    export_hash: ReferenceHash,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReferencePublicRecursorLayout {
    pub(crate) name: ReferenceModuleName,
    pub(crate) minor_start: usize,
    pub(crate) major_index: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReferencePublicInductiveLayout {
    pub(crate) name: ReferenceModuleName,
    pub(crate) param_count: usize,
    pub(crate) index_count: usize,
    pub(crate) constructors: Vec<ReferenceModuleName>,
    pub(crate) recursor: Option<ReferencePublicRecursorLayout>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReferencePublicInductiveGroup {
    pub(crate) decl_interface_hash: ReferenceHash,
    pub(crate) families: Vec<ReferencePublicInductiveLayout>,
}

impl ReferencePublicEnvironment {
    pub(crate) fn new(
        imports: Vec<(ReferenceModuleName, ReferenceHash)>,
        exports: Vec<ReferencePublicExport>,
        module_axioms: Vec<ReferenceAxiomDependency>,
        core_features: Vec<ReferenceCoreFeature>,
        inductive_groups: Vec<ReferencePublicInductiveGroup>,
    ) -> Self {
        Self {
            imports: imports
                .into_iter()
                .map(|(module, export_hash)| ReferencePublicImport {
                    module,
                    export_hash,
                })
                .collect(),
            exports,
            module_axioms,
            core_features,
            inductive_groups,
        }
    }

    /// Returns public exports in canonical export-block order.
    pub fn exports(&self) -> &[ReferencePublicExport] {
        &self.exports
    }

    /// Returns module-level transitive axiom dependencies.
    pub fn module_axioms(&self) -> &[ReferenceAxiomDependency] {
        &self.module_axioms
    }

    /// Returns core features required by this public environment.
    pub fn core_features(&self) -> &[ReferenceCoreFeature] {
        &self.core_features
    }
}

/// One declaration exported by an imported module.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReferencePublicExport {
    /// Exported declaration name.
    pub name: ReferenceModuleName,
    /// Exported declaration kind.
    pub kind: ReferenceExportKind,
    /// Declaration interface hash.
    pub decl_interface_hash: ReferenceHash,
    /// Transitive axiom dependencies committed by this export.
    pub axiom_dependencies: Vec<ReferenceAxiomDependency>,
    universe_params: Vec<ReferenceModuleName>,
    universe_constraints: Vec<decode::ReferenceUniverseConstraint>,
    ty: ReferenceCoreExpr,
    body: Option<ReferenceCoreExpr>,
}

/// Kind of an imported public export.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReferenceExportKind {
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

/// Axiom dependency carried by an imported public environment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReferenceAxiomDependency {
    /// Axiom declaration name.
    pub name: ReferenceModuleName,
    /// Axiom declaration interface hash.
    pub decl_interface_hash: ReferenceHash,
}

/// Import environment resolved for the module currently being checked.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ReferenceImportEnvironment {
    imports: Vec<ReferenceResolvedImport>,
}

impl ReferenceImportEnvironment {
    pub(crate) fn new(imports: Vec<ReferenceResolvedImport>) -> Self {
        Self { imports }
    }

    /// Returns resolved imports in the current certificate's canonical order.
    pub fn imports(&self) -> &[ReferenceResolvedImport] {
        &self.imports
    }

    /// Returns the number of resolved imports.
    pub const fn len(&self) -> usize {
        self.imports.len()
    }

    /// Returns true when no imports were resolved.
    pub const fn is_empty(&self) -> bool {
        self.imports.is_empty()
    }
}

/// One resolved import attached to the current module environment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReferenceResolvedImport {
    /// Imported module name.
    pub module: ReferenceModuleName,
    /// Resolved export hash.
    pub export_hash: ReferenceHash,
    /// Resolved certificate hash.
    pub certificate_hash: ReferenceHash,
    /// Imported public environment.
    pub public_environment: Arc<ReferencePublicEnvironment>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum ReferenceCoreLevel {
    Zero,
    Succ(Arc<ReferenceCoreLevel>),
    Max(Arc<ReferenceCoreLevel>, Arc<ReferenceCoreLevel>),
    IMax(Arc<ReferenceCoreLevel>, Arc<ReferenceCoreLevel>),
    Param(ReferenceModuleName),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ReferenceCoreExpr {
    Sort(ReferenceCoreLevel),
    BVar(u32),
    Const {
        global_ref: ReferenceCoreGlobalRef,
        levels: Vec<ReferenceCoreLevel>,
    },
    App(Arc<ReferenceCoreExpr>, Arc<ReferenceCoreExpr>),
    Lam {
        ty: Arc<ReferenceCoreExpr>,
        body: Arc<ReferenceCoreExpr>,
    },
    Pi {
        ty: Arc<ReferenceCoreExpr>,
        body: Arc<ReferenceCoreExpr>,
    },
    Let {
        ty: Arc<ReferenceCoreExpr>,
        value: Arc<ReferenceCoreExpr>,
        body: Arc<ReferenceCoreExpr>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ReferenceCoreGlobalRef {
    Builtin {
        name: ReferenceModuleName,
        decl_interface_hash: ReferenceHash,
    },
    Imported {
        import_index: usize,
        name: ReferenceModuleName,
        decl_interface_hash: ReferenceHash,
    },
    Local {
        decl_index: usize,
    },
    LocalGenerated {
        decl_index: usize,
        name: ReferenceModuleName,
    },
}

/// Canonical dotted module or declaration name.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ReferenceModuleName {
    components: Vec<String>,
}

impl ReferenceModuleName {
    /// Builds a module name from already separated canonical components.
    pub fn new(components: Vec<String>) -> Result<Self, ReferenceNameError> {
        if components.is_empty() {
            return Err(ReferenceNameError::Empty);
        }
        if let Some(index) = components.iter().position(|component| component.is_empty()) {
            return Err(ReferenceNameError::EmptyComponent { index });
        }
        if let Some(index) = components
            .iter()
            .position(|component| component.contains('.'))
        {
            return Err(ReferenceNameError::ComponentContainsDot { index });
        }
        if let Some(index) = components
            .iter()
            .position(|component| !reference_name_component_is_canonical(component))
        {
            return Err(ReferenceNameError::InvalidComponent { index });
        }
        Ok(Self { components })
    }

    /// Builds a module name from a dotted string.
    pub fn from_dotted(value: &str) -> Result<Self, ReferenceNameError> {
        Self::new(value.split('.').map(str::to_owned).collect())
    }

    /// Returns the canonical name components.
    pub fn components(&self) -> &[String] {
        &self.components
    }

    /// Returns the dotted display form.
    pub fn dotted(&self) -> String {
        self.components.join(".")
    }
}

fn reference_name_component_is_canonical(component: &str) -> bool {
    let mut bytes = component.bytes();
    let Some(first) = bytes.next() else {
        return false;
    };
    (first.is_ascii_alphabetic() || first == b'_')
        && bytes.all(|byte| byte.is_ascii_alphanumeric() || byte == b'_' || byte == b'\'')
}

/// Structured error for invalid reference-checker names.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReferenceNameError {
    /// The name has no components.
    Empty,
    /// One component is empty.
    EmptyComponent {
        /// Component index that was empty.
        index: usize,
    },
    /// One component contains a dotted separator.
    ComponentContainsDot {
        /// Component index that contained a dot.
        index: usize,
    },
    /// One component violates the canonical name component grammar.
    InvalidComponent {
        /// Component index that violated the grammar.
        index: usize,
    },
}

/// Decoded source-free canonical certificate.
///
/// This is intentionally an opaque boundary object for P8H-02. The reference
/// checker can inspect canonical certificate structure without accepting source
/// files, tactic scripts, AI sidecars, or semantic import resolution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReferenceDecodedCertificate {
    header: ReferenceCertificateHeader,
    imports_len: usize,
    name_table_len: usize,
    level_table_len: usize,
    term_table_len: usize,
    declarations_len: usize,
    export_block_len: usize,
    hashes: ReferenceModuleHashes,
}

impl ReferenceDecodedCertificate {
    /// Returns the decoded certificate header.
    pub const fn header(&self) -> &ReferenceCertificateHeader {
        &self.header
    }

    /// Returns the number of decoded import entries.
    pub const fn imports_len(&self) -> usize {
        self.imports_len
    }

    /// Returns the number of decoded canonical name table entries.
    pub const fn name_table_len(&self) -> usize {
        self.name_table_len
    }

    /// Returns the number of decoded canonical level table entries.
    pub const fn level_table_len(&self) -> usize {
        self.level_table_len
    }

    /// Returns the number of decoded canonical term table entries.
    pub const fn term_table_len(&self) -> usize {
        self.term_table_len
    }

    /// Returns the number of decoded declaration certificates.
    pub const fn declarations_len(&self) -> usize {
        self.declarations_len
    }

    /// Returns the number of decoded export entries.
    pub const fn export_block_len(&self) -> usize {
        self.export_block_len
    }

    /// Returns the stored canonical module hashes.
    pub const fn hashes(&self) -> &ReferenceModuleHashes {
        &self.hashes
    }
}

/// Decoded source-free certificate header.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReferenceCertificateHeader {
    /// Canonical certificate format tag.
    pub format: String,
    /// Core specification version tag.
    pub core_spec: String,
    /// Certified module name.
    pub module: ReferenceModuleName,
}

/// Canonical hashes stored at the end of a decoded module certificate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ReferenceModuleHashes {
    /// Stored export hash.
    pub export_hash: ReferenceHash,
    /// Stored axiom report hash.
    pub axiom_report_hash: ReferenceHash,
    /// Stored certificate hash.
    pub certificate_hash: ReferenceHash,
}

/// Hash role used in structured reference checker hash mismatch errors.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReferenceHashObject {
    /// Declaration interface hash.
    DeclInterface,
    /// Declaration interface hash whose payload contains dependency material.
    DeclInterfaceDependencyMaterial,
    /// Declaration certificate hash.
    DeclCertificate,
    /// Declaration certificate hash whose payload contains dependency material.
    DeclCertificateDependencyMaterial,
    /// Export block hash.
    ExportBlock,
    /// Axiom report hash.
    AxiomReport,
    /// Full module certificate hash.
    ModuleCertificate,
}

impl ReferenceDecodedCertificate {
    /// Builds a decoded certificate summary from decoder-owned data.
    pub(crate) const fn new(
        header: ReferenceCertificateHeader,
        counts: ReferenceDecodedCertificateCounts,
        hashes: ReferenceModuleHashes,
    ) -> Self {
        Self {
            header,
            imports_len: counts.imports_len,
            name_table_len: counts.name_table_len,
            level_table_len: counts.level_table_len,
            term_table_len: counts.term_table_len,
            declarations_len: counts.declarations_len,
            export_block_len: counts.export_block_len,
            hashes,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ReferenceDecodedCertificateCounts {
    imports_len: usize,
    name_table_len: usize,
    level_table_len: usize,
    term_table_len: usize,
    declarations_len: usize,
    export_block_len: usize,
}

/// Deterministic policy input for the reference checker.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReferenceCheckerPolicy {
    /// Trust mode for import and axiom policy gates.
    pub trust_mode: ReferenceTrustMode,
    /// Exact axiom names allowed by the policy.
    pub allowed_axioms: Vec<String>,
    /// Reject declarations that depend on a synthetic `sorry` axiom.
    pub deny_sorry: bool,
    /// Reject every custom axiom not explicitly allowed by the policy.
    pub deny_custom_axioms: bool,
    /// Core feature profiles supported by this checker run.
    pub supported_core_features: Vec<ReferenceCoreFeature>,
}

impl Default for ReferenceCheckerPolicy {
    fn default() -> Self {
        Self {
            trust_mode: ReferenceTrustMode::Normal,
            allowed_axioms: Vec::new(),
            deny_sorry: true,
            deny_custom_axioms: false,
            supported_core_features: Vec::new(),
        }
    }
}

/// Reference checker trust mode.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReferenceTrustMode {
    /// Normal certificate check mode.
    Normal,
    /// High-trust mode requiring certificate hashes for imports.
    HighTrust,
}

/// Optional core feature profile committed by a certificate.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ReferenceCoreFeature {}

impl ReferenceCoreFeature {
    /// Stable certificate feature name.
    pub const fn as_str(self) -> &'static str {
        match self {}
    }

    /// Parse a stable certificate feature name.
    pub fn from_name(_name: &str) -> Option<Self> {
        None
    }
}

/// Result returned by [`check_certificate`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReferenceCheckResult {
    /// The certificate was accepted by the reference checker.
    Checked(ReferenceCheckedModule),
    /// The certificate was rejected with a deterministic structured error.
    Rejected(ReferenceCheckError),
}

impl ReferenceCheckResult {
    /// Returns true when the certificate was checked and accepted.
    pub const fn is_checked(&self) -> bool {
        matches!(self, Self::Checked(_))
    }

    /// Returns the rejection error, if any.
    pub const fn error(&self) -> Option<&ReferenceCheckError> {
        match self {
            Self::Checked(_) => None,
            Self::Rejected(error) => Some(error),
        }
    }
}

/// Accepted module summary produced by the reference checker.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReferenceCheckedModule {
    module: ReferenceModuleName,
    export_hash: ReferenceHash,
    axiom_report_hash: ReferenceHash,
    certificate_hash: ReferenceHash,
    declaration_count: usize,
    public_environment: Arc<ReferencePublicEnvironment>,
    checked_by_reference_checker: bool,
}

impl ReferenceCheckedModule {
    pub(crate) fn new(
        module: ReferenceModuleName,
        export_hash: ReferenceHash,
        axiom_report_hash: ReferenceHash,
        certificate_hash: ReferenceHash,
        declaration_count: usize,
        public_environment: Arc<ReferencePublicEnvironment>,
    ) -> Self {
        Self {
            module,
            export_hash,
            axiom_report_hash,
            certificate_hash,
            declaration_count,
            public_environment,
            checked_by_reference_checker: true,
        }
    }

    #[cfg(test)]
    pub(crate) fn from_import_entry(entry: ReferenceImportEntry) -> Self {
        Self::new(
            entry.module,
            entry.export_hash,
            entry.axiom_report_hash,
            entry.certificate_hash,
            0,
            entry.public_environment,
        )
    }

    fn into_import_entry(self) -> ReferenceImportEntry {
        ReferenceImportEntry::new(
            self.module,
            self.export_hash,
            self.axiom_report_hash,
            self.certificate_hash,
            self.public_environment,
            self.checked_by_reference_checker,
        )
    }

    /// Returns the checked module name.
    pub const fn module(&self) -> &ReferenceModuleName {
        &self.module
    }

    /// Returns the checked module export hash.
    pub const fn export_hash(&self) -> &ReferenceHash {
        &self.export_hash
    }

    /// Returns the checked module axiom-report hash.
    pub const fn axiom_report_hash(&self) -> &ReferenceHash {
        &self.axiom_report_hash
    }

    /// Returns the checked module certificate hash.
    pub const fn certificate_hash(&self) -> &ReferenceHash {
        &self.certificate_hash
    }

    /// Returns the number of declarations decoded and checked for this module.
    pub const fn declaration_count(&self) -> usize {
        self.declaration_count
    }

    /// Returns the checked module public environment.
    pub fn public_environment(&self) -> &ReferencePublicEnvironment {
        &self.public_environment
    }
}

/// Complete identity of an import resolved by the reference checker.
#[non_exhaustive]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReferenceCheckResolvedImportIdentity {
    /// Index in the import list that owns this identity.
    pub import_index: usize,
    /// Canonical imported module name.
    pub module: ReferenceModuleName,
    /// Resolved imported module export hash.
    pub export_hash: ReferenceHash,
}

impl ReferenceCheckResolvedImportIdentity {
    /// Creates a complete resolved-import diagnostic identity.
    pub fn new(
        import_index: usize,
        module: ReferenceModuleName,
        export_hash: ReferenceHash,
    ) -> Self {
        Self {
            import_index,
            module,
            export_hash,
        }
    }
}

/// Import target requested by an unresolved declaration reference.
#[non_exhaustive]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReferenceCheckImportTarget {
    /// The target import index was outside the available import environment.
    Unresolved {
        /// Requested import index.
        import_index: usize,
    },
    /// The target import entry was available and has a complete identity.
    Resolved(ReferenceCheckResolvedImportIdentity),
}

/// Typed identity of a declaration/global reference rejected by the checker.
#[non_exhaustive]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReferenceCheckReference {
    /// Builtin declaration reference.
    Builtin {
        /// Exact canonical declaration name.
        declaration: ReferenceModuleName,
        /// Requested declaration-interface hash.
        decl_interface_hash: ReferenceHash,
    },
    /// Imported declaration reference.
    Imported {
        /// Resolved current import whose public environment contained this
        /// reference, or `None` for the current certificate's import list.
        owner_import: Option<ReferenceCheckResolvedImportIdentity>,
        /// Requested target import.
        import: ReferenceCheckImportTarget,
        /// Exact canonical declaration name.
        declaration: ReferenceModuleName,
        /// Requested declaration-interface hash.
        decl_interface_hash: ReferenceHash,
    },
    /// Local declaration reference.
    Local {
        /// Resolved current import whose public environment illegally contained
        /// this local reference, or `None` for the current certificate.
        owner_import: Option<ReferenceCheckResolvedImportIdentity>,
        /// Requested declaration-table index.
        declaration_index: usize,
        /// Exact canonical declaration name when available.
        declaration: Option<ReferenceModuleName>,
    },
    /// Generated local constructor or recursor reference.
    LocalGenerated {
        /// Resolved current import whose public environment illegally contained
        /// this generated local reference, or `None` for the current certificate.
        owner_import: Option<ReferenceCheckResolvedImportIdentity>,
        /// Parent declaration-table index.
        declaration_index: usize,
        /// Exact canonical generated declaration name.
        declaration: ReferenceModuleName,
    },
}

/// Deterministic structured reference checker error.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReferenceCheckError {
    /// Stable machine-readable error kind.
    pub kind: ReferenceCheckErrorKind,
    /// Certificate section where the error was detected.
    pub section: ReferenceCertificateSection,
    /// Byte offset where the error was detected.
    pub offset: usize,
    /// Optional stable reason code for this error.
    pub reason: Option<ReferenceCheckReason>,
    /// Typed declaration/import identity for declaration/global
    /// [`ReferenceCheckReason::UnknownReference`] failures.
    ///
    /// The two existing universe-parameter failures that reuse that reason do
    /// not carry declaration reference context.
    pub reference: Option<ReferenceCheckReference>,
}

impl ReferenceCheckError {
    pub(crate) fn empty() -> Self {
        Self {
            kind: ReferenceCheckErrorKind::EmptyCertificate,
            section: ReferenceCertificateSection::HeaderFormat,
            offset: 0,
            reason: None,
            reference: None,
        }
    }

    pub(crate) fn malformed(
        section: ReferenceCertificateSection,
        offset: usize,
        reason: ReferenceCheckReason,
    ) -> Self {
        Self {
            kind: ReferenceCheckErrorKind::MalformedCertificate,
            section,
            offset,
            reason: Some(reason),
            reference: None,
        }
    }

    pub(crate) fn unsupported(offset: usize) -> Self {
        Self {
            kind: ReferenceCheckErrorKind::UnsupportedSkeleton,
            section: ReferenceCertificateSection::FullCertificate,
            offset,
            reason: Some(ReferenceCheckReason::ReferenceCheckerBodyUnimplemented),
            reference: None,
        }
    }

    pub(crate) fn unsupported_core_feature(offset: usize) -> Self {
        Self {
            kind: ReferenceCheckErrorKind::UnsupportedCoreFeature,
            section: ReferenceCertificateSection::AxiomReport,
            offset,
            reason: Some(ReferenceCheckReason::UnsupportedCoreFeature),
            reference: None,
        }
    }

    pub(crate) fn import_resolution(
        section: ReferenceCertificateSection,
        offset: usize,
        reason: ReferenceCheckReason,
    ) -> Self {
        Self {
            kind: ReferenceCheckErrorKind::ImportResolution,
            section,
            offset,
            reason: Some(reason),
            reference: None,
        }
    }

    pub(crate) fn type_check(
        section: ReferenceCertificateSection,
        offset: usize,
        reason: ReferenceCheckReason,
    ) -> Self {
        Self {
            kind: ReferenceCheckErrorKind::TypeCheck,
            section,
            offset,
            reason: Some(reason),
            reference: None,
        }
    }

    pub(crate) fn unknown_reference(
        section: ReferenceCertificateSection,
        offset: usize,
        reference: ReferenceCheckReference,
    ) -> Self {
        Self {
            kind: ReferenceCheckErrorKind::TypeCheck,
            section,
            offset,
            reason: Some(ReferenceCheckReason::UnknownReference),
            reference: Some(reference),
        }
    }
}

/// Stable top-level reference checker error kind.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReferenceCheckErrorKind {
    /// The certificate byte input was empty.
    EmptyCertificate,
    /// The certificate was malformed or not canonical.
    MalformedCertificate,
    /// A stored hash did not match the reference checker recomputation.
    HashMismatch,
    /// Import store resolution or import policy failed.
    ImportResolution,
    /// A stored axiom report did not match reference-checker recomputation.
    AxiomReportMismatch,
    /// Axiom admission policy rejected the certificate.
    AxiomPolicy,
    /// Minimal source-free type checking failed.
    TypeCheck,
    /// The checked certificate used a declaration form reserved for a later milestone.
    UnsupportedSkeleton,
    /// The checked certificate requires an unsupported core feature profile.
    UnsupportedCoreFeature,
}

/// Stable certificate section label for diagnostics.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReferenceCertificateSection {
    /// Certificate format string in the header.
    HeaderFormat,
    /// Core spec string in the header.
    HeaderCoreSpec,
    /// Module name in the header.
    HeaderModule,
    /// Import table.
    Imports,
    /// Canonical name table.
    NameTable,
    /// Canonical universe level table.
    LevelTable,
    /// Canonical term table.
    TermTable,
    /// Declaration certificate table.
    Declarations,
    /// Export block.
    ExportBlock,
    /// Axiom report block.
    AxiomReport,
    /// Final stored module hashes.
    Hashes,
    /// Explicit import store supplied to the checker.
    ImportStore,
    /// Whole certificate after section-level decoding.
    FullCertificate,
}

/// Stable reason code for deterministic reference checker rejections.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReferenceCheckReason {
    /// A varint ended after the input ended.
    UnexpectedEof,
    /// A varint used a noncanonical byte sequence.
    NonCanonicalUvar,
    /// A varint exceeded the supported `u64` range.
    UvarOverflow,
    /// A length did not fit into the host `usize`.
    LengthOverflow,
    /// A tag byte is not defined by the canonical certificate format.
    UnknownTag {
        /// Unknown tag byte.
        tag: u8,
    },
    /// A string was not valid UTF-8.
    InvalidUtf8,
    /// The certificate format tag was not a supported NPA certificate format.
    FormatMismatch,
    /// The core spec tag was not a supported NPA core spec.
    CoreSpecMismatch,
    /// The old public export layout would drop non-empty universe constraints.
    ConstrainedExportRequiresFormatUpgrade,
    /// The module name had no components.
    EmptyModuleName,
    /// A module name component was empty.
    EmptyModuleNameComponent,
    /// A canonical name component contained a dotted separator.
    DottedNameComponent,
    /// A canonical name component violated `[A-Za-z_][A-Za-z0-9_']*`.
    InvalidNameComponent,
    /// An index referenced a missing table entry.
    DanglingReference,
    /// A canonical table was not in strict canonical order.
    NonCanonicalOrder,
    /// A canonical name table contained duplicate entries.
    DuplicateName,
    /// A canonical declaration table contained duplicate names.
    DuplicateDeclarationName,
    /// A declaration collided with a reserved core primitive name.
    ReservedCorePrimitive,
    /// An import binding appeared more than once.
    DuplicateImport,
    /// The requested high-trust import closure contains a cycle.
    ImportCycle,
    /// A level table entry was not normalized.
    NonNormalizedLevel,
    /// A term table entry was not normalized.
    NonNormalizedTerm,
    /// A canonical table entry was not reachable from certificate roots.
    UnusedTableEntry,
    /// Extra bytes remained after the canonical certificate sections.
    TrailingBytes,
    /// A source or replay path was supplied where only certificate inputs are allowed.
    SourceInputForbidden,
    /// A requested import module was not available in the explicit import store.
    MissingImport,
    /// An import module was present, but not with the requested export hash.
    ImportExportHashMismatch,
    /// High-trust mode required a certificate hash in the import entry.
    MissingImportCertificateHash,
    /// A present import certificate hash did not match the resolved import.
    ImportCertificateHashMismatch,
    /// High-trust mode rejected an import that was not checked by this checker.
    UncheckedImport,
    /// A constant or global reference was unavailable in the checked environment.
    UnknownReference,
    /// A known core feature is not enabled by the active checker policy.
    UnsupportedCoreFeature,
    /// A constant was applied to the wrong number of universe levels.
    BadUniverseArity,
    /// A universe-parameter telescope contained the same name more than once.
    DuplicateUniverseParam,
    /// A declaration universe context repeats the same constraint.
    DuplicateUniverseConstraint,
    /// A certificate still contains an elaboration-only universe metavariable.
    UnresolvedMetavariable,
    /// A universe constraint is outside the supported checker fragment.
    UnsupportedUniverseConstraint,
    /// A universe constraint context has no natural-number solution.
    UnsatisfiableUniverseConstraints,
    /// A universe constraint obligation is not entailed by the ambient context.
    UniverseConstraintViolation,
    /// A de Bruijn index was not in local scope.
    InvalidBVar,
    /// A term was expected to have a sort type.
    ExpectedSort,
    /// A term was expected to have a function type.
    ExpectedFunction,
    /// An inferred type was not definitionally equal to the expected type.
    TypeMismatch,
    /// Type checking or conversion exhausted its deterministic resource bound.
    ResourceLimit,
    /// An inductive constructor did not return its declared family.
    BadConstructorResult,
    /// A non-parameter constructor field lives above the inductive family's sort.
    ConstructorUniverseBoundViolation,
    /// A constructor contains a recursive occurrence outside the MVP strictly positive shape.
    NonPositiveOccurrence,
    /// A generated recursor rule index did not match the declaration shape.
    BadRecursorRule,
    /// A generated recursor parameter binder did not match the inductive parameter telescope.
    BadRecursorParam,
    /// A generated recursor motive binder did not target the inductive family.
    BadRecursorMotive,
    /// A generated recursor major premise did not target the inductive family.
    BadRecursorMajor,
    /// A generated recursor minor premise did not match its constructor.
    BadRecursorMinor,
    /// A generated recursor result did not apply the motive to the major premise.
    BadRecursorResult,
    /// A generated recursor type was not the canonical type for its declaration.
    BadRecursorType,
    /// A stored hash did not match the reference checker recomputation.
    HashMismatch {
        /// Hash role that mismatched.
        object: ReferenceHashObject,
    },
    /// A stored axiom report did not match reference-checker recomputation.
    AxiomReportMismatch,
    /// `deny_sorry` rejected a synthetic `sorry` axiom dependency.
    SorryDenied,
    /// A custom axiom was not in the exact allowlist or standard exception set.
    ForbiddenAxiom,
    /// The P8H-03 decoder/hash verifier intentionally has no semantic checker body.
    ReferenceCheckerBodyUnimplemented,
}

impl ReferenceCheckError {
    pub(crate) fn axiom_report(section: ReferenceCertificateSection, offset: usize) -> Self {
        Self {
            kind: ReferenceCheckErrorKind::AxiomReportMismatch,
            section,
            offset,
            reason: Some(ReferenceCheckReason::AxiomReportMismatch),
            reference: None,
        }
    }

    pub(crate) fn axiom_policy(
        section: ReferenceCertificateSection,
        offset: usize,
        reason: ReferenceCheckReason,
    ) -> Self {
        Self {
            kind: ReferenceCheckErrorKind::AxiomPolicy,
            section,
            offset,
            reason: Some(reason),
            reference: None,
        }
    }

    pub(crate) fn hash_mismatch(
        section: ReferenceCertificateSection,
        offset: usize,
        object: ReferenceHashObject,
    ) -> Self {
        Self {
            kind: ReferenceCheckErrorKind::HashMismatch,
            section,
            offset,
            reason: Some(ReferenceCheckReason::HashMismatch { object }),
            reference: None,
        }
    }
}

/// Decode a source-free canonical certificate without semantic checking.
///
/// This function accepts only `.npcert` canonical binary bytes. It validates
/// section order, known tags, canonical table shape, dangling references, and
/// table reachability. It does not resolve imports, type check declarations, or
/// validate any AI sidecar.
pub fn decode_certificate(
    cert_bytes: &[u8],
) -> Result<ReferenceDecodedCertificate, ReferenceCheckError> {
    decode::decode_certificate_impl(cert_bytes)
}

/// Decode and verify all stored canonical hashes without semantic checking.
///
/// This recomputes term, declaration, export, axiom-report, and full
/// certificate hashes inside the reference checker boundary. It does not resolve
/// imports, type check declarations, or validate any AI sidecar.
pub fn verify_certificate_hashes(
    cert_bytes: &[u8],
) -> Result<ReferenceDecodedCertificate, ReferenceCheckError> {
    decode::verify_certificate_hashes_impl(cert_bytes)
}

/// Decode, hash-verify, and resolve the current certificate's imports.
///
/// Import resolution only consults the explicit [`ReferenceImportStore`]. It
/// does not access the filesystem, discover package paths, use the network, or
/// fetch remote imports.
pub fn build_import_environment(
    cert_bytes: &[u8],
    import_store: &ReferenceImportStore,
    policy: &ReferenceCheckerPolicy,
) -> Result<ReferenceImportEnvironment, ReferenceCheckError> {
    if cert_bytes.is_empty() {
        return Err(ReferenceCheckError::empty());
    }
    decode::build_import_environment_impl(cert_bytes, import_store, policy)
}

/// Check a canonical certificate with the Phase 8 reference-checker API.
///
/// This decodes canonical source-free certificate bytes, verifies stored hashes,
/// resolves explicit imports, and runs the P8H-07 minimal type/declaration,
/// β/δ/ι/ζ conversion, and simple inductive/recursor checker. It intentionally
/// does not call the fast Rust kernel or `npa_cert::verify_module_cert`.
pub fn check_certificate(
    cert_bytes: &[u8],
    import_store: &ReferenceImportStore,
    policy: &ReferenceCheckerPolicy,
) -> ReferenceCheckResult {
    if cert_bytes.is_empty() {
        return ReferenceCheckResult::Rejected(ReferenceCheckError::empty());
    }

    match decode::check_certificate_impl(cert_bytes, import_store, policy) {
        Ok(module) => ReferenceCheckResult::Checked(module),
        Err(error) => ReferenceCheckResult::Rejected(error),
    }
}

/// Diagnostic observation captured at the independent checker's decode boundary.
///
/// This value is not proof evidence and does not influence checker policy or
/// acceptance. It is returned even when a later verification stage rejects the
/// certificate.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ReferenceCheckObservation {
    /// Whether canonical certificate decoding and structural validation completed.
    pub certificate_decoded: bool,
    /// Number of declarations in the decoded certificate, or zero before decode.
    pub declaration_count: usize,
    /// Canonical first-N declaration details requested by the caller.
    pub declarations: Vec<ReferenceCheckDeclarationObservation>,
}

/// Bounded declaration metadata captured at the reference-checker decode boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReferenceCheckDeclarationObservation {
    /// Declaration index in canonical certificate order.
    pub declaration_index: usize,
    /// Canonical declaration name.
    pub declaration: ReferenceModuleName,
    /// Number of distinct certificate term-table nodes reachable from the declaration.
    pub term_nodes: usize,
}

/// Hard cap for declaration details returned by one observed reference check.
pub const REFERENCE_CHECK_DECLARATION_DETAIL_LIMIT: usize = 2_048;

/// Check a canonical certificate and return diagnostic decode-boundary data.
///
/// The observation is untrusted performance metadata. The verdict is identical
/// to [`check_certificate`] for the same inputs. Requested detail is clamped to
/// [`REFERENCE_CHECK_DECLARATION_DETAIL_LIMIT`].
pub fn check_certificate_with_observation(
    cert_bytes: &[u8],
    import_store: &ReferenceImportStore,
    policy: &ReferenceCheckerPolicy,
    declaration_detail_limit: usize,
) -> (ReferenceCheckResult, ReferenceCheckObservation) {
    let mut observation = ReferenceCheckObservation::default();
    if cert_bytes.is_empty() {
        return (
            ReferenceCheckResult::Rejected(ReferenceCheckError::empty()),
            observation,
        );
    }

    let result = match decode::check_certificate_impl_with_observation(
        cert_bytes,
        import_store,
        policy,
        declaration_detail_limit.min(REFERENCE_CHECK_DECLARATION_DETAIL_LIMIT),
        &mut observation,
    ) {
        Ok(module) => ReferenceCheckResult::Checked(module),
        Err(error) => ReferenceCheckResult::Rejected(error),
    };
    (result, observation)
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::decode::{ReferenceUniverseConstraint, ReferenceUniverseContext};
    use npa_cert::{
        build_module_cert, encode_module_cert, generate_inductive_artifacts_v1,
        generate_mutual_inductive_artifacts_v1, verify_module_cert,
        verify_module_cert_with_import_refs,
        verify_module_cert_with_import_refs_and_kernel_options, AxiomPolicy, CertError, CoreModule,
        Name, VerifierSession,
    };
    use npa_kernel::{
        eq, eq_inductive, eq_refl, nat, nat_inductive, nat_succ, nat_zero, prop, type0, Binder,
        ConstructorDecl, Ctx, Decl, Env, Error, Expr, InductiveDecl, KernelExecutionOptions, Level,
        MutualInductiveBlock, Reducibility, ResourceLimitKind, UniverseConstraint, UniverseContext,
        MAX_UNIVERSE_CONTEXT_NODES,
    };
    use sha2::{Digest, Sha256};

    fn encode_uvar(mut value: u64) -> Vec<u8> {
        let mut out = Vec::new();
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
        out
    }

    fn encode_string(out: &mut Vec<u8>, value: &str) {
        out.extend(encode_uvar(value.len() as u64));
        out.extend(value.as_bytes());
    }

    fn encode_name(out: &mut Vec<u8>, components: &[&str]) {
        out.extend(encode_uvar(components.len() as u64));
        for component in components {
            encode_string(out, component);
        }
    }

    fn header_bytes_for_tags(format: &str, core_spec: &str, module: &[&str]) -> Vec<u8> {
        let mut bytes = Vec::new();
        encode_string(&mut bytes, format);
        encode_string(&mut bytes, core_spec);
        encode_name(&mut bytes, module);
        bytes
    }

    fn header_bytes_for(module: &[&str]) -> Vec<u8> {
        header_bytes_for_tags(REFERENCE_CERTIFICATE_FORMAT, REFERENCE_CORE_SPEC, module)
    }

    fn ref_name(name: &str) -> ReferenceModuleName {
        ReferenceModuleName::from_dotted(name).unwrap()
    }

    fn rz() -> ReferenceCoreLevel {
        ReferenceCoreLevel::Zero
    }

    fn rp(name: &str) -> ReferenceCoreLevel {
        ReferenceCoreLevel::Param(ref_name(name))
    }

    fn rs(level: ReferenceCoreLevel) -> ReferenceCoreLevel {
        ReferenceCoreLevel::Succ(Arc::new(level))
    }

    fn rmax(lhs: ReferenceCoreLevel, rhs: ReferenceCoreLevel) -> ReferenceCoreLevel {
        ReferenceCoreLevel::Max(Arc::new(lhs), Arc::new(rhs))
    }

    fn rimax(lhs: ReferenceCoreLevel, rhs: ReferenceCoreLevel) -> ReferenceCoreLevel {
        ReferenceCoreLevel::IMax(Arc::new(lhs), Arc::new(rhs))
    }

    fn rc_le(lhs: ReferenceCoreLevel, rhs: ReferenceCoreLevel) -> ReferenceUniverseConstraint {
        ReferenceUniverseConstraint::le(lhs, rhs)
    }

    fn rc_eq(lhs: ReferenceCoreLevel, rhs: ReferenceCoreLevel) -> ReferenceUniverseConstraint {
        ReferenceUniverseConstraint::eq(lhs, rhs)
    }

    fn ref_params(params: &[&str]) -> Vec<ReferenceModuleName> {
        params.iter().map(|param| ref_name(param)).collect()
    }

    fn reason(error: ReferenceCheckError) -> Option<ReferenceCheckReason> {
        error.reason
    }

    fn header_bytes() -> Vec<u8> {
        header_bytes_for(&["Std", "Nat"])
    }

    fn hash_with_domain(domain: &[u8], payload: &[u8]) -> ReferenceHash {
        let mut hasher = Sha256::new();
        hasher.update(domain);
        hasher.update(payload);
        hasher.finalize().into()
    }

    fn kernel_pi_telescope(domains: Vec<Expr>, body: Expr) -> Expr {
        domains
            .into_iter()
            .rev()
            .fold(body, |body, domain| Expr::pi("_", domain, body))
    }

    fn kernel_inductive_type(data: &InductiveDecl) -> Expr {
        let domains = data
            .params
            .iter()
            .chain(&data.indices)
            .map(|binder| binder.ty.clone())
            .collect();
        kernel_pi_telescope(domains, Expr::sort(data.sort.clone()))
    }

    fn certificate_for_inductive(module: &str, data: InductiveDecl) -> Vec<u8> {
        let cert = build_module_cert(
            CoreModule {
                name: Name::from_dotted(module),
                declarations: vec![Decl::Inductive {
                    name: data.name.clone(),
                    universe_params: data.universe_params.clone(),
                    ty: kernel_inductive_type(&data),
                    data: Box::new(data),
                }],
            },
            &[],
        )
        .unwrap();
        encode_module_cert(&cert).unwrap()
    }

    fn certificate_for_indexed_inductives() -> Vec<u8> {
        let nat_data = nat_inductive();
        let vec_data = generate_inductive_artifacts_v1(&vec_inductive()).unwrap();
        let fin_data = generate_inductive_artifacts_v1(&fin_inductive()).unwrap();
        let cert = build_module_cert(
            CoreModule {
                name: Name::from_dotted("Test.Indexed"),
                declarations: vec![
                    Decl::Inductive {
                        name: nat_data.name.clone(),
                        universe_params: nat_data.universe_params.clone(),
                        ty: kernel_inductive_type(&nat_data),
                        data: Box::new(nat_data),
                    },
                    Decl::Inductive {
                        name: vec_data.name.clone(),
                        universe_params: vec_data.universe_params.clone(),
                        ty: kernel_inductive_type(&vec_data),
                        data: Box::new(vec_data),
                    },
                    Decl::Inductive {
                        name: fin_data.name.clone(),
                        universe_params: fin_data.universe_params.clone(),
                        ty: kernel_inductive_type(&fin_data),
                        data: Box::new(fin_data),
                    },
                ],
            },
            &[],
        )
        .unwrap();
        encode_module_cert(&cert).unwrap()
    }

    #[test]
    fn memoized_fast_certificate_agrees_with_off_and_reference_checkers() {
        let level = Level::param("u");
        let cert = build_module_cert(
            CoreModule {
                name: Name::from_dotted("Test.KernelMemo"),
                declarations: vec![Decl::Def {
                    name: "Memo.id".to_owned(),
                    universe_params: vec!["u".to_owned()],
                    ty: Expr::pi(
                        "A",
                        Expr::sort(level.clone()),
                        Expr::pi("x", Expr::bvar(0), Expr::bvar(1)),
                    ),
                    value: Expr::lam(
                        "A",
                        Expr::sort(level),
                        Expr::lam("x", Expr::bvar(0), Expr::bvar(0)),
                    ),
                    reducibility: Reducibility::Reducible,
                }],
            },
            &[],
        )
        .unwrap();
        let bytes = encode_module_cert(&cert).unwrap();
        let fast_off =
            verify_module_cert_with_import_refs(&bytes, &[], &AxiomPolicy::normal()).unwrap();
        let fast_memo = verify_module_cert_with_import_refs_and_kernel_options(
            &bytes,
            &[],
            &AxiomPolicy::normal(),
            KernelExecutionOptions::ephemeral_memo(),
        )
        .unwrap();
        assert_eq!(fast_memo, fast_off);

        let reference = check_certificate(
            &bytes,
            &ReferenceImportStore::default(),
            &ReferenceCheckerPolicy::default(),
        );
        let ReferenceCheckResult::Checked(reference) = reference else {
            panic!("reference checker rejected memo differential fixture");
        };
        assert_eq!(reference.export_hash(), &fast_memo.export_hash());
        assert_eq!(reference.certificate_hash(), &fast_memo.certificate_hash());
    }

    fn std_logic_eq_certificate() -> Vec<u8> {
        certificate_for_inductive("Std.Logic", eq_inductive())
    }

    fn std_nat_basic_certificate() -> Vec<u8> {
        certificate_for_inductive("Std.Nat.Basic", nat_inductive())
    }

    fn universe_meta_param_certificate() -> Vec<u8> {
        let mut cert = build_module_cert(
            CoreModule {
                name: Name::from_dotted("M"),
                declarations: vec![Decl::Axiom {
                    name: "a".to_owned(),
                    universe_params: vec!["w".to_owned()],
                    ty: Expr::sort(Level::param("w")),
                }],
            },
            &[],
        )
        .unwrap();
        for name in &mut cert.name_table {
            if name.as_dotted() == "w" {
                *name = Name::from_dotted("z?meta");
            }
        }
        encode_module_cert(&cert).unwrap()
    }

    fn constrained_axiom_certificate() -> Vec<u8> {
        let cert = build_module_cert(
            CoreModule {
                name: Name::from_dotted("Test.UniverseConstraints"),
                declarations: vec![Decl::AxiomConstrained {
                    name: "List.map".to_owned(),
                    universe_params: vec!["u".to_owned(), "v".to_owned(), "w".to_owned()],
                    universe_constraints: vec![UniverseConstraint::le(
                        Level::max(Level::param("u"), Level::param("v")),
                        Level::param("w"),
                    )],
                    ty: Expr::sort(Level::param("w")),
                }],
            },
            &[],
        )
        .unwrap();
        encode_module_cert(&cert).unwrap()
    }

    fn use_constrained_axiom_module(levels: Vec<Level>) -> CoreModule {
        CoreModule {
            name: Name::from_dotted("Test.UseUniverseConstraints"),
            declarations: vec![Decl::Axiom {
                name: "Use.map".to_owned(),
                universe_params: Vec::new(),
                ty: Expr::konst("List.map", levels),
            }],
        }
    }

    fn std_nat_zero_eq_zero_certificate(logic_bytes: &[u8]) -> Vec<u8> {
        let mut session = VerifierSession::new();
        let logic = verify_module_cert(logic_bytes, &mut session, &AxiomPolicy::normal()).unwrap();
        let nat_data = nat_inductive();
        let cert = build_module_cert(
            CoreModule {
                name: Name::from_dotted("Std.Nat"),
                declarations: vec![
                    Decl::Inductive {
                        name: nat_data.name.clone(),
                        universe_params: nat_data.universe_params.clone(),
                        ty: kernel_inductive_type(&nat_data),
                        data: Box::new(nat_data),
                    },
                    Decl::Theorem {
                        name: "Nat.zero_eq_zero".to_owned(),
                        universe_params: Vec::new(),
                        ty: eq(type0(), nat(), nat_zero(), nat_zero()),
                        proof: eq_refl(type0(), nat(), nat_zero()),
                    },
                ],
            },
            std::slice::from_ref(&logic),
        )
        .unwrap();
        encode_module_cert(&cert).unwrap()
    }

    fn list_inductive() -> InductiveDecl {
        let u = Level::param("u");
        let list_a = |level: Level, a: Expr| Expr::app(Expr::konst("List", vec![level]), a);

        InductiveDecl::new(
            "List",
            vec!["u".to_owned()],
            vec![Binder::new("A", Expr::sort(u.clone()))],
            vec![],
            u.clone(),
            vec![
                ConstructorDecl::new(
                    "List.nil",
                    Expr::pi("A", Expr::sort(u.clone()), list_a(u.clone(), Expr::bvar(0))),
                ),
                ConstructorDecl::new(
                    "List.cons",
                    Expr::pi(
                        "A",
                        Expr::sort(u.clone()),
                        Expr::pi(
                            "x",
                            Expr::bvar(0),
                            Expr::pi(
                                "xs",
                                list_a(u.clone(), Expr::bvar(1)),
                                list_a(u.clone(), Expr::bvar(2)),
                            ),
                        ),
                    ),
                ),
            ],
            None,
        )
    }

    fn list_type(level: Level, elem: Expr) -> Expr {
        Expr::app(Expr::konst("List", vec![level]), elem)
    }

    fn rose_type(level: Level, elem: Expr) -> Expr {
        Expr::app(Expr::konst("Rose", vec![level]), elem)
    }

    fn rose_nested_list_inductive() -> InductiveDecl {
        let u = Level::param("u");
        InductiveDecl::new(
            "Rose",
            vec!["u".to_owned()],
            vec![Binder::new("A", Expr::sort(u.clone()))],
            vec![],
            u.clone(),
            vec![ConstructorDecl::new(
                "Rose.node",
                Expr::pi(
                    "A",
                    Expr::sort(u.clone()),
                    Expr::pi(
                        "value",
                        Expr::bvar(0),
                        Expr::pi(
                            "children",
                            list_type(u.clone(), rose_type(u.clone(), Expr::bvar(1))),
                            rose_type(u, Expr::bvar(2)),
                        ),
                    ),
                ),
            )],
            None,
        )
    }

    fn certificate_for_nested_rose() -> Vec<u8> {
        let list_data = generate_inductive_artifacts_v1(&list_inductive()).unwrap();
        let rose_data = generate_inductive_artifacts_v1(&rose_nested_list_inductive()).unwrap();
        let cert = build_module_cert(
            CoreModule {
                name: Name::from_dotted("Test.NestedRose"),
                declarations: vec![
                    Decl::Inductive {
                        name: list_data.name.clone(),
                        universe_params: list_data.universe_params.clone(),
                        ty: kernel_inductive_type(&list_data),
                        data: Box::new(list_data),
                    },
                    Decl::Inductive {
                        name: rose_data.name.clone(),
                        universe_params: rose_data.universe_params.clone(),
                        ty: kernel_inductive_type(&rose_data),
                        data: Box::new(rose_data),
                    },
                ],
            },
            &[],
        )
        .unwrap();
        encode_module_cert(&cert).unwrap()
    }

    fn vec_type(level: Level, a: Expr, n: Expr) -> Expr {
        Expr::apps(Expr::konst("Vec", vec![level]), vec![a, n])
    }

    fn vec_nil(level: Level, a: Expr) -> Expr {
        Expr::app(Expr::konst("Vec.nil", vec![level]), a)
    }

    fn vec_inductive() -> InductiveDecl {
        let u = Level::param("u");
        InductiveDecl::new(
            "Vec",
            vec!["u".to_owned()],
            vec![Binder::new("A", Expr::sort(u.clone()))],
            vec![Binder::new("n", nat())],
            u.clone(),
            vec![
                ConstructorDecl::new(
                    "Vec.nil",
                    Expr::pi(
                        "A",
                        Expr::sort(u.clone()),
                        vec_type(u.clone(), Expr::bvar(0), nat_zero()),
                    ),
                ),
                ConstructorDecl::new(
                    "Vec.cons",
                    Expr::pi(
                        "A",
                        Expr::sort(u.clone()),
                        Expr::pi(
                            "n",
                            nat(),
                            Expr::pi(
                                "x",
                                Expr::bvar(1),
                                Expr::pi(
                                    "xs",
                                    vec_type(u.clone(), Expr::bvar(2), Expr::bvar(1)),
                                    vec_type(u.clone(), Expr::bvar(3), nat_succ(Expr::bvar(2))),
                                ),
                            ),
                        ),
                    ),
                ),
            ],
            None,
        )
        .with_universe_constraints(vec![UniverseConstraint::le(type0(), u)])
    }

    fn fin_type(n: Expr) -> Expr {
        Expr::app(Expr::konst("Fin", vec![]), n)
    }

    fn fin_inductive() -> InductiveDecl {
        InductiveDecl::new(
            "Fin",
            vec![],
            vec![],
            vec![Binder::new("n", nat())],
            type0(),
            vec![
                ConstructorDecl::new(
                    "Fin.zero",
                    Expr::pi("n", nat(), fin_type(nat_succ(Expr::bvar(0)))),
                ),
                ConstructorDecl::new(
                    "Fin.succ",
                    Expr::pi(
                        "n",
                        nat(),
                        Expr::pi(
                            "i",
                            fin_type(Expr::bvar(0)),
                            fin_type(nat_succ(Expr::bvar(1))),
                        ),
                    ),
                ),
            ],
            None,
        )
    }

    fn even_type(n: Expr) -> Expr {
        Expr::app(Expr::konst("Even", vec![]), n)
    }

    fn odd_type(n: Expr) -> Expr {
        Expr::app(Expr::konst("Odd", vec![]), n)
    }

    fn even_zero() -> Expr {
        Expr::konst("Even.zero", vec![])
    }

    fn even_succ(n: Expr, h: Expr) -> Expr {
        Expr::apps(Expr::konst("Even.succ", vec![]), vec![n, h])
    }

    fn odd_succ(n: Expr, h: Expr) -> Expr {
        Expr::apps(Expr::konst("Odd.succ", vec![]), vec![n, h])
    }

    fn mutual_identity_motive_args() -> (Expr, Expr, Expr, Expr, Expr) {
        let m_even = Expr::lam(
            "n",
            nat(),
            Expr::lam("_", even_type(Expr::bvar(0)), even_type(Expr::bvar(1))),
        );
        let m_odd = Expr::lam(
            "n",
            nat(),
            Expr::lam("_", odd_type(Expr::bvar(0)), odd_type(Expr::bvar(1))),
        );
        let z = even_zero();
        let even_step = Expr::lam(
            "n",
            nat(),
            Expr::lam(
                "h",
                odd_type(Expr::bvar(0)),
                Expr::lam(
                    "_ih",
                    odd_type(Expr::bvar(1)),
                    even_succ(Expr::bvar(2), Expr::bvar(1)),
                ),
            ),
        );
        let odd_step = Expr::lam(
            "n",
            nat(),
            Expr::lam(
                "h",
                even_type(Expr::bvar(0)),
                Expr::lam(
                    "_ih",
                    even_type(Expr::bvar(1)),
                    odd_succ(Expr::bvar(2), Expr::bvar(1)),
                ),
            ),
        );
        (m_even, m_odd, z, even_step, odd_step)
    }

    fn even_odd_mutual_base() -> MutualInductiveBlock {
        MutualInductiveBlock::new(
            "EvenOdd",
            vec![],
            vec![
                InductiveDecl::new(
                    "Even",
                    vec![],
                    vec![],
                    vec![Binder::new("n", nat())],
                    prop(),
                    vec![
                        ConstructorDecl::new("Even.zero", even_type(nat_zero())),
                        ConstructorDecl::new(
                            "Even.succ",
                            Expr::pi(
                                "n",
                                nat(),
                                Expr::pi(
                                    "h",
                                    odd_type(Expr::bvar(0)),
                                    even_type(nat_succ(Expr::bvar(1))),
                                ),
                            ),
                        ),
                    ],
                    None,
                ),
                InductiveDecl::new(
                    "Odd",
                    vec![],
                    vec![],
                    vec![Binder::new("n", nat())],
                    prop(),
                    vec![ConstructorDecl::new(
                        "Odd.succ",
                        Expr::pi(
                            "n",
                            nat(),
                            Expr::pi(
                                "h",
                                even_type(Expr::bvar(0)),
                                odd_type(nat_succ(Expr::bvar(1))),
                            ),
                        ),
                    )],
                    None,
                ),
            ],
        )
    }

    fn certificate_for_mutual_even_odd() -> Vec<u8> {
        let nat_data = nat_inductive();
        let block = generate_mutual_inductive_artifacts_v1(&even_odd_mutual_base()).unwrap();
        let cert = build_module_cert(
            CoreModule {
                name: Name::from_dotted("Test.EvenOdd"),
                declarations: vec![
                    Decl::Inductive {
                        name: nat_data.name.clone(),
                        universe_params: nat_data.universe_params.clone(),
                        ty: kernel_inductive_type(&nat_data),
                        data: Box::new(nat_data),
                    },
                    Decl::MutualInductiveBlock {
                        name: block.name.clone(),
                        universe_params: block.universe_params.clone(),
                        data: Box::new(block),
                    },
                ],
            },
            &[],
        )
        .unwrap();
        encode_module_cert(&cert).unwrap()
    }

    fn certificate_for_mutual_odd_iota_theorem() -> Vec<u8> {
        let nat_data = nat_inductive();
        let block = generate_mutual_inductive_artifacts_v1(&even_odd_mutual_base()).unwrap();
        let (m_even, m_odd, z, even_step, odd_step) = mutual_identity_motive_args();
        let odd_one = odd_succ(nat_zero(), even_zero());
        let proof = Expr::apps(
            Expr::konst("Odd.rec", vec![]),
            vec![
                m_even,
                m_odd,
                z,
                even_step,
                odd_step,
                nat_succ(nat_zero()),
                odd_one,
            ],
        );
        let cert = build_module_cert(
            CoreModule {
                name: Name::from_dotted("Test.EvenOddIota"),
                declarations: vec![
                    Decl::Inductive {
                        name: nat_data.name.clone(),
                        universe_params: nat_data.universe_params.clone(),
                        ty: kernel_inductive_type(&nat_data),
                        data: Box::new(nat_data),
                    },
                    Decl::MutualInductiveBlock {
                        name: block.name.clone(),
                        universe_params: block.universe_params.clone(),
                        data: Box::new(block),
                    },
                    Decl::Theorem {
                        name: "odd_iota".to_owned(),
                        universe_params: vec![],
                        ty: odd_type(nat_succ(nat_zero())),
                        proof,
                    },
                ],
            },
            &[],
        )
        .unwrap();
        encode_module_cert(&cert).unwrap()
    }

    fn nat_rec_term(major: Expr) -> Expr {
        let result_universe = type0();
        let motive_universe = Level::succ(result_universe.clone());
        let motive = Expr::lam("_", nat(), Expr::sort(result_universe.clone()));
        let step = Expr::lam(
            "_",
            nat(),
            Expr::lam("ih", Expr::sort(result_universe), nat()),
        );
        Expr::apps(
            Expr::konst("Nat.rec", vec![motive_universe]),
            vec![motive, nat(), step, major],
        )
    }

    fn nat_iota_theorem_certificate(major: Expr) -> Vec<u8> {
        let nat_data = nat_inductive();
        let cert = build_module_cert(
            CoreModule {
                name: Name::from_dotted("Test.NatIota"),
                declarations: vec![
                    Decl::Inductive {
                        name: nat_data.name.clone(),
                        universe_params: nat_data.universe_params.clone(),
                        ty: kernel_inductive_type(&nat_data),
                        data: Box::new(nat_data),
                    },
                    Decl::Theorem {
                        name: "Nat.iotaWitness".to_owned(),
                        universe_params: vec![],
                        ty: nat_rec_term(major),
                        proof: nat_zero(),
                    },
                ],
            },
            &[],
        )
        .unwrap();
        encode_module_cert(&cert).unwrap()
    }

    fn imported_nat_iota_theorem_certificate(
        nat_import: &npa_cert::VerifiedModule,
        major: Expr,
    ) -> Vec<u8> {
        let cert = build_module_cert(
            CoreModule {
                name: Name::from_dotted("Test.ImportedNatIota"),
                declarations: vec![Decl::Theorem {
                    name: "Nat.importedIotaWitness".to_owned(),
                    universe_params: vec![],
                    ty: nat_rec_term(major),
                    proof: nat_zero(),
                }],
            },
            std::slice::from_ref(nat_import),
        )
        .unwrap();
        encode_module_cert(&cert).unwrap()
    }

    fn vec_rec_nil_term() -> Expr {
        let elem_level = type0();
        let motive_level = Level::succ(elem_level.clone());
        let motive = Expr::lam(
            "n",
            nat(),
            Expr::lam(
                "_",
                vec_type(elem_level.clone(), nat(), Expr::bvar(0)),
                Expr::sort(elem_level.clone()),
            ),
        );
        let nil = vec_type(elem_level.clone(), nat(), nat_zero());
        let major = vec_nil(elem_level.clone(), nat());
        let cons = Expr::lam(
            "n",
            nat(),
            Expr::lam(
                "x",
                nat(),
                Expr::lam(
                    "xs",
                    vec_type(elem_level.clone(), nat(), Expr::bvar(1)),
                    Expr::lam(
                        "_ih",
                        Expr::sort(elem_level.clone()),
                        vec_type(elem_level.clone(), nat(), nat_succ(Expr::bvar(3))),
                    ),
                ),
            ),
        );
        Expr::apps(
            Expr::konst("Vec.rec", vec![elem_level.clone(), motive_level]),
            vec![nat(), motive, nil, cons, nat_zero(), major],
        )
    }

    fn imported_vec_iota_theorem_certificate(indexed_import: &npa_cert::VerifiedModule) -> Vec<u8> {
        let elem_level = type0();
        let cert = build_module_cert(
            CoreModule {
                name: Name::from_dotted("Test.ImportedVecIota"),
                declarations: vec![Decl::Theorem {
                    name: "Vec.importedIotaWitness".to_owned(),
                    universe_params: vec![],
                    ty: vec_rec_nil_term(),
                    proof: vec_nil(elem_level.clone(), nat()),
                }],
            },
            std::slice::from_ref(indexed_import),
        )
        .unwrap();
        encode_module_cert(&cert).unwrap()
    }

    fn encode_usize_vec(out: &mut Vec<u8>, values: &[usize]) {
        out.extend(encode_uvar(values.len() as u64));
        for value in values {
            out.extend(encode_uvar(*value as u64));
        }
    }

    fn encode_option_usize(out: &mut Vec<u8>, value: Option<usize>) {
        match value {
            Some(value) => {
                out.push(0x01);
                out.extend(encode_uvar(value as u64));
            }
            None => out.push(0x00),
        }
    }

    fn encode_option_hash(out: &mut Vec<u8>, value: Option<&ReferenceHash>) {
        match value {
            Some(value) => {
                out.push(0x01);
                out.extend(value);
            }
            None => out.push(0x00),
        }
    }

    fn encode_dependency_entries_empty(out: &mut Vec<u8>) {
        out.extend(encode_uvar(0));
    }

    fn encode_axiom_refs_empty(out: &mut Vec<u8>) {
        out.extend(encode_uvar(0));
    }

    fn encode_universe_constraints_empty(out: &mut Vec<u8>) {
        out.extend(encode_uvar(0));
    }

    fn encode_local_global_ref(out: &mut Vec<u8>, decl_index: usize) {
        out.push(0x01);
        out.extend(encode_uvar(decl_index as u64));
    }

    fn encode_axiom_refs_self(out: &mut Vec<u8>, decl_interface_hash: &ReferenceHash) {
        out.extend(encode_uvar(1));
        encode_local_global_ref(out, 0);
        out.extend(encode_uvar(0)); // name A
        out.extend(decl_interface_hash);
    }

    fn encode_axiom_refs_optional_self(
        out: &mut Vec<u8>,
        include_self: bool,
        decl_interface_hash: &ReferenceHash,
    ) {
        if include_self {
            encode_axiom_refs_self(out, decl_interface_hash);
        } else {
            encode_axiom_refs_empty(out);
        }
    }

    fn legacy_bytes_from_npa_cert(mut cert: npa_cert::ModuleCert) -> Vec<u8> {
        cert.header.format = REFERENCE_LEGACY_CERTIFICATE_FORMAT.to_owned();
        cert.header.core_spec = REFERENCE_LEGACY_CORE_SPEC.to_owned();
        cert.hashes.export_hash = hash_with_domain(
            REFERENCE_LEGACY_MODULE_EXPORT_DOMAIN,
            &encode_npa_cert_export_block_legacy(&cert.export_block),
        );
        cert.hashes.certificate_hash = [0; 32];
        let placeholder = encode_module_cert(&cert).unwrap();
        let without_hash = placeholder
            .get(..placeholder.len() - 32)
            .expect("module certificate hash trailer is present");
        cert.hashes.certificate_hash =
            hash_with_domain(REFERENCE_LEGACY_MODULE_CERT_DOMAIN, without_hash);
        encode_module_cert(&cert).unwrap()
    }

    fn encode_npa_cert_export_block_legacy(block: &[npa_cert::ExportEntry]) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend(encode_uvar(block.len() as u64));
        for entry in block {
            out.extend(encode_uvar(entry.name as u64));
            out.push(match entry.kind {
                npa_cert::ExportKind::Axiom => 0x00,
                npa_cert::ExportKind::Def => 0x01,
                npa_cert::ExportKind::Theorem => 0x02,
                npa_cert::ExportKind::Inductive => 0x03,
                npa_cert::ExportKind::Constructor => 0x04,
                npa_cert::ExportKind::Recursor => 0x05,
            });
            encode_usize_vec(&mut out, &entry.universe_params);
            out.extend(encode_uvar(entry.ty as u64));
            encode_option_usize(&mut out, entry.body);
            out.extend(entry.type_hash);
            encode_option_hash(&mut out, entry.body_hash.as_ref());
            encode_npa_cert_option_reducibility(&mut out, entry.reducibility);
            encode_npa_cert_option_opacity(&mut out, entry.opacity);
            out.extend(entry.decl_interface_hash);
            encode_npa_cert_axiom_refs(&mut out, &entry.axiom_dependencies);
        }
        out
    }

    fn encode_npa_cert_axiom_refs(out: &mut Vec<u8>, axioms: &[npa_cert::AxiomRef]) {
        out.extend(encode_uvar(axioms.len() as u64));
        for axiom in axioms {
            encode_npa_cert_global_ref(out, &axiom.global_ref);
            out.extend(encode_uvar(axiom.name as u64));
            out.extend(axiom.decl_interface_hash);
        }
    }

    fn encode_npa_cert_global_ref(out: &mut Vec<u8>, global_ref: &npa_cert::GlobalRef) {
        match global_ref {
            npa_cert::GlobalRef::Builtin {
                name,
                decl_interface_hash,
            } => {
                out.push(0x03);
                out.extend(encode_uvar(*name as u64));
                out.extend(decl_interface_hash);
            }
            npa_cert::GlobalRef::Imported {
                import_index,
                name,
                decl_interface_hash,
            } => {
                out.push(0x00);
                out.extend(encode_uvar(*import_index as u64));
                out.extend(encode_uvar(*name as u64));
                out.extend(decl_interface_hash);
            }
            npa_cert::GlobalRef::Local { decl_index } => {
                out.push(0x01);
                out.extend(encode_uvar(*decl_index as u64));
            }
            npa_cert::GlobalRef::LocalGenerated { decl_index, name } => {
                out.push(0x02);
                out.extend(encode_uvar(*decl_index as u64));
                out.extend(encode_uvar(*name as u64));
            }
        }
    }

    fn encode_npa_cert_option_reducibility(
        out: &mut Vec<u8>,
        value: Option<npa_cert::CertReducibility>,
    ) {
        match value {
            Some(npa_cert::CertReducibility::Reducible) => out.extend([0x01, 0x00]),
            Some(npa_cert::CertReducibility::Opaque) => out.extend([0x01, 0x01]),
            None => out.push(0x00),
        }
    }

    fn encode_npa_cert_option_opacity(out: &mut Vec<u8>, value: Option<npa_cert::Opacity>) {
        match value {
            Some(npa_cert::Opacity::Opaque) => out.extend([0x01, 0x00]),
            None => out.push(0x00),
        }
    }

    fn append_common_empty_suffix(bytes: &mut Vec<u8>) {
        append_common_empty_suffix_with_domains(
            bytes,
            REFERENCE_MODULE_EXPORT_DOMAIN,
            REFERENCE_MODULE_CERT_DOMAIN,
        );
    }

    fn append_common_empty_suffix_with_domains(
        bytes: &mut Vec<u8>,
        export_domain: &[u8],
        certificate_domain: &[u8],
    ) {
        bytes.extend(encode_uvar(0)); // level table
        bytes.extend(encode_uvar(0)); // term table
        bytes.extend(encode_uvar(0)); // declarations
        let export_block = encode_uvar(0);
        bytes.extend(&export_block);
        let mut axiom_report = encode_uvar(0); // per-declaration entries
        axiom_report.extend(encode_uvar(0)); // module axioms
        bytes.extend(&axiom_report);
        let export_hash = hash_with_domain(export_domain, &export_block);
        let axiom_report_hash = hash_with_domain(b"NPA-AXIOM-REPORT-0.1", &axiom_report);
        bytes.extend(export_hash);
        bytes.extend(axiom_report_hash);
        let certificate_hash = hash_with_domain(certificate_domain, bytes);
        bytes.extend(certificate_hash);
    }

    fn empty_module_certificate() -> Vec<u8> {
        let mut bytes = header_bytes();
        bytes.extend(encode_uvar(0)); // imports
        bytes.extend(encode_uvar(1)); // name table contains the header module name
        encode_name(&mut bytes, &["Std", "Nat"]);
        append_common_empty_suffix(&mut bytes);
        bytes
    }

    fn legacy_empty_module_certificate() -> Vec<u8> {
        let mut bytes = header_bytes_for_tags(
            REFERENCE_LEGACY_CERTIFICATE_FORMAT,
            REFERENCE_LEGACY_CORE_SPEC,
            &["Std", "Nat"],
        );
        bytes.extend(encode_uvar(0)); // imports
        bytes.extend(encode_uvar(1)); // name table contains the header module name
        encode_name(&mut bytes, &["Std", "Nat"]);
        append_common_empty_suffix_with_domains(
            &mut bytes,
            REFERENCE_LEGACY_MODULE_EXPORT_DOMAIN,
            REFERENCE_LEGACY_MODULE_CERT_DOMAIN,
        );
        bytes
    }

    fn previous_empty_module_certificate() -> Vec<u8> {
        let mut bytes = header_bytes_for_tags(
            REFERENCE_PREVIOUS_CERTIFICATE_FORMAT,
            REFERENCE_PREVIOUS_CORE_SPEC,
            &["Std", "Nat"],
        );
        bytes.extend(encode_uvar(0)); // imports
        bytes.extend(encode_uvar(1)); // name table contains the header module name
        encode_name(&mut bytes, &["Std", "Nat"]);
        append_common_empty_suffix_with_domains(
            &mut bytes,
            REFERENCE_PREVIOUS_MODULE_EXPORT_DOMAIN,
            REFERENCE_PREVIOUS_MODULE_CERT_DOMAIN,
        );
        bytes
    }

    fn certificate_with_name_table(names: &[&[&str]]) -> Vec<u8> {
        let mut bytes = header_bytes();
        bytes.extend(encode_uvar(0)); // imports
        bytes.extend(encode_uvar(names.len() as u64));
        for name in names {
            encode_name(&mut bytes, name);
        }
        append_common_empty_suffix(&mut bytes);
        bytes
    }

    fn empty_module_certificate_importing_std_nat(
        export_hash: ReferenceHash,
        certificate_hash: Option<ReferenceHash>,
    ) -> Vec<u8> {
        let mut bytes = header_bytes_for(&["Use", "Import"]);
        bytes.extend(encode_uvar(1)); // imports
        encode_name(&mut bytes, &["Std", "Nat"]);
        bytes.extend(export_hash);
        encode_option_hash(&mut bytes, certificate_hash.as_ref());
        bytes.extend(encode_uvar(2)); // name table
        encode_name(&mut bytes, &["Std", "Nat"]);
        encode_name(&mut bytes, &["Use", "Import"]);
        append_common_empty_suffix(&mut bytes);
        bytes
    }

    fn empty_module_certificate_importing_std_nat_twice(export_hash: ReferenceHash) -> Vec<u8> {
        let mut bytes = header_bytes_for(&["Use", "Import"]);
        bytes.extend(encode_uvar(2)); // imports
        for _ in 0..2 {
            encode_name(&mut bytes, &["Std", "Nat"]);
            bytes.extend(export_hash);
            encode_option_hash(&mut bytes, None);
        }
        bytes.extend(encode_uvar(2)); // name table
        encode_name(&mut bytes, &["Std", "Nat"]);
        encode_name(&mut bytes, &["Use", "Import"]);
        append_common_empty_suffix(&mut bytes);
        bytes
    }

    #[derive(Clone, Copy)]
    enum TestTerm {
        Sort(usize),
        BVar(u32),
        ConstLocal {
            decl_index: usize,
        },
        App(usize, usize),
        Lam {
            ty: usize,
            body: usize,
        },
        Pi {
            ty: usize,
            body: usize,
        },
        Let {
            ty: usize,
            value: usize,
            body: usize,
        },
    }

    #[derive(Clone, Copy)]
    enum TestDeclKind {
        ReducibleDef { ty: usize, value: usize },
        Theorem { ty: usize, proof: usize },
    }

    #[derive(Clone, Copy)]
    enum TestDeclSpec {
        Axiom {
            name: &'static str,
            ty: usize,
        },
        Def {
            name: &'static str,
            ty: usize,
            value: usize,
            reducible: bool,
        },
        Theorem {
            name: &'static str,
            ty: usize,
            proof: usize,
        },
    }

    impl TestDeclSpec {
        fn name(self) -> &'static str {
            match self {
                Self::Axiom { name, .. } | Self::Def { name, .. } | Self::Theorem { name, .. } => {
                    name
                }
            }
        }
    }

    #[derive(Clone)]
    struct TestInductiveSpec {
        names: Vec<&'static [&'static str]>,
        name: usize,
        universe_params: Vec<usize>,
        params: Vec<usize>,
        indices: Vec<usize>,
        sort: usize,
        constructors: Vec<TestConstructorSpec>,
        recursor: Option<TestRecursorSpec>,
    }

    #[derive(Clone, Copy)]
    struct TestConstructorSpec {
        name: usize,
        ty: usize,
    }

    #[derive(Clone, Copy)]
    struct TestRecursorSpec {
        name: usize,
        ty: usize,
        minor_start: usize,
        major_index: usize,
    }

    struct DeclarationCertificateFixture {
        bytes: Vec<u8>,
    }

    fn encode_test_terms(out: &mut Vec<u8>, terms: &[TestTerm]) {
        out.extend(encode_uvar(terms.len() as u64));
        for term in terms {
            match term {
                TestTerm::Sort(level) => {
                    out.push(0x00);
                    out.extend(encode_uvar(*level as u64));
                }
                TestTerm::BVar(index) => {
                    out.push(0x01);
                    out.extend(encode_uvar(u64::from(*index)));
                }
                TestTerm::ConstLocal { decl_index } => {
                    out.push(0x02);
                    out.push(0x01);
                    out.extend(encode_uvar(*decl_index as u64));
                    encode_usize_vec(out, &[]);
                }
                TestTerm::App(fun, arg) => {
                    out.push(0x03);
                    out.extend(encode_uvar(*fun as u64));
                    out.extend(encode_uvar(*arg as u64));
                }
                TestTerm::Lam { ty, body } => {
                    out.push(0x04);
                    out.extend(encode_uvar(*ty as u64));
                    out.extend(encode_uvar(*body as u64));
                }
                TestTerm::Pi { ty, body } => {
                    out.push(0x05);
                    out.extend(encode_uvar(*ty as u64));
                    out.extend(encode_uvar(*body as u64));
                }
                TestTerm::Let { ty, value, body } => {
                    out.push(0x06);
                    out.extend(encode_uvar(*ty as u64));
                    out.extend(encode_uvar(*value as u64));
                    out.extend(encode_uvar(*body as u64));
                }
            }
        }
    }

    fn test_term_hashes(level_hashes: &[ReferenceHash], terms: &[TestTerm]) -> Vec<ReferenceHash> {
        let mut hashes = Vec::with_capacity(terms.len());
        for term in terms {
            let mut payload = Vec::new();
            match term {
                TestTerm::Sort(level) => {
                    payload.push(0x00);
                    payload.extend(level_hashes[*level]);
                }
                TestTerm::BVar(index) => {
                    payload.push(0x01);
                    payload.extend(encode_uvar(u64::from(*index)));
                }
                TestTerm::ConstLocal { decl_index } => {
                    payload.push(0x02);
                    payload.push(0x01);
                    payload.extend(encode_uvar(*decl_index as u64));
                    payload.extend(encode_uvar(0));
                }
                TestTerm::App(fun, arg) => {
                    payload.push(0x03);
                    payload.extend(hashes[*fun]);
                    payload.extend(hashes[*arg]);
                }
                TestTerm::Lam { ty, body } => {
                    payload.push(0x04);
                    payload.extend(hashes[*ty]);
                    payload.extend(hashes[*body]);
                }
                TestTerm::Pi { ty, body } => {
                    payload.push(0x05);
                    payload.extend(hashes[*ty]);
                    payload.extend(hashes[*body]);
                }
                TestTerm::Let { ty, value, body } => {
                    payload.push(0x06);
                    payload.extend(hashes[*ty]);
                    payload.extend(hashes[*value]);
                    payload.extend(hashes[*body]);
                }
            }
            hashes.push(hash_with_domain(b"NPA-TERM-0.1", &payload));
        }
        hashes
    }

    fn test_level_hashes(terms: &[TestTerm]) -> Vec<ReferenceHash> {
        let max_sort_level = terms
            .iter()
            .filter_map(|term| match term {
                TestTerm::Sort(level) => Some(*level),
                TestTerm::BVar(_)
                | TestTerm::ConstLocal { .. }
                | TestTerm::App(_, _)
                | TestTerm::Lam { .. }
                | TestTerm::Pi { .. }
                | TestTerm::Let { .. } => None,
            })
            .max()
            .unwrap_or(0);
        let mut hashes = vec![hash_with_domain(b"NPA-LEVEL-0.1", &[0x00])];
        for level in 1..=max_sort_level {
            let mut payload = vec![0x01];
            payload.extend(hashes[level - 1]);
            hashes.push(hash_with_domain(b"NPA-LEVEL-0.1", &payload));
        }
        hashes
    }

    fn encode_test_levels(out: &mut Vec<u8>, level_hashes: &[ReferenceHash]) {
        out.extend(encode_uvar(level_hashes.len() as u64));
        out.push(0x00);
        for level in 1..level_hashes.len() {
            out.push(0x01);
            out.extend(encode_uvar((level - 1) as u64));
        }
    }

    fn encode_option_reducibility(out: &mut Vec<u8>, is_reducible: bool) {
        out.push(0x01);
        out.push(if is_reducible { 0x00 } else { 0x01 });
    }

    fn encode_option_opacity(out: &mut Vec<u8>, is_opaque: bool) {
        if is_opaque {
            out.push(0x01);
            out.push(0x00);
        } else {
            out.push(0x00);
        }
    }

    fn declaration_certificate_fixture(
        decl_name: &[&str],
        terms: &[TestTerm],
        kind: TestDeclKind,
    ) -> DeclarationCertificateFixture {
        let mut bytes = header_bytes();
        bytes.extend(encode_uvar(0)); // imports
        bytes.extend(encode_uvar(2)); // name table: decl, Std.Nat
        encode_name(&mut bytes, decl_name);
        encode_name(&mut bytes, &["Std", "Nat"]);

        let level_hashes = test_level_hashes(terms);
        encode_test_levels(&mut bytes, &level_hashes);
        let term_hashes = test_term_hashes(&level_hashes, terms);
        encode_test_terms(&mut bytes, terms);

        let (decl_tag, ty, body, body_hash, reducible, opaque) = match kind {
            TestDeclKind::ReducibleDef { ty, value } => {
                (0x01, ty, Some(value), Some(term_hashes[value]), true, false)
            }
            TestDeclKind::Theorem { ty, proof } => (0x02, ty, Some(proof), None, false, true),
        };

        let mut iface_payload = Vec::new();
        iface_payload.push(decl_tag);
        encode_name(&mut iface_payload, decl_name);
        encode_usize_vec(&mut iface_payload, &[]);
        iface_payload.extend(term_hashes[ty]);
        if reducible {
            iface_payload.push(0x00);
        }
        if opaque {
            iface_payload.push(0x00);
        }
        encode_dependency_entries_empty(&mut iface_payload);
        encode_axiom_refs_empty(&mut iface_payload);
        if reducible {
            iface_payload.extend(body_hash.unwrap());
        }
        let decl_interface_hash = hash_with_domain(b"NPA-DECL-IFACE-0.1", &iface_payload);

        let mut decl_cert_payload = Vec::new();
        decl_cert_payload.extend(decl_interface_hash);
        if let Some(body) = body {
            decl_cert_payload.extend(term_hashes[body]);
        }
        encode_dependency_entries_empty(&mut decl_cert_payload);
        if reducible {
            encode_axiom_refs_empty(&mut decl_cert_payload);
        }
        let decl_certificate_hash = hash_with_domain(b"NPA-DECL-CERT-0.1", &decl_cert_payload);

        bytes.extend(encode_uvar(1)); // declarations
        bytes.push(decl_tag);
        bytes.extend(encode_uvar(0)); // name
        encode_usize_vec(&mut bytes, &[]);
        bytes.extend(encode_uvar(ty as u64));
        match kind {
            TestDeclKind::ReducibleDef { value, .. } => {
                bytes.extend(encode_uvar(value as u64));
                bytes.push(0x00);
            }
            TestDeclKind::Theorem { proof, .. } => {
                bytes.extend(encode_uvar(proof as u64));
                bytes.push(0x00);
            }
        }
        encode_dependency_entries_empty(&mut bytes);
        encode_axiom_refs_empty(&mut bytes);
        bytes.extend(decl_interface_hash);
        bytes.extend(decl_certificate_hash);

        let mut export_block = Vec::new();
        export_block.extend(encode_uvar(1));
        export_block.extend(encode_uvar(0)); // name
        export_block.push(if reducible { 0x01 } else { 0x02 });
        encode_usize_vec(&mut export_block, &[]);
        encode_universe_constraints_empty(&mut export_block);
        export_block.extend(encode_uvar(ty as u64));
        encode_option_usize(&mut export_block, reducible.then_some(body.unwrap()));
        export_block.extend(term_hashes[ty]);
        encode_option_hash(&mut export_block, body_hash.as_ref());
        if reducible {
            encode_option_reducibility(&mut export_block, true);
        } else {
            export_block.push(0x00);
        }
        encode_option_opacity(&mut export_block, opaque);
        export_block.extend(decl_interface_hash);
        encode_axiom_refs_empty(&mut export_block);

        let mut axiom_report = Vec::new();
        axiom_report.extend(encode_uvar(1));
        axiom_report.extend(encode_uvar(0)); // decl index
        encode_axiom_refs_empty(&mut axiom_report);
        encode_axiom_refs_empty(&mut axiom_report);
        encode_axiom_refs_empty(&mut axiom_report); // module axioms

        bytes.extend(&export_block);
        bytes.extend(&axiom_report);
        let export_hash = hash_with_domain(REFERENCE_MODULE_EXPORT_DOMAIN, &export_block);
        let axiom_report_hash = hash_with_domain(b"NPA-AXIOM-REPORT-0.1", &axiom_report);
        bytes.extend(export_hash);
        bytes.extend(axiom_report_hash);
        let certificate_hash = hash_with_domain(REFERENCE_MODULE_CERT_DOMAIN, &bytes);
        bytes.extend(certificate_hash);

        DeclarationCertificateFixture { bytes }
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
    struct TestDependencyEntry {
        decl_index: usize,
        decl_interface_hash: ReferenceHash,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
    struct TestAxiomRef {
        decl_index: usize,
        name: usize,
        decl_interface_hash: ReferenceHash,
    }

    fn encode_test_dependency_entries(out: &mut Vec<u8>, entries: &[TestDependencyEntry]) {
        out.extend(encode_uvar(entries.len() as u64));
        for entry in entries {
            encode_local_global_ref(out, entry.decl_index);
            out.extend(entry.decl_interface_hash);
        }
    }

    fn encode_test_axiom_refs(out: &mut Vec<u8>, axioms: &[TestAxiomRef]) {
        out.extend(encode_uvar(axioms.len() as u64));
        for axiom in axioms {
            encode_local_global_ref(out, axiom.decl_index);
            out.extend(encode_uvar(axiom.name as u64));
            out.extend(axiom.decl_interface_hash);
        }
    }

    fn test_decl_term_ids(declaration: TestDeclSpec) -> Vec<usize> {
        match declaration {
            TestDeclSpec::Axiom { ty, .. } => vec![ty],
            TestDeclSpec::Def { ty, value, .. } => vec![ty, value],
            TestDeclSpec::Theorem { ty, proof, .. } => vec![ty, proof],
        }
    }

    fn test_decl_interface_term_ids(declaration: TestDeclSpec) -> Vec<usize> {
        match declaration {
            TestDeclSpec::Axiom { ty, .. } => vec![ty],
            TestDeclSpec::Def {
                ty,
                value,
                reducible,
                ..
            } => {
                let mut terms = vec![ty];
                if reducible {
                    terms.push(value);
                }
                terms
            }
            TestDeclSpec::Theorem { ty, .. } => vec![ty],
        }
    }

    fn collect_test_local_refs(terms: &[TestTerm], term_id: usize, refs: &mut BTreeSet<usize>) {
        match terms[term_id] {
            TestTerm::Sort(_) | TestTerm::BVar(_) => {}
            TestTerm::ConstLocal { decl_index } => {
                refs.insert(decl_index);
            }
            TestTerm::App(fun, arg) => {
                collect_test_local_refs(terms, fun, refs);
                collect_test_local_refs(terms, arg, refs);
            }
            TestTerm::Lam { ty, body } | TestTerm::Pi { ty, body } => {
                collect_test_local_refs(terms, ty, refs);
                collect_test_local_refs(terms, body, refs);
            }
            TestTerm::Let { ty, value, body } => {
                collect_test_local_refs(terms, ty, refs);
                collect_test_local_refs(terms, value, refs);
                collect_test_local_refs(terms, body, refs);
            }
        }
    }

    fn test_dependencies_for_terms(
        terms: &[TestTerm],
        term_ids: &[usize],
        current_decl_index: usize,
        interface_hashes: &[ReferenceHash],
    ) -> Vec<TestDependencyEntry> {
        let mut refs = BTreeSet::new();
        for term_id in term_ids {
            collect_test_local_refs(terms, *term_id, &mut refs);
        }
        refs.into_iter()
            .filter(|decl_index| *decl_index < current_decl_index)
            .map(|decl_index| TestDependencyEntry {
                decl_index,
                decl_interface_hash: interface_hashes[decl_index],
            })
            .collect()
    }

    fn test_axioms_for_decl(
        declaration: TestDeclSpec,
        decl_index: usize,
        dependencies: &[TestDependencyEntry],
        declarations: &[TestDeclSpec],
        interface_hashes: &[ReferenceHash],
        previous_axioms: &[Vec<TestAxiomRef>],
    ) -> (Vec<TestAxiomRef>, Vec<TestAxiomRef>) {
        let mut direct = BTreeSet::new();
        let mut transitive = BTreeSet::new();
        for dependency in dependencies {
            if matches!(
                declarations[dependency.decl_index],
                TestDeclSpec::Axiom { .. }
            ) {
                direct.insert(TestAxiomRef {
                    decl_index: dependency.decl_index,
                    name: dependency.decl_index,
                    decl_interface_hash: interface_hashes[dependency.decl_index],
                });
            }
            transitive.extend(previous_axioms[dependency.decl_index].iter().copied());
        }
        if matches!(declaration, TestDeclSpec::Axiom { .. }) {
            let self_ref = TestAxiomRef {
                decl_index,
                name: decl_index,
                decl_interface_hash: interface_hashes[decl_index],
            };
            direct.insert(self_ref);
            transitive.insert(self_ref);
        }
        (
            direct.into_iter().collect(),
            transitive.into_iter().collect(),
        )
    }

    fn multi_declaration_certificate_fixture(
        terms: &[TestTerm],
        declarations: &[TestDeclSpec],
    ) -> DeclarationCertificateFixture {
        assert!(declarations
            .windows(2)
            .all(|pair| pair[0].name() < pair[1].name()));
        assert!(declarations
            .last()
            .is_none_or(|declaration| declaration.name() < "Std"));

        let level_hashes = test_level_hashes(terms);
        let term_hashes = test_term_hashes(&level_hashes, terms);
        let mut interface_hashes = Vec::with_capacity(declarations.len());
        let mut certificate_hashes = Vec::with_capacity(declarations.len());
        let mut dependencies_by_decl = Vec::with_capacity(declarations.len());
        let mut direct_axioms_by_decl = Vec::with_capacity(declarations.len());
        let mut transitive_axioms_by_decl = Vec::with_capacity(declarations.len());

        for (decl_index, declaration) in declarations.iter().enumerate() {
            let dependencies = test_dependencies_for_terms(
                terms,
                &test_decl_term_ids(*declaration),
                decl_index,
                &interface_hashes,
            );
            let interface_dependencies = test_dependencies_for_terms(
                terms,
                &test_decl_interface_term_ids(*declaration),
                decl_index,
                &interface_hashes,
            );

            let preliminary_axioms = if matches!(*declaration, TestDeclSpec::Axiom { .. }) {
                (Vec::new(), Vec::new())
            } else {
                test_axioms_for_decl(
                    *declaration,
                    decl_index,
                    &dependencies,
                    declarations,
                    &interface_hashes,
                    &transitive_axioms_by_decl,
                )
            };

            let mut iface_payload = Vec::new();
            match *declaration {
                TestDeclSpec::Axiom { name, ty } => {
                    iface_payload.push(0x00);
                    encode_name(&mut iface_payload, &[name]);
                    encode_usize_vec(&mut iface_payload, &[]);
                    iface_payload.extend(term_hashes[ty]);
                    encode_test_dependency_entries(&mut iface_payload, &interface_dependencies);
                }
                TestDeclSpec::Def {
                    name,
                    ty,
                    value,
                    reducible,
                } => {
                    iface_payload.push(0x01);
                    encode_name(&mut iface_payload, &[name]);
                    encode_usize_vec(&mut iface_payload, &[]);
                    iface_payload.extend(term_hashes[ty]);
                    iface_payload.push(if reducible { 0x00 } else { 0x01 });
                    encode_test_dependency_entries(&mut iface_payload, &interface_dependencies);
                    encode_test_axiom_refs(&mut iface_payload, &preliminary_axioms.1);
                    if reducible {
                        iface_payload.extend(term_hashes[value]);
                    }
                }
                TestDeclSpec::Theorem { name, ty, .. } => {
                    iface_payload.push(0x02);
                    encode_name(&mut iface_payload, &[name]);
                    encode_usize_vec(&mut iface_payload, &[]);
                    iface_payload.extend(term_hashes[ty]);
                    iface_payload.push(0x00);
                    encode_test_dependency_entries(&mut iface_payload, &interface_dependencies);
                    encode_test_axiom_refs(&mut iface_payload, &preliminary_axioms.1);
                }
            }
            let interface_hash = hash_with_domain(b"NPA-DECL-IFACE-0.1", &iface_payload);
            interface_hashes.push(interface_hash);

            let (direct_axioms, transitive_axioms) = test_axioms_for_decl(
                *declaration,
                decl_index,
                &dependencies,
                declarations,
                &interface_hashes,
                &transitive_axioms_by_decl,
            );

            let mut cert_payload = Vec::new();
            cert_payload.extend(interface_hash);
            match *declaration {
                TestDeclSpec::Axiom { .. } => {
                    encode_test_axiom_refs(&mut cert_payload, &transitive_axioms);
                }
                TestDeclSpec::Def { value, .. } => {
                    cert_payload.extend(term_hashes[value]);
                    encode_test_dependency_entries(&mut cert_payload, &dependencies);
                    encode_test_axiom_refs(&mut cert_payload, &transitive_axioms);
                }
                TestDeclSpec::Theorem { proof, .. } => {
                    cert_payload.extend(term_hashes[proof]);
                    encode_test_dependency_entries(&mut cert_payload, &dependencies);
                }
            }
            dependencies_by_decl.push(dependencies);
            direct_axioms_by_decl.push(direct_axioms);
            transitive_axioms_by_decl.push(transitive_axioms);
            certificate_hashes.push(hash_with_domain(b"NPA-DECL-CERT-0.1", &cert_payload));
        }

        let mut bytes = header_bytes();
        bytes.extend(encode_uvar(0)); // imports
        bytes.extend(encode_uvar((declarations.len() + 1) as u64)); // decl names + Std.Nat
        for declaration in declarations {
            encode_name(&mut bytes, &[declaration.name()]);
        }
        encode_name(&mut bytes, &["Std", "Nat"]);
        encode_test_levels(&mut bytes, &level_hashes);
        encode_test_terms(&mut bytes, terms);

        bytes.extend(encode_uvar(declarations.len() as u64));
        for (decl_index, declaration) in declarations.iter().enumerate() {
            match *declaration {
                TestDeclSpec::Axiom { ty, .. } => {
                    bytes.push(0x00);
                    bytes.extend(encode_uvar(decl_index as u64));
                    encode_usize_vec(&mut bytes, &[]);
                    bytes.extend(encode_uvar(ty as u64));
                }
                TestDeclSpec::Def {
                    ty,
                    value,
                    reducible,
                    ..
                } => {
                    bytes.push(0x01);
                    bytes.extend(encode_uvar(decl_index as u64));
                    encode_usize_vec(&mut bytes, &[]);
                    bytes.extend(encode_uvar(ty as u64));
                    bytes.extend(encode_uvar(value as u64));
                    bytes.push(if reducible { 0x00 } else { 0x01 });
                }
                TestDeclSpec::Theorem { ty, proof, .. } => {
                    bytes.push(0x02);
                    bytes.extend(encode_uvar(decl_index as u64));
                    encode_usize_vec(&mut bytes, &[]);
                    bytes.extend(encode_uvar(ty as u64));
                    bytes.extend(encode_uvar(proof as u64));
                    bytes.push(0x00);
                }
            }
            encode_test_dependency_entries(&mut bytes, &dependencies_by_decl[decl_index]);
            encode_test_axiom_refs(&mut bytes, &transitive_axioms_by_decl[decl_index]);
            bytes.extend(interface_hashes[decl_index]);
            bytes.extend(certificate_hashes[decl_index]);
        }

        let mut export_block = Vec::new();
        export_block.extend(encode_uvar(declarations.len() as u64));
        for (decl_index, declaration) in declarations.iter().enumerate() {
            export_block.extend(encode_uvar(decl_index as u64));
            match *declaration {
                TestDeclSpec::Axiom { ty, .. } => {
                    export_block.push(0x00);
                    encode_usize_vec(&mut export_block, &[]);
                    encode_universe_constraints_empty(&mut export_block);
                    export_block.extend(encode_uvar(ty as u64));
                    encode_option_usize(&mut export_block, None);
                    export_block.extend(term_hashes[ty]);
                    encode_option_hash(&mut export_block, None);
                    export_block.push(0x00);
                    export_block.push(0x00);
                }
                TestDeclSpec::Def {
                    ty,
                    value,
                    reducible,
                    ..
                } => {
                    export_block.push(0x01);
                    encode_usize_vec(&mut export_block, &[]);
                    encode_universe_constraints_empty(&mut export_block);
                    export_block.extend(encode_uvar(ty as u64));
                    encode_option_usize(&mut export_block, reducible.then_some(value));
                    export_block.extend(term_hashes[ty]);
                    if reducible {
                        encode_option_hash(&mut export_block, Some(&term_hashes[value]));
                    } else {
                        encode_option_hash(&mut export_block, None);
                    }
                    encode_option_reducibility(&mut export_block, reducible);
                    export_block.push(0x00);
                }
                TestDeclSpec::Theorem { ty, .. } => {
                    export_block.push(0x02);
                    encode_usize_vec(&mut export_block, &[]);
                    encode_universe_constraints_empty(&mut export_block);
                    export_block.extend(encode_uvar(ty as u64));
                    encode_option_usize(&mut export_block, None);
                    export_block.extend(term_hashes[ty]);
                    encode_option_hash(&mut export_block, None);
                    export_block.push(0x00);
                    encode_option_opacity(&mut export_block, true);
                }
            }
            export_block.extend(interface_hashes[decl_index]);
            encode_test_axiom_refs(&mut export_block, &transitive_axioms_by_decl[decl_index]);
        }

        let mut axiom_report = Vec::new();
        axiom_report.extend(encode_uvar(declarations.len() as u64));
        for decl_index in 0..declarations.len() {
            axiom_report.extend(encode_uvar(decl_index as u64));
            encode_test_axiom_refs(&mut axiom_report, &direct_axioms_by_decl[decl_index]);
            encode_test_axiom_refs(&mut axiom_report, &transitive_axioms_by_decl[decl_index]);
        }
        let module_axioms = transitive_axioms_by_decl
            .iter()
            .flat_map(|axioms| axioms.iter().copied())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        encode_test_axiom_refs(&mut axiom_report, &module_axioms);

        bytes.extend(&export_block);
        bytes.extend(&axiom_report);
        let export_hash = hash_with_domain(REFERENCE_MODULE_EXPORT_DOMAIN, &export_block);
        let axiom_report_hash = hash_with_domain(b"NPA-AXIOM-REPORT-0.1", &axiom_report);
        bytes.extend(export_hash);
        bytes.extend(axiom_report_hash);
        let certificate_hash = hash_with_domain(REFERENCE_MODULE_CERT_DOMAIN, &bytes);
        bytes.extend(certificate_hash);

        DeclarationCertificateFixture { bytes }
    }

    fn encode_name_from_table(out: &mut Vec<u8>, names: &[&[&str]], id: usize) {
        encode_name(out, names[id]);
    }

    fn encode_name_id_list_from_table(out: &mut Vec<u8>, names: &[&[&str]], ids: &[usize]) {
        out.extend(encode_uvar(ids.len() as u64));
        for id in ids {
            encode_name_from_table(out, names, *id);
        }
    }

    fn encode_test_binders(out: &mut Vec<u8>, binders: &[usize]) {
        out.extend(encode_uvar(binders.len() as u64));
        for binder in binders {
            out.extend(encode_uvar(*binder as u64));
        }
    }

    fn single_inductive_certificate_fixture(
        terms: &[TestTerm],
        spec: TestInductiveSpec,
    ) -> DeclarationCertificateFixture {
        let mut level_hashes = test_level_hashes(terms);
        while level_hashes.len() <= spec.sort {
            let mut payload = vec![0x01];
            payload.extend(level_hashes.last().unwrap());
            level_hashes.push(hash_with_domain(b"NPA-LEVEL-0.1", &payload));
        }
        let term_hashes = test_term_hashes(&level_hashes, terms);
        let family_type_term = terms
            .iter()
            .position(|term| matches!(term, TestTerm::Sort(level) if *level == spec.sort))
            .expect("single-inductive fixture includes its family sort term");

        let mut recursor_sig_payload = Vec::new();
        let mut recursor_rule_payload = Vec::new();
        match spec.recursor {
            Some(recursor) => {
                recursor_sig_payload.push(0x01);
                encode_name_from_table(&mut recursor_sig_payload, &spec.names, recursor.name);
                encode_name_id_list_from_table(
                    &mut recursor_sig_payload,
                    &spec.names,
                    &spec.universe_params,
                );
                recursor_sig_payload.extend(term_hashes[recursor.ty]);

                recursor_rule_payload.push(0x01);
                recursor_rule_payload.extend(encode_uvar(recursor.minor_start as u64));
                recursor_rule_payload.extend(encode_uvar(recursor.major_index as u64));
            }
            None => {
                recursor_sig_payload.push(0x00);
                recursor_rule_payload.push(0x00);
            }
        }
        let recursor_sig_hash = hash_with_domain(b"NPA-GEN-REC-SIG-0.1", &recursor_sig_payload);
        let recursor_rule_hash = hash_with_domain(b"NPA-GEN-COMP-RULE-0.1", &recursor_rule_payload);

        let mut iface_payload = Vec::new();
        iface_payload.push(0x03);
        encode_name_from_table(&mut iface_payload, &spec.names, spec.name);
        encode_name_id_list_from_table(&mut iface_payload, &spec.names, &spec.universe_params);
        iface_payload.extend(encode_uvar(spec.params.len() as u64));
        for param in &spec.params {
            iface_payload.extend(term_hashes[*param]);
        }
        iface_payload.extend(encode_uvar(spec.indices.len() as u64));
        for index in &spec.indices {
            iface_payload.extend(term_hashes[*index]);
        }
        iface_payload.extend(level_hashes[spec.sort]);
        iface_payload.extend(encode_uvar(spec.constructors.len() as u64));
        for constructor in &spec.constructors {
            encode_name_from_table(&mut iface_payload, &spec.names, constructor.name);
            iface_payload.extend(term_hashes[constructor.ty]);
        }
        iface_payload.extend(recursor_sig_hash);
        iface_payload.extend(recursor_rule_hash);
        encode_dependency_entries_empty(&mut iface_payload);
        encode_axiom_refs_empty(&mut iface_payload);
        let interface_hash = hash_with_domain(b"NPA-DECL-IFACE-0.1", &iface_payload);

        let mut cert_payload = Vec::new();
        cert_payload.extend(interface_hash);
        encode_dependency_entries_empty(&mut cert_payload);
        encode_axiom_refs_empty(&mut cert_payload);
        let certificate_hash = hash_with_domain(b"NPA-DECL-CERT-0.1", &cert_payload);

        let mut bytes = header_bytes();
        bytes.extend(encode_uvar(0)); // imports
        bytes.extend(encode_uvar(spec.names.len() as u64));
        for name in &spec.names {
            encode_name(&mut bytes, name);
        }
        encode_test_levels(&mut bytes, &level_hashes);
        encode_test_terms(&mut bytes, terms);

        bytes.extend(encode_uvar(1)); // declarations
        bytes.push(0x03);
        bytes.extend(encode_uvar(spec.name as u64));
        encode_usize_vec(&mut bytes, &spec.universe_params);
        encode_test_binders(&mut bytes, &spec.params);
        encode_test_binders(&mut bytes, &spec.indices);
        bytes.extend(encode_uvar(spec.sort as u64));
        bytes.extend(encode_uvar(spec.constructors.len() as u64));
        for constructor in &spec.constructors {
            bytes.extend(encode_uvar(constructor.name as u64));
            bytes.extend(encode_uvar(constructor.ty as u64));
        }
        match spec.recursor {
            Some(recursor) => {
                bytes.push(0x01);
                bytes.extend(encode_uvar(recursor.name as u64));
                encode_usize_vec(&mut bytes, &spec.universe_params);
                bytes.extend(encode_uvar(recursor.ty as u64));
                bytes.extend(encode_uvar(recursor.minor_start as u64));
                bytes.extend(encode_uvar(recursor.major_index as u64));
            }
            None => bytes.push(0x00),
        }
        encode_dependency_entries_empty(&mut bytes);
        encode_axiom_refs_empty(&mut bytes);
        bytes.extend(interface_hash);
        bytes.extend(certificate_hash);

        let mut export_block = Vec::new();
        let export_len = 1 + spec.constructors.len() + usize::from(spec.recursor.is_some());
        export_block.extend(encode_uvar(export_len as u64));
        export_block.extend(encode_uvar(spec.name as u64));
        export_block.push(0x03);
        encode_usize_vec(&mut export_block, &spec.universe_params);
        encode_universe_constraints_empty(&mut export_block);
        export_block.extend(encode_uvar(family_type_term as u64));
        encode_option_usize(&mut export_block, None);
        export_block.extend(term_hashes[family_type_term]);
        encode_option_hash(&mut export_block, None);
        export_block.push(0x00);
        export_block.push(0x00);
        export_block.extend(interface_hash);
        encode_axiom_refs_empty(&mut export_block);
        for constructor in &spec.constructors {
            export_block.extend(encode_uvar(constructor.name as u64));
            export_block.push(0x04);
            encode_usize_vec(&mut export_block, &spec.universe_params);
            encode_universe_constraints_empty(&mut export_block);
            export_block.extend(encode_uvar(constructor.ty as u64));
            encode_option_usize(&mut export_block, None);
            export_block.extend(term_hashes[constructor.ty]);
            encode_option_hash(&mut export_block, None);
            export_block.push(0x00);
            export_block.push(0x00);
            export_block.extend(interface_hash);
            encode_axiom_refs_empty(&mut export_block);
        }
        if let Some(recursor) = spec.recursor {
            export_block.extend(encode_uvar(recursor.name as u64));
            export_block.push(0x05);
            encode_usize_vec(&mut export_block, &spec.universe_params);
            encode_universe_constraints_empty(&mut export_block);
            export_block.extend(encode_uvar(recursor.ty as u64));
            encode_option_usize(&mut export_block, None);
            export_block.extend(term_hashes[recursor.ty]);
            encode_option_hash(&mut export_block, None);
            export_block.push(0x00);
            export_block.push(0x00);
            export_block.extend(interface_hash);
            encode_axiom_refs_empty(&mut export_block);
        }

        let mut axiom_report = Vec::new();
        axiom_report.extend(encode_uvar(1));
        axiom_report.extend(encode_uvar(0)); // decl index
        encode_axiom_refs_empty(&mut axiom_report);
        encode_axiom_refs_empty(&mut axiom_report);
        encode_axiom_refs_empty(&mut axiom_report);

        bytes.extend(&export_block);
        bytes.extend(&axiom_report);
        let export_hash = hash_with_domain(REFERENCE_MODULE_EXPORT_DOMAIN, &export_block);
        let axiom_report_hash = hash_with_domain(b"NPA-AXIOM-REPORT-0.1", &axiom_report);
        bytes.extend(export_hash);
        bytes.extend(axiom_report_hash);
        let certificate_hash = hash_with_domain(REFERENCE_MODULE_CERT_DOMAIN, &bytes);
        bytes.extend(certificate_hash);

        DeclarationCertificateFixture { bytes }
    }

    fn local_const_certificate_fixture() -> DeclarationCertificateFixture {
        let terms = [TestTerm::Sort(0), TestTerm::ConstLocal { decl_index: 0 }];
        multi_declaration_certificate_fixture(
            &terms,
            &[
                TestDeclSpec::Axiom { name: "A", ty: 0 },
                TestDeclSpec::Theorem {
                    name: "B",
                    ty: 0,
                    proof: 1,
                },
            ],
        )
    }

    fn well_typed_identity_terms() -> Vec<TestTerm> {
        vec![
            TestTerm::Sort(0),
            TestTerm::BVar(0),
            TestTerm::BVar(1),
            TestTerm::Lam { ty: 1, body: 1 },
            TestTerm::Pi { ty: 1, body: 2 },
            TestTerm::Lam { ty: 0, body: 3 },
            TestTerm::Pi { ty: 0, body: 4 },
        ]
    }

    fn identity_type_only_terms() -> Vec<TestTerm> {
        vec![
            TestTerm::Sort(0),
            TestTerm::BVar(0),
            TestTerm::BVar(1),
            TestTerm::Pi { ty: 1, body: 2 },
            TestTerm::Pi { ty: 0, body: 3 },
        ]
    }

    #[derive(Clone, Debug)]
    struct AxiomCertificateFixture {
        bytes: Vec<u8>,
        decl_interface_hash_offset: usize,
        decl_certificate_hash_offset: usize,
        export_hash_offset: usize,
        axiom_report_hash_offset: usize,
        certificate_hash_offset: usize,
        export_hash: ReferenceHash,
        axiom_report_hash: ReferenceHash,
        certificate_hash: ReferenceHash,
    }

    fn axiom_certificate_fixture() -> AxiomCertificateFixture {
        axiom_certificate_fixture_with_axiom_dependencies(true)
    }

    fn axiom_certificate_fixture_with_axiom_dependencies(
        include_self_axiom: bool,
    ) -> AxiomCertificateFixture {
        named_axiom_certificate_fixture(&["Std", "Nat"], &["A"], include_self_axiom)
    }

    fn named_axiom_certificate_fixture(
        module: &[&str],
        axiom_name: &[&str],
        include_self_axiom: bool,
    ) -> AxiomCertificateFixture {
        assert!(axiom_name < module);

        let mut bytes = header_bytes_for(module);
        bytes.extend(encode_uvar(0)); // imports
        bytes.extend(encode_uvar(2)); // name table: axiom, module
        encode_name(&mut bytes, axiom_name);
        encode_name(&mut bytes, module);

        bytes.extend(encode_uvar(1)); // level table
        bytes.push(0x00); // Zero

        let level_hash = hash_with_domain(b"NPA-LEVEL-0.1", &[0x00]);
        let mut term_payload = Vec::new();
        term_payload.push(0x00); // Sort
        term_payload.extend(level_hash);
        let term_hash = hash_with_domain(b"NPA-TERM-0.1", &term_payload);

        bytes.extend(encode_uvar(1)); // term table
        bytes.push(0x00); // Sort
        bytes.extend(encode_uvar(0)); // level 0

        let mut iface_payload = Vec::new();
        iface_payload.push(0x00); // Axiom
        encode_name(&mut iface_payload, axiom_name);
        encode_usize_vec(&mut iface_payload, &[]);
        iface_payload.extend(term_hash);
        encode_dependency_entries_empty(&mut iface_payload);
        let decl_interface_hash = hash_with_domain(b"NPA-DECL-IFACE-0.1", &iface_payload);

        bytes.extend(encode_uvar(1)); // declarations
        bytes.push(0x00); // Axiom
        bytes.extend(encode_uvar(0)); // name A
        encode_usize_vec(&mut bytes, &[]); // universe params
        bytes.extend(encode_uvar(0)); // ty term
        encode_dependency_entries_empty(&mut bytes);
        encode_axiom_refs_optional_self(&mut bytes, include_self_axiom, &decl_interface_hash);

        let mut decl_cert_payload = Vec::new();
        decl_cert_payload.extend(decl_interface_hash);
        encode_axiom_refs_optional_self(
            &mut decl_cert_payload,
            include_self_axiom,
            &decl_interface_hash,
        );
        let decl_certificate_hash = hash_with_domain(b"NPA-DECL-CERT-0.1", &decl_cert_payload);

        let decl_interface_hash_offset = bytes.len();
        bytes.extend(decl_interface_hash);
        let decl_certificate_hash_offset = bytes.len();
        bytes.extend(decl_certificate_hash);

        let mut export_block = Vec::new();
        export_block.extend(encode_uvar(1));
        export_block.extend(encode_uvar(0)); // name A
        export_block.push(0x00); // Axiom export
        encode_usize_vec(&mut export_block, &[]);
        encode_universe_constraints_empty(&mut export_block);
        export_block.extend(encode_uvar(0)); // ty term
        encode_option_usize(&mut export_block, None);
        export_block.extend(term_hash);
        encode_option_hash(&mut export_block, None);
        export_block.push(0x00); // no reducibility
        export_block.push(0x00); // no opacity
        export_block.extend(decl_interface_hash);
        encode_axiom_refs_optional_self(
            &mut export_block,
            include_self_axiom,
            &decl_interface_hash,
        );

        let mut axiom_report = Vec::new();
        axiom_report.extend(encode_uvar(1));
        axiom_report.extend(encode_uvar(0)); // decl index
        encode_axiom_refs_optional_self(
            &mut axiom_report,
            include_self_axiom,
            &decl_interface_hash,
        );
        encode_axiom_refs_optional_self(
            &mut axiom_report,
            include_self_axiom,
            &decl_interface_hash,
        );
        encode_axiom_refs_optional_self(
            &mut axiom_report,
            include_self_axiom,
            &decl_interface_hash,
        ); // module axioms

        bytes.extend(&export_block);
        bytes.extend(&axiom_report);

        let export_hash = hash_with_domain(REFERENCE_MODULE_EXPORT_DOMAIN, &export_block);
        let axiom_report_hash = hash_with_domain(b"NPA-AXIOM-REPORT-0.1", &axiom_report);
        let export_hash_offset = bytes.len();
        bytes.extend(export_hash);
        let axiom_report_hash_offset = bytes.len();
        bytes.extend(axiom_report_hash);
        let certificate_hash_offset = bytes.len();
        let certificate_hash = hash_with_domain(REFERENCE_MODULE_CERT_DOMAIN, &bytes);
        bytes.extend(certificate_hash);

        AxiomCertificateFixture {
            bytes,
            decl_interface_hash_offset,
            decl_certificate_hash_offset,
            export_hash_offset,
            axiom_report_hash_offset,
            certificate_hash_offset,
            export_hash,
            axiom_report_hash,
            certificate_hash,
        }
    }

    fn assert_hash_mismatch(
        error: ReferenceCheckError,
        section: ReferenceCertificateSection,
        offset: usize,
        object: ReferenceHashObject,
    ) {
        assert_eq!(error.kind, ReferenceCheckErrorKind::HashMismatch);
        assert_eq!(error.section, section);
        assert_eq!(error.offset, offset);
        assert_eq!(
            error.reason,
            Some(ReferenceCheckReason::HashMismatch { object })
        );
    }

    fn assert_import_resolution(error: ReferenceCheckError, reason: ReferenceCheckReason) {
        assert_eq!(error.kind, ReferenceCheckErrorKind::ImportResolution);
        assert_eq!(error.section, ReferenceCertificateSection::Imports);
        assert_eq!(error.reason, Some(reason));
    }

    fn assert_type_check(error: ReferenceCheckError, reason: ReferenceCheckReason) {
        assert_eq!(error.kind, ReferenceCheckErrorKind::TypeCheck, "{error:?}");
        assert_eq!(
            error.section,
            ReferenceCertificateSection::Declarations,
            "{error:?}"
        );
        assert_eq!(error.reason, Some(reason), "{error:?}");
    }

    fn assert_axiom_report_mismatch(error: ReferenceCheckError) {
        assert_eq!(
            error.kind,
            ReferenceCheckErrorKind::AxiomReportMismatch,
            "{error:?}"
        );
        assert_eq!(
            error.reason,
            Some(ReferenceCheckReason::AxiomReportMismatch),
            "{error:?}"
        );
    }

    fn assert_axiom_policy(error: ReferenceCheckError, reason: ReferenceCheckReason) {
        assert_eq!(
            error.kind,
            ReferenceCheckErrorKind::AxiomPolicy,
            "{error:?}"
        );
        assert_eq!(error.reason, Some(reason), "{error:?}");
    }

    fn diagnostic_name(value: &str) -> ReferenceModuleName {
        ReferenceModuleName::from_dotted(value).unwrap()
    }

    #[test]
    fn unknown_reference_constructor_preserves_every_reference_lane() {
        let owner = ReferenceCheckResolvedImportIdentity {
            import_index: 2,
            module: diagnostic_name("Owner.Module"),
            export_hash: [0x22; 32],
        };
        let target = ReferenceCheckResolvedImportIdentity {
            import_index: 1,
            module: diagnostic_name("Target.Module"),
            export_hash: [0x11; 32],
        };
        let contexts = vec![
            ReferenceCheckReference::Builtin {
                declaration: diagnostic_name("Eq.refl"),
                decl_interface_hash: [0x01; 32],
            },
            ReferenceCheckReference::Imported {
                owner_import: None,
                import: ReferenceCheckImportTarget::Resolved(target.clone()),
                declaration: diagnostic_name("Target.Module.value"),
                decl_interface_hash: [0x02; 32],
            },
            ReferenceCheckReference::Imported {
                owner_import: Some(owner.clone()),
                import: ReferenceCheckImportTarget::Unresolved { import_index: 7 },
                declaration: diagnostic_name("Nested.missing"),
                decl_interface_hash: [0x03; 32],
            },
            ReferenceCheckReference::Local {
                owner_import: None,
                declaration_index: 4,
                declaration: Some(diagnostic_name("Current.local")),
            },
            ReferenceCheckReference::LocalGenerated {
                owner_import: None,
                declaration_index: 5,
                declaration: diagnostic_name("Current.generated"),
            },
            ReferenceCheckReference::Local {
                owner_import: Some(owner.clone()),
                declaration_index: 6,
                declaration: None,
            },
            ReferenceCheckReference::LocalGenerated {
                owner_import: Some(owner),
                declaration_index: 8,
                declaration: diagnostic_name("Imported.generated"),
            },
        ];

        for context in contexts {
            let error = ReferenceCheckError::unknown_reference(
                ReferenceCertificateSection::Declarations,
                37,
                context.clone(),
            );
            assert_eq!(error.kind, ReferenceCheckErrorKind::TypeCheck);
            assert_eq!(error.reason, Some(ReferenceCheckReason::UnknownReference));
            assert_eq!(error.section, ReferenceCertificateSection::Declarations);
            assert_eq!(error.offset, 37);
            assert_eq!(error.reference, Some(context));
        }
    }

    #[test]
    fn unknown_reference_context_disambiguates_the_same_offset() {
        let local = ReferenceCheckError::unknown_reference(
            ReferenceCertificateSection::Declarations,
            91,
            ReferenceCheckReference::Local {
                owner_import: None,
                declaration_index: 0,
                declaration: Some(diagnostic_name("Current.local")),
            },
        );
        let imported = ReferenceCheckError::unknown_reference(
            ReferenceCertificateSection::Declarations,
            91,
            ReferenceCheckReference::Imported {
                owner_import: None,
                import: ReferenceCheckImportTarget::Unresolved { import_index: 0 },
                declaration: diagnostic_name("Imported.missing"),
                decl_interface_hash: [0x44; 32],
            },
        );

        assert_eq!(local.offset, imported.offset);
        assert_ne!(local.reference, imported.reference);
    }

    #[test]
    fn unknown_reference_call_site_inventory_preserves_universe_exceptions() {
        let source = include_str!("decode.rs");
        let production_source = source
            .split_once("#[cfg(test)]")
            .map(|(production_source, _)| production_source)
            .expect("decode tests remain separated from production code");
        assert_eq!(
            production_source
                .matches("ReferenceCheckError::unknown_reference(")
                .count(),
            14
        );
        assert_eq!(
            production_source
                .matches("ReferenceCheckReason::UnknownReference")
                .count(),
            2
        );

        let universe_error = ReferenceCheckError::type_check(
            ReferenceCertificateSection::Declarations,
            13,
            ReferenceCheckReason::UnknownReference,
        );
        assert_eq!(universe_error.reference, None);
    }

    #[test]
    fn public_api_is_certificate_bytes_import_store_and_policy_only() {
        let _: fn(&[u8], &ReferenceImportStore, &ReferenceCheckerPolicy) -> ReferenceCheckResult =
            check_certificate;
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();

        let result = check_certificate(&[], &imports, &policy);

        assert_eq!(
            result,
            ReferenceCheckResult::Rejected(ReferenceCheckError {
                kind: ReferenceCheckErrorKind::EmptyCertificate,
                section: ReferenceCertificateSection::HeaderFormat,
                offset: 0,
                reason: None,
                reference: None,
            })
        );
    }

    #[test]
    fn empty_certificate_returns_deterministic_structured_error() {
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();

        let first = check_certificate(&[], &imports, &policy);
        let second = check_certificate(&[], &imports, &policy);

        assert_eq!(first, second);
        assert_eq!(
            first.error().unwrap().kind,
            ReferenceCheckErrorKind::EmptyCertificate
        );
    }

    #[test]
    fn malformed_certificate_returns_deterministic_structured_error() {
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();
        let malformed = [0x00];

        let result = check_certificate(&malformed, &imports, &policy);

        assert_eq!(
            result,
            ReferenceCheckResult::Rejected(ReferenceCheckError {
                kind: ReferenceCheckErrorKind::MalformedCertificate,
                section: ReferenceCertificateSection::HeaderFormat,
                offset: 1,
                reason: Some(ReferenceCheckReason::FormatMismatch),
                reference: None,
            })
        );
    }

    #[test]
    fn empty_module_certificate_is_checked_after_type_check() {
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();
        let cert = empty_module_certificate();

        let result = check_certificate(&cert, &imports, &policy);

        assert!(result.is_checked());
    }

    #[test]
    fn decode_valid_golden_certificate_without_source_sections() {
        let cert = empty_module_certificate();

        let decoded = decode_certificate(&cert).expect("minimal canonical certificate decodes");

        assert_eq!(decoded.header().format, REFERENCE_CERTIFICATE_FORMAT);
        assert_eq!(decoded.header().core_spec, REFERENCE_CORE_SPEC);
        assert_eq!(decoded.header().module.dotted(), "Std.Nat");
        assert_eq!(decoded.imports_len(), 0);
        assert_eq!(decoded.name_table_len(), 1);
        assert_eq!(decoded.level_table_len(), 0);
        assert_eq!(decoded.term_table_len(), 0);
        assert_eq!(decoded.declarations_len(), 0);
        assert_eq!(decoded.export_block_len(), 0);
        assert_ne!(decoded.hashes().certificate_hash, [0; 32]);
    }

    #[test]
    fn verify_hashes_accepts_legacy_empty_public_exports() {
        let cert = legacy_empty_module_certificate();

        let decoded = verify_certificate_hashes(&cert).expect("legacy empty export verifies");

        assert_eq!(decoded.header().format, REFERENCE_LEGACY_CERTIFICATE_FORMAT);
        assert_eq!(decoded.header().core_spec, REFERENCE_LEGACY_CORE_SPEC);
        assert_eq!(decoded.header().module.dotted(), "Std.Nat");
        assert_eq!(decoded.export_block_len(), 0);
        assert_ne!(decoded.hashes().certificate_hash, [0; 32]);
    }

    #[test]
    fn verify_hashes_accepts_previous_empty_public_exports() {
        let cert = previous_empty_module_certificate();

        let decoded = verify_certificate_hashes(&cert).expect("previous empty export verifies");

        assert_eq!(
            decoded.header().format,
            REFERENCE_PREVIOUS_CERTIFICATE_FORMAT
        );
        assert_eq!(decoded.header().core_spec, REFERENCE_PREVIOUS_CORE_SPEC);
        assert_eq!(decoded.header().module.dotted(), "Std.Nat");
        assert_eq!(decoded.export_block_len(), 0);
        assert_ne!(decoded.hashes().certificate_hash, [0; 32]);
    }

    #[test]
    fn verify_hashes_accepts_current_constrained_public_exports() {
        let cert = constrained_axiom_certificate();

        let decoded = verify_certificate_hashes(&cert).expect("constrained export verifies");

        assert_eq!(decoded.header().format, REFERENCE_CERTIFICATE_FORMAT);
        assert_eq!(decoded.header().core_spec, REFERENCE_CORE_SPEC);
        assert_eq!(decoded.header().module.dotted(), "Test.UniverseConstraints");
        assert_eq!(decoded.export_block_len(), 1);
        assert_ne!(decoded.hashes().export_hash, [0; 32]);
    }

    #[test]
    fn verify_hashes_rejects_legacy_constrained_public_exports() {
        let cert = build_module_cert(
            CoreModule {
                name: Name::from_dotted("Test.UniverseConstraints"),
                declarations: vec![Decl::AxiomConstrained {
                    name: "List.map".to_owned(),
                    universe_params: vec!["u".to_owned(), "v".to_owned(), "w".to_owned()],
                    universe_constraints: vec![UniverseConstraint::le(
                        Level::max(Level::param("u"), Level::param("v")),
                        Level::param("w"),
                    )],
                    ty: Expr::sort(Level::param("w")),
                }],
            },
            &[],
        )
        .unwrap();
        let legacy = legacy_bytes_from_npa_cert(cert);

        let error =
            verify_certificate_hashes(&legacy).expect_err("legacy constrained export rejects");

        assert_eq!(error.kind, ReferenceCheckErrorKind::MalformedCertificate);
        assert_eq!(error.section, ReferenceCertificateSection::ExportBlock);
        assert_eq!(
            error.reason,
            Some(ReferenceCheckReason::ConstrainedExportRequiresFormatUpgrade)
        );
    }

    #[test]
    fn hash_verifier_accepts_golden_axiom_certificate_without_source_sections() {
        let fixture = axiom_certificate_fixture();

        let verified =
            verify_certificate_hashes(&fixture.bytes).expect("golden axiom certificate verifies");

        assert_eq!(verified.header().module.dotted(), "Std.Nat");
        assert_eq!(verified.declarations_len(), 1);
        assert_eq!(verified.hashes().export_hash, fixture.export_hash);
        assert_eq!(
            verified.hashes().axiom_report_hash,
            fixture.axiom_report_hash
        );
        assert_eq!(verified.hashes().certificate_hash, fixture.certificate_hash);
    }

    #[test]
    fn hash_verifier_rejects_decl_interface_hash_mismatch_by_object() {
        let fixture = axiom_certificate_fixture();
        let mut cert = fixture.bytes;
        cert[fixture.decl_interface_hash_offset] ^= 0x01;

        let error =
            verify_certificate_hashes(&cert).expect_err("decl interface hash mismatch rejects");

        assert_hash_mismatch(
            error,
            ReferenceCertificateSection::Declarations,
            fixture.decl_interface_hash_offset,
            ReferenceHashObject::DeclInterface,
        );
    }

    #[test]
    fn hash_verifier_rejects_decl_certificate_hash_mismatch_by_object() {
        let fixture = axiom_certificate_fixture_with_axiom_dependencies(false);
        let mut cert = fixture.bytes;
        cert[fixture.decl_certificate_hash_offset] ^= 0x01;

        let error =
            verify_certificate_hashes(&cert).expect_err("decl certificate hash mismatch rejects");

        assert_hash_mismatch(
            error,
            ReferenceCertificateSection::Declarations,
            fixture.decl_certificate_hash_offset,
            ReferenceHashObject::DeclCertificate,
        );
    }

    #[test]
    fn hash_verifier_classifies_dependency_material_hash_mismatch() {
        let fixture = axiom_certificate_fixture_with_axiom_dependencies(true);
        let mut cert = fixture.bytes;
        cert[fixture.decl_certificate_hash_offset] ^= 0x01;

        let error = verify_certificate_hashes(&cert)
            .expect_err("dependency-bearing declaration certificate hash mismatch rejects");

        assert_hash_mismatch(
            error,
            ReferenceCertificateSection::Declarations,
            fixture.decl_certificate_hash_offset,
            ReferenceHashObject::DeclCertificateDependencyMaterial,
        );
    }

    #[test]
    fn hash_verifier_rejects_export_hash_mismatch_by_object() {
        let fixture = axiom_certificate_fixture();
        let mut cert = fixture.bytes;
        cert[fixture.export_hash_offset] ^= 0x01;

        let error = verify_certificate_hashes(&cert).expect_err("export hash mismatch rejects");

        assert_hash_mismatch(
            error,
            ReferenceCertificateSection::Hashes,
            fixture.export_hash_offset,
            ReferenceHashObject::ExportBlock,
        );
    }

    #[test]
    fn hash_verifier_rejects_axiom_report_hash_mismatch_by_object() {
        let fixture = axiom_certificate_fixture();
        let mut cert = fixture.bytes;
        cert[fixture.axiom_report_hash_offset] ^= 0x01;

        let error =
            verify_certificate_hashes(&cert).expect_err("axiom report hash mismatch rejects");

        assert_hash_mismatch(
            error,
            ReferenceCertificateSection::Hashes,
            fixture.axiom_report_hash_offset,
            ReferenceHashObject::AxiomReport,
        );
    }

    #[test]
    fn hash_verifier_rejects_certificate_hash_mismatch_by_object() {
        let fixture = axiom_certificate_fixture();
        let mut cert = fixture.bytes;
        cert[fixture.certificate_hash_offset] ^= 0x01;

        let error =
            verify_certificate_hashes(&cert).expect_err("certificate hash mismatch rejects");

        assert_hash_mismatch(
            error,
            ReferenceCertificateSection::Hashes,
            fixture.certificate_hash_offset,
            ReferenceHashObject::ModuleCertificate,
        );
    }

    #[test]
    fn check_certificate_runs_hash_verifier_before_type_check() {
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();
        let fixture = axiom_certificate_fixture();
        let mut cert = fixture.bytes;
        cert[fixture.certificate_hash_offset] ^= 0x01;

        let result = check_certificate(&cert, &imports, &policy);

        assert_hash_mismatch(
            result.error().unwrap().clone(),
            ReferenceCertificateSection::Hashes,
            fixture.certificate_hash_offset,
            ReferenceHashObject::ModuleCertificate,
        );
    }

    #[test]
    fn axiom_report_rejects_certificate_missing_actual_dependency() {
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();
        let fixture = axiom_certificate_fixture_with_axiom_dependencies(false);

        let result = check_certificate(&fixture.bytes, &imports, &policy);

        assert_axiom_report_mismatch(result.error().unwrap().clone());
    }

    #[test]
    fn axiom_report_accepts_recomputed_self_dependency_in_normal_mode() {
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();
        let fixture = axiom_certificate_fixture_with_axiom_dependencies(true);

        let result = check_certificate(&fixture.bytes, &imports, &policy);

        assert!(result.is_checked(), "{result:?}");
    }

    #[test]
    fn axiom_policy_rejects_custom_axiom_in_high_trust_mode() {
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy {
            trust_mode: ReferenceTrustMode::HighTrust,
            ..ReferenceCheckerPolicy::default()
        };
        let fixture = axiom_certificate_fixture_with_axiom_dependencies(true);

        let result = check_certificate(&fixture.bytes, &imports, &policy);

        assert_axiom_policy(
            result.error().unwrap().clone(),
            ReferenceCheckReason::ForbiddenAxiom,
        );
    }

    #[test]
    fn check_observation_survives_rejection_after_decode() {
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy {
            trust_mode: ReferenceTrustMode::HighTrust,
            ..ReferenceCheckerPolicy::default()
        };
        let fixture = axiom_certificate_fixture_with_axiom_dependencies(true);

        let (result, observation) =
            check_certificate_with_observation(&fixture.bytes, &imports, &policy, 1);

        assert_eq!(result, check_certificate(&fixture.bytes, &imports, &policy));
        assert!(!result.is_checked());
        assert!(observation.certificate_decoded);
        assert_eq!(observation.declaration_count, 1);
        assert_eq!(observation.declarations.len(), 1);
        assert_eq!(observation.declarations[0].declaration_index, 0);
        assert!(observation.declarations[0].term_nodes > 0);

        let (_, count_only) =
            check_certificate_with_observation(&fixture.bytes, &imports, &policy, 0);
        assert!(count_only.certificate_decoded);
        assert_eq!(count_only.declaration_count, 1);
        assert!(count_only.declarations.is_empty());

        let (empty, empty_observation) =
            check_certificate_with_observation(&[], &imports, &policy, 1);
        assert!(!empty.is_checked());
        assert!(!empty_observation.certificate_decoded);
        assert_eq!(empty_observation.declaration_count, 0);
        assert!(empty_observation.declarations.is_empty());
    }

    #[test]
    fn axiom_policy_rechecks_checked_import_axioms_at_checker_boundary() {
        let fixture = axiom_certificate_fixture_with_axiom_dependencies(true);
        let unchecked_store =
            ReferenceImportStore::from_source_free_certificates([fixture.bytes.as_slice()])
                .expect("source-free import store builds");
        let checked =
            ReferenceCheckedModule::from_import_entry(unchecked_store.entries()[0].clone());
        let imports =
            ReferenceImportStore::from_checked_modules([checked]).expect("checked store builds");
        let policy = ReferenceCheckerPolicy {
            trust_mode: ReferenceTrustMode::HighTrust,
            ..ReferenceCheckerPolicy::default()
        };
        let cert = empty_module_certificate_importing_std_nat(
            fixture.export_hash,
            Some(fixture.certificate_hash),
        );

        let result = check_certificate(&cert, &imports, &policy);

        assert_axiom_policy(
            result.error().unwrap().clone(),
            ReferenceCheckReason::ForbiddenAxiom,
        );
    }

    #[test]
    fn axiom_policy_rejects_synthetic_sorry_before_custom_axiom_gate() {
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy {
            trust_mode: ReferenceTrustMode::HighTrust,
            ..ReferenceCheckerPolicy::default()
        };
        let fixture = named_axiom_certificate_fixture(&["Std", "Nat"], &["A", "sorry"], true);

        let result = check_certificate(&fixture.bytes, &imports, &policy);

        assert_axiom_policy(
            result.error().unwrap().clone(),
            ReferenceCheckReason::SorryDenied,
        );
    }

    #[test]
    fn axiom_policy_allows_exact_std_logic_eq_rec_exception() {
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy {
            trust_mode: ReferenceTrustMode::HighTrust,
            ..ReferenceCheckerPolicy::default()
        };
        let fixture = named_axiom_certificate_fixture(&["Std", "Logic"], &["Eq", "rec"], true);

        let result = check_certificate(&fixture.bytes, &imports, &policy);

        assert!(result.is_checked(), "{result:?}");
    }

    #[test]
    fn axiom_policy_rejects_non_eq_rec_classical_axiom() {
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy {
            trust_mode: ReferenceTrustMode::HighTrust,
            ..ReferenceCheckerPolicy::default()
        };
        let fixture =
            named_axiom_certificate_fixture(&["Std", "Logic"], &["Classical", "choice"], true);

        let result = check_certificate(&fixture.bytes, &imports, &policy);

        assert_axiom_policy(
            result.error().unwrap().clone(),
            ReferenceCheckReason::ForbiddenAxiom,
        );
    }

    #[test]
    fn type_check_accepts_well_typed_reducible_def() {
        let terms = well_typed_identity_terms();
        let fixture = declaration_certificate_fixture(
            &["Adef"],
            &terms,
            TestDeclKind::ReducibleDef { ty: 6, value: 5 },
        );
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();

        let result = check_certificate(&fixture.bytes, &imports, &policy);

        let ReferenceCheckResult::Checked(module) = result else {
            panic!("well-typed def should check");
        };
        assert_eq!(module.module().dotted(), "Std.Nat");
        assert_eq!(module.public_environment().exports().len(), 1);
        assert!(module.public_environment().exports()[0].body.is_some());
    }

    #[test]
    fn type_check_accepts_well_typed_theorem_and_keeps_proof_opaque() {
        let terms = well_typed_identity_terms();
        let fixture = declaration_certificate_fixture(
            &["Athm"],
            &terms,
            TestDeclKind::Theorem { ty: 6, proof: 5 },
        );
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();

        let result = check_certificate(&fixture.bytes, &imports, &policy);

        let ReferenceCheckResult::Checked(module) = result else {
            panic!("well-typed theorem should check");
        };
        let export = &module.public_environment().exports()[0];
        assert_eq!(export.kind, ReferenceExportKind::Theorem);
        assert!(export.body.is_none());
    }

    #[test]
    fn smt_reconstructed_npa_proof_certificate_checks_source_free() {
        let module = npa_cert::CoreModule {
            name: npa_cert::Name::from_dotted("Smt.Ref"),
            declarations: vec![
                Decl::Axiom {
                    name: "Smt.Ref.P".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::sort(Level::zero()),
                },
                Decl::Axiom {
                    name: "Smt.Ref.proof".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::konst("Smt.Ref.P", vec![]),
                },
                Decl::Theorem {
                    name: "Smt.Ref.goal".to_owned(),
                    universe_params: Vec::new(),
                    ty: Expr::konst("Smt.Ref.P", vec![]),
                    proof: Expr::konst("Smt.Ref.proof", vec![]),
                },
            ],
        };
        let cert = npa_cert::build_module_cert(module, &[]).unwrap();
        let bytes = npa_cert::encode_module_cert(&cert).unwrap();

        let result = check_certificate(
            &bytes,
            &ReferenceImportStore::default(),
            &ReferenceCheckerPolicy::default(),
        );

        assert!(
            result.is_checked(),
            "reference checker must accept the source-free NPA proof term used after SMT reconstruction"
        );
    }

    #[test]
    fn type_check_accepts_let_term() {
        let terms = [
            TestTerm::Sort(0),
            TestTerm::Sort(1),
            TestTerm::BVar(0),
            TestTerm::Let {
                ty: 1,
                value: 0,
                body: 2,
            },
        ];
        let fixture = declaration_certificate_fixture(
            &["Alet"],
            &terms,
            TestDeclKind::Theorem { ty: 1, proof: 3 },
        );
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();

        let result = check_certificate(&fixture.bytes, &imports, &policy);

        assert!(result.is_checked());
    }

    #[test]
    fn type_check_accepts_local_const_reference_after_prior_declaration() {
        let fixture = local_const_certificate_fixture();
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();

        let result = check_certificate(&fixture.bytes, &imports, &policy);

        let ReferenceCheckResult::Checked(module) = result else {
            panic!("local const reference should check after its declaration");
        };
        assert_eq!(module.public_environment().exports().len(), 2);
    }

    #[test]
    fn type_check_rejects_ill_typed_application() {
        let terms = [TestTerm::Sort(0), TestTerm::App(0, 0)];
        let fixture = declaration_certificate_fixture(
            &["Abad"],
            &terms,
            TestDeclKind::Theorem { ty: 0, proof: 1 },
        );
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();

        let result = check_certificate(&fixture.bytes, &imports, &policy);

        assert_type_check(
            result.error().unwrap().clone(),
            ReferenceCheckReason::ExpectedFunction,
        );
    }

    #[test]
    fn type_check_rejects_wrong_theorem_proof_type() {
        let terms = identity_type_only_terms();
        let fixture = declaration_certificate_fixture(
            &["Awrong"],
            &terms,
            TestDeclKind::Theorem { ty: 4, proof: 0 },
        );
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();

        let result = check_certificate(&fixture.bytes, &imports, &policy);

        assert_type_check(
            result.error().unwrap().clone(),
            ReferenceCheckReason::TypeMismatch,
        );
    }

    #[test]
    fn type_check_rejects_de_bruijn_index_out_of_scope() {
        let terms = [TestTerm::Sort(0), TestTerm::BVar(0)];
        let fixture = declaration_certificate_fixture(
            &["Ascope"],
            &terms,
            TestDeclKind::Theorem { ty: 0, proof: 1 },
        );
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();

        let result = check_certificate(&fixture.bytes, &imports, &policy);

        assert_type_check(
            result.error().unwrap().clone(),
            ReferenceCheckReason::InvalidBVar,
        );
    }

    #[test]
    fn conversion_accepts_beta_reduced_expected_type() {
        let terms = [
            TestTerm::Sort(0),
            TestTerm::Sort(1),
            TestTerm::BVar(0),
            TestTerm::ConstLocal { decl_index: 0 },
            TestTerm::Lam { ty: 1, body: 2 },
            TestTerm::App(4, 0),
        ];
        let fixture = multi_declaration_certificate_fixture(
            &terms,
            &[
                TestDeclSpec::Axiom { name: "A", ty: 0 },
                TestDeclSpec::Theorem {
                    name: "B",
                    ty: 5,
                    proof: 3,
                },
            ],
        );
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();

        let result = check_certificate(&fixture.bytes, &imports, &policy);

        assert!(result.is_checked());
    }

    #[test]
    fn conversion_rejects_beta_reduced_type_mismatch() {
        let terms = [
            TestTerm::Sort(0),
            TestTerm::Sort(1),
            TestTerm::BVar(0),
            TestTerm::Lam { ty: 1, body: 2 },
            TestTerm::App(3, 0),
        ];
        let fixture = multi_declaration_certificate_fixture(
            &terms,
            &[TestDeclSpec::Theorem {
                name: "A",
                ty: 4,
                proof: 0,
            }],
        );
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();

        let result = check_certificate(&fixture.bytes, &imports, &policy);

        assert_type_check(
            result.error().unwrap().clone(),
            ReferenceCheckReason::TypeMismatch,
        );
    }

    #[test]
    fn conversion_accepts_reducible_delta_expected_type() {
        let terms = [
            TestTerm::Sort(0),
            TestTerm::Sort(1),
            TestTerm::ConstLocal { decl_index: 0 },
            TestTerm::ConstLocal { decl_index: 1 },
        ];
        let fixture = multi_declaration_certificate_fixture(
            &terms,
            &[
                TestDeclSpec::Def {
                    name: "A",
                    ty: 1,
                    value: 0,
                    reducible: true,
                },
                TestDeclSpec::Axiom { name: "B", ty: 0 },
                TestDeclSpec::Theorem {
                    name: "C",
                    ty: 2,
                    proof: 3,
                },
            ],
        );
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();

        let result = check_certificate(&fixture.bytes, &imports, &policy);

        assert!(result.is_checked());
    }

    #[test]
    fn conversion_rejects_opaque_delta_expected_type() {
        let terms = [
            TestTerm::Sort(0),
            TestTerm::Sort(1),
            TestTerm::ConstLocal { decl_index: 0 },
            TestTerm::ConstLocal { decl_index: 1 },
        ];
        let fixture = multi_declaration_certificate_fixture(
            &terms,
            &[
                TestDeclSpec::Def {
                    name: "A",
                    ty: 1,
                    value: 0,
                    reducible: false,
                },
                TestDeclSpec::Axiom { name: "B", ty: 0 },
                TestDeclSpec::Theorem {
                    name: "C",
                    ty: 2,
                    proof: 3,
                },
            ],
        );
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();

        let result = check_certificate(&fixture.bytes, &imports, &policy);

        assert_type_check(
            result.error().unwrap().clone(),
            ReferenceCheckReason::TypeMismatch,
        );
    }

    #[test]
    fn conversion_accepts_zeta_reduced_expected_type() {
        let terms = [
            TestTerm::Sort(0),
            TestTerm::Sort(1),
            TestTerm::BVar(0),
            TestTerm::ConstLocal { decl_index: 0 },
            TestTerm::Let {
                ty: 1,
                value: 0,
                body: 2,
            },
        ];
        let fixture = multi_declaration_certificate_fixture(
            &terms,
            &[
                TestDeclSpec::Axiom { name: "A", ty: 0 },
                TestDeclSpec::Theorem {
                    name: "B",
                    ty: 4,
                    proof: 3,
                },
            ],
        );
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();

        let result = check_certificate(&fixture.bytes, &imports, &policy);

        assert!(result.is_checked());
    }

    #[test]
    fn conversion_rejects_zeta_reduced_type_mismatch() {
        let terms = [
            TestTerm::Sort(0),
            TestTerm::Sort(1),
            TestTerm::BVar(0),
            TestTerm::Let {
                ty: 1,
                value: 0,
                body: 2,
            },
        ];
        let fixture = multi_declaration_certificate_fixture(
            &terms,
            &[TestDeclSpec::Theorem {
                name: "A",
                ty: 3,
                proof: 0,
            }],
        );
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();

        let result = check_certificate(&fixture.bytes, &imports, &policy);

        assert_type_check(
            result.error().unwrap().clone(),
            ReferenceCheckReason::TypeMismatch,
        );
    }

    #[test]
    fn conversion_rejects_untrusted_theorem_unfolding() {
        let terms = [
            TestTerm::Sort(0),
            TestTerm::Sort(1),
            TestTerm::ConstLocal { decl_index: 0 },
            TestTerm::ConstLocal { decl_index: 1 },
        ];
        let fixture = multi_declaration_certificate_fixture(
            &terms,
            &[
                TestDeclSpec::Theorem {
                    name: "A",
                    ty: 1,
                    proof: 0,
                },
                TestDeclSpec::Axiom { name: "B", ty: 2 },
                TestDeclSpec::Theorem {
                    name: "C",
                    ty: 0,
                    proof: 3,
                },
            ],
        );
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();

        let result = check_certificate(&fixture.bytes, &imports, &policy);

        assert_type_check(
            result.error().unwrap().clone(),
            ReferenceCheckReason::TypeMismatch,
        );
    }

    #[test]
    fn inductive_accepts_valid_nat_eq_and_list_certificates() {
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();
        let cases = [
            certificate_for_inductive("Test.Nat", nat_inductive()),
            certificate_for_inductive("Test.Eq", eq_inductive()),
            certificate_for_inductive(
                "Test.List",
                generate_inductive_artifacts_v1(&list_inductive()).unwrap(),
            ),
            certificate_for_indexed_inductives(),
            certificate_for_mutual_even_odd(),
        ];

        for bytes in cases {
            let result = check_certificate(&bytes, &imports, &policy);
            assert!(result.is_checked(), "{result:?}");
        }
    }

    #[test]
    fn positivity_accepts_approved_nested_rose_certificate() {
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();
        let bytes = certificate_for_nested_rose();

        let result = check_certificate(&bytes, &imports, &policy);

        assert!(result.is_checked(), "{result:?}");
    }

    #[test]
    fn positivity_rejects_negative_occurrence_with_structured_error() {
        let terms = [
            TestTerm::Sort(1),
            TestTerm::ConstLocal { decl_index: 0 },
            TestTerm::Pi { ty: 1, body: 1 },
            TestTerm::Pi { ty: 2, body: 1 },
        ];
        let fixture = single_inductive_certificate_fixture(
            &terms,
            TestInductiveSpec {
                names: vec![&["Bad"], &["Bad", "mk"], &["Std", "Nat"]],
                name: 0,
                universe_params: vec![],
                params: vec![],
                indices: vec![],
                sort: 1,
                constructors: vec![TestConstructorSpec { name: 1, ty: 3 }],
                recursor: None,
            },
        );
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();

        let result = check_certificate(&fixture.bytes, &imports, &policy);

        assert_type_check(
            result.error().unwrap().clone(),
            ReferenceCheckReason::NonPositiveOccurrence,
        );
    }

    #[test]
    fn inductive_mutual_iota_matches_fast_kernel_certificate() {
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();
        let bytes = certificate_for_mutual_odd_iota_theorem();

        let result = check_certificate(&bytes, &imports, &policy);

        assert!(result.is_checked(), "{result:?}");
    }

    #[test]
    fn inductive_rejects_negative_occurrence_with_structured_error() {
        let terms = [
            TestTerm::Sort(1),
            TestTerm::ConstLocal { decl_index: 0 },
            TestTerm::Pi { ty: 1, body: 1 },
            TestTerm::Pi { ty: 2, body: 1 },
        ];
        let fixture = single_inductive_certificate_fixture(
            &terms,
            TestInductiveSpec {
                names: vec![&["Bad"], &["Bad", "mk"], &["Std", "Nat"]],
                name: 0,
                universe_params: vec![],
                params: vec![],
                indices: vec![],
                sort: 1,
                constructors: vec![TestConstructorSpec { name: 1, ty: 3 }],
                recursor: None,
            },
        );
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();

        let result = check_certificate(&fixture.bytes, &imports, &policy);

        assert_type_check(
            result.error().unwrap().clone(),
            ReferenceCheckReason::NonPositiveOccurrence,
        );
    }

    #[test]
    fn inductive_rejects_constructor_result_mismatch_with_structured_error() {
        let terms = [TestTerm::Sort(1)];
        let fixture = single_inductive_certificate_fixture(
            &terms,
            TestInductiveSpec {
                names: vec![&["Bad"], &["Bad", "mk"], &["Std", "Nat"]],
                name: 0,
                universe_params: vec![],
                params: vec![],
                indices: vec![],
                sort: 1,
                constructors: vec![TestConstructorSpec { name: 1, ty: 0 }],
                recursor: None,
            },
        );
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();

        let result = check_certificate(&fixture.bytes, &imports, &policy);

        assert_type_check(
            result.error().unwrap().clone(),
            ReferenceCheckReason::BadConstructorResult,
        );
    }

    #[test]
    fn inductive_rejects_constructor_field_above_declared_sort_with_structured_error() {
        let terms = [
            TestTerm::Sort(1),
            TestTerm::ConstLocal { decl_index: 0 },
            TestTerm::Pi { ty: 0, body: 1 },
        ];
        let fixture = single_inductive_certificate_fixture(
            &terms,
            TestInductiveSpec {
                names: vec![
                    &["Audit", "Code"],
                    &["Audit", "Code", "mk"],
                    &["Std", "Nat"],
                ],
                name: 0,
                universe_params: vec![],
                params: vec![],
                indices: vec![],
                sort: 1,
                constructors: vec![TestConstructorSpec { name: 1, ty: 2 }],
                recursor: None,
            },
        );

        let result = check_certificate(
            &fixture.bytes,
            &ReferenceImportStore::default(),
            &ReferenceCheckerPolicy::default(),
        );

        assert_type_check(
            result.error().unwrap().clone(),
            ReferenceCheckReason::ConstructorUniverseBoundViolation,
        );
    }

    #[test]
    fn inductive_universe_bound_preserves_canonical_prop_exception() {
        let terms = [
            TestTerm::Sort(0),
            TestTerm::Sort(1),
            TestTerm::ConstLocal { decl_index: 0 },
            TestTerm::Pi { ty: 1, body: 2 },
        ];
        let fixture = single_inductive_certificate_fixture(
            &terms,
            TestInductiveSpec {
                names: vec![
                    &["Audit", "PropBox"],
                    &["Audit", "PropBox", "mk"],
                    &["Std", "Nat"],
                ],
                name: 0,
                universe_params: vec![],
                params: vec![],
                indices: vec![],
                sort: 0,
                constructors: vec![TestConstructorSpec { name: 1, ty: 3 }],
                recursor: None,
            },
        );

        let result = check_certificate(
            &fixture.bytes,
            &ReferenceImportStore::default(),
            &ReferenceCheckerPolicy::default(),
        );
        assert!(result.is_checked(), "Prop fixture rejected: {result:?}");
    }

    #[test]
    fn inductive_universe_bound_checks_dependent_fields_sequentially() {
        let terms = [
            TestTerm::Sort(2),
            TestTerm::Sort(1),
            TestTerm::BVar(0),
            TestTerm::ConstLocal { decl_index: 0 },
            TestTerm::Pi { ty: 2, body: 3 },
            TestTerm::Pi { ty: 1, body: 4 },
        ];
        let fixture = single_inductive_certificate_fixture(
            &terms,
            TestInductiveSpec {
                names: vec![
                    &["Audit", "DependentStore"],
                    &["Audit", "DependentStore", "mk"],
                    &["Std", "Nat"],
                ],
                name: 0,
                universe_params: vec![],
                params: vec![],
                indices: vec![],
                sort: 2,
                constructors: vec![TestConstructorSpec { name: 1, ty: 5 }],
                recursor: None,
            },
        );

        let result = check_certificate(
            &fixture.bytes,
            &ReferenceImportStore::default(),
            &ReferenceCheckerPolicy::default(),
        );
        assert!(
            result.is_checked(),
            "dependent fixture rejected: {result:?}"
        );
    }

    #[test]
    fn inductive_rejects_recursor_result_mismatch_with_structured_error() {
        let terms = [
            TestTerm::Sort(0),
            TestTerm::ConstLocal { decl_index: 0 },
            TestTerm::Pi { ty: 1, body: 1 },
            TestTerm::Pi { ty: 1, body: 0 },
            TestTerm::Pi { ty: 3, body: 2 },
        ];
        let fixture = single_inductive_certificate_fixture(
            &terms,
            TestInductiveSpec {
                names: vec![&["Empty"], &["Empty", "rec"], &["Std", "Nat"]],
                name: 0,
                universe_params: vec![],
                params: vec![],
                indices: vec![],
                sort: 0,
                constructors: vec![],
                recursor: Some(TestRecursorSpec {
                    name: 1,
                    ty: 4,
                    minor_start: 1,
                    major_index: 1,
                }),
            },
        );
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();

        let result = check_certificate(&fixture.bytes, &imports, &policy);

        assert_type_check(
            result.error().unwrap().clone(),
            ReferenceCheckReason::BadRecursorResult,
        );
    }

    #[test]
    fn iota_accepts_nat_recursor_zero_theorem_matching_fast_kernel() {
        let mut env = Env::new();
        env.add_inductive(nat_inductive()).unwrap();
        let recursor_type = nat_rec_term(nat_zero());
        assert!(env
            .is_defeq(&Ctx::new(), &[], &recursor_type, &nat())
            .unwrap());

        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();
        let bytes = nat_iota_theorem_certificate(nat_zero());

        let result = check_certificate(&bytes, &imports, &policy);

        assert!(result.is_checked(), "{result:?}");
    }

    #[test]
    fn iota_accepts_nat_recursor_succ_theorem_matching_fast_kernel() {
        let mut env = Env::new();
        env.add_inductive(nat_inductive()).unwrap();
        let major = nat_succ(nat_zero());
        let recursor_type = nat_rec_term(major.clone());
        assert!(env
            .is_defeq(&Ctx::new(), &[], &recursor_type, &nat())
            .unwrap());

        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();
        let bytes = nat_iota_theorem_certificate(major);

        let result = check_certificate(&bytes, &imports, &policy);

        assert!(result.is_checked(), "{result:?}");
    }

    #[test]
    fn iota_accepts_imported_nat_recursor_succ_theorem_matching_fast_kernel() {
        let nat_bytes = std_nat_basic_certificate();
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();
        let ReferenceCheckResult::Checked(nat_checked) =
            check_certificate(&nat_bytes, &imports, &policy)
        else {
            panic!("Std.Nat.Basic import certificate must check");
        };

        let mut session = VerifierSession::new();
        let nat_verified =
            verify_module_cert(&nat_bytes, &mut session, &AxiomPolicy::normal()).unwrap();
        let major = nat_succ(nat_zero());
        let bytes = imported_nat_iota_theorem_certificate(&nat_verified, major);
        let imports = ReferenceImportStore::from_checked_modules([nat_checked]).unwrap();

        let result = check_certificate(&bytes, &imports, &policy);

        assert!(result.is_checked(), "{result:?}");
    }

    #[test]
    fn iota_accepts_imported_indexed_vec_recursor_nil_theorem_matching_fast_kernel() {
        let indexed_bytes = certificate_for_indexed_inductives();
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();
        let ReferenceCheckResult::Checked(indexed_checked) =
            check_certificate(&indexed_bytes, &imports, &policy)
        else {
            panic!("Test.Indexed import certificate must check");
        };

        let mut session = VerifierSession::new();
        let indexed_verified =
            verify_module_cert(&indexed_bytes, &mut session, &AxiomPolicy::normal()).unwrap();
        let bytes = imported_vec_iota_theorem_certificate(&indexed_verified);
        let imports = ReferenceImportStore::from_checked_modules([indexed_checked]).unwrap();

        let result = check_certificate(&bytes, &imports, &policy);

        assert!(result.is_checked(), "{result:?}");
    }

    #[test]
    fn import_store_from_source_free_certificate_resolves_normal_mode_by_export_hash() {
        let fixture = axiom_certificate_fixture();
        let store = ReferenceImportStore::from_source_free_certificates([fixture.bytes.as_slice()])
            .expect("source-free import store builds");
        let policy = ReferenceCheckerPolicy::default();
        let cert = empty_module_certificate_importing_std_nat(fixture.export_hash, None);

        let env =
            build_import_environment(&cert, &store, &policy).expect("import environment resolves");

        assert_eq!(store.len(), 1);
        assert!(!store.entries()[0].checked_by_reference_checker());
        assert_eq!(env.len(), 1);
        assert_eq!(env.imports()[0].module.dotted(), "Std.Nat");
        assert_eq!(env.imports()[0].export_hash, fixture.export_hash);
        assert_eq!(env.imports()[0].public_environment.exports().len(), 1);
    }

    #[test]
    fn import_resolution_does_not_resolve_by_name_only() {
        let fixture = axiom_certificate_fixture();
        let store = ReferenceImportStore::from_source_free_certificates([fixture.bytes.as_slice()])
            .expect("source-free import store builds");
        let policy = ReferenceCheckerPolicy::default();
        let mut wrong_export_hash = fixture.export_hash;
        wrong_export_hash[0] ^= 0x01;
        let cert = empty_module_certificate_importing_std_nat(wrong_export_hash, None);

        let error = build_import_environment(&cert, &store, &policy)
            .expect_err("wrong export hash must reject");

        assert_import_resolution(error, ReferenceCheckReason::ImportExportHashMismatch);
    }

    #[test]
    fn import_resolution_rejects_missing_import_deterministically() {
        let fixture = axiom_certificate_fixture();
        let store = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();
        let cert = empty_module_certificate_importing_std_nat(fixture.export_hash, None);

        let first =
            build_import_environment(&cert, &store, &policy).expect_err("missing import rejects");
        let second = build_import_environment(&cert, &store, &policy)
            .expect_err("missing import rejects deterministically");

        assert_eq!(first, second);
        assert_import_resolution(first, ReferenceCheckReason::MissingImport);
    }

    #[test]
    fn normal_mode_rejects_present_import_certificate_hash_mismatch() {
        let fixture = axiom_certificate_fixture();
        let store = ReferenceImportStore::from_source_free_certificates([fixture.bytes.as_slice()])
            .expect("source-free import store builds");
        let policy = ReferenceCheckerPolicy::default();
        let mut wrong_certificate_hash = fixture.certificate_hash;
        wrong_certificate_hash[0] ^= 0x01;
        let cert = empty_module_certificate_importing_std_nat(
            fixture.export_hash,
            Some(wrong_certificate_hash),
        );

        let error = build_import_environment(&cert, &store, &policy)
            .expect_err("certificate hash mismatch rejects");

        assert_import_resolution(error, ReferenceCheckReason::ImportCertificateHashMismatch);
    }

    #[test]
    fn high_trust_rejects_unchecked_source_free_import() {
        let fixture = axiom_certificate_fixture();
        let store = ReferenceImportStore::from_source_free_certificates([fixture.bytes.as_slice()])
            .expect("source-free import store builds");
        let policy = ReferenceCheckerPolicy {
            trust_mode: ReferenceTrustMode::HighTrust,
            ..ReferenceCheckerPolicy::default()
        };
        let cert = empty_module_certificate_importing_std_nat(
            fixture.export_hash,
            Some(fixture.certificate_hash),
        );

        let error = build_import_environment(&cert, &store, &policy)
            .expect_err("unchecked high-trust import rejects");

        assert_import_resolution(error, ReferenceCheckReason::UncheckedImport);
    }

    #[test]
    fn high_trust_rejects_missing_import_certificate_hash() {
        let fixture = axiom_certificate_fixture();
        let unchecked_store =
            ReferenceImportStore::from_source_free_certificates([fixture.bytes.as_slice()])
                .expect("source-free import store builds");
        let checked =
            ReferenceCheckedModule::from_import_entry(unchecked_store.entries()[0].clone());
        let store = ReferenceImportStore::from_checked_modules([checked])
            .expect("checked import store builds");
        let policy = ReferenceCheckerPolicy {
            trust_mode: ReferenceTrustMode::HighTrust,
            ..ReferenceCheckerPolicy::default()
        };
        let cert = empty_module_certificate_importing_std_nat(fixture.export_hash, None);

        let error = build_import_environment(&cert, &store, &policy)
            .expect_err("missing high-trust certificate hash rejects");

        assert_import_resolution(error, ReferenceCheckReason::MissingImportCertificateHash);
    }

    #[test]
    fn high_trust_accepts_same_checker_checked_module_interface() {
        let fixture = axiom_certificate_fixture();
        let unchecked_store =
            ReferenceImportStore::from_source_free_certificates([fixture.bytes.as_slice()])
                .expect("source-free import store builds");
        let checked =
            ReferenceCheckedModule::from_import_entry(unchecked_store.entries()[0].clone());
        let store = ReferenceImportStore::from_checked_modules([checked])
            .expect("checked import store builds");
        let policy = ReferenceCheckerPolicy {
            trust_mode: ReferenceTrustMode::HighTrust,
            ..ReferenceCheckerPolicy::default()
        };
        let cert = empty_module_certificate_importing_std_nat(
            fixture.export_hash,
            Some(fixture.certificate_hash),
        );

        let env =
            build_import_environment(&cert, &store, &policy).expect("high-trust import resolves");

        assert_eq!(env.len(), 1);
        assert_eq!(env.imports()[0].certificate_hash, fixture.certificate_hash);
    }

    #[test]
    fn std_imported_public_environment_remaps_local_refs_to_imported_refs() {
        let logic_bytes = std_logic_eq_certificate();
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy {
            trust_mode: ReferenceTrustMode::HighTrust,
            deny_custom_axioms: true,
            ..ReferenceCheckerPolicy::default()
        };
        let ReferenceCheckResult::Checked(logic) =
            check_certificate(&logic_bytes, &imports, &policy)
        else {
            panic!("Std.Logic fixture must check before it can be imported");
        };
        let store = ReferenceImportStore::from_checked_modules([logic]).unwrap();
        let nat_bytes = std_nat_zero_eq_zero_certificate(&logic_bytes);

        let result = check_certificate(&nat_bytes, &store, &policy);

        assert!(
            result.is_checked(),
            "imported Eq.refl type must not resolve its Eq reference as a Std.Nat local"
        );
    }

    #[test]
    fn eq_reasoning_fixture_uses_checked_std_logic_eq_builtin_bridge() {
        let logic_bytes = include_bytes!(
            "../../../testdata/package/proofs/vendor/npa-std/Std/Logic/Eq/certificate.npcert"
        );
        let eq_reasoning_bytes = include_bytes!(
            "../../../testdata/package/proofs/Proofs/Ai/EqReasoning/certificate.npcert"
        );
        let policy = ReferenceCheckerPolicy {
            trust_mode: ReferenceTrustMode::HighTrust,
            allowed_axioms: vec!["Eq.rec".to_owned()],
            deny_custom_axioms: true,
            ..ReferenceCheckerPolicy::default()
        };
        let ReferenceCheckResult::Checked(logic) =
            check_certificate(logic_bytes, &ReferenceImportStore::default(), &policy)
        else {
            panic!("Std.Logic.Eq fixture must check before it can be imported");
        };
        let store = ReferenceImportStore::from_checked_modules([logic]).unwrap();

        let result = check_certificate(eq_reasoning_bytes, &store, &policy);

        assert!(
            result.is_checked(),
            "checked Std.Logic.Eq exports must bridge Eq, Eq.refl, and Eq.rec to canonical builtins"
        );
    }

    #[test]
    fn import_store_rejects_duplicate_import_bindings() {
        let fixture = axiom_certificate_fixture();

        let error = ReferenceImportStore::from_source_free_certificates([
            fixture.bytes.as_slice(),
            fixture.bytes.as_slice(),
        ])
        .expect_err("duplicate import store entries reject");

        assert_eq!(error.kind, ReferenceCheckErrorKind::ImportResolution);
        assert_eq!(error.section, ReferenceCertificateSection::ImportStore);
        assert_eq!(error.reason, Some(ReferenceCheckReason::DuplicateImport));
    }

    #[test]
    fn current_certificate_rejects_duplicate_import_bindings() {
        let fixture = axiom_certificate_fixture();
        let store = ReferenceImportStore::from_source_free_certificates([fixture.bytes.as_slice()])
            .expect("source-free import store builds");
        let policy = ReferenceCheckerPolicy::default();
        let cert = empty_module_certificate_importing_std_nat_twice(fixture.export_hash);

        let error = build_import_environment(&cert, &store, &policy)
            .expect_err("duplicate certificate imports reject");

        assert_import_resolution(error, ReferenceCheckReason::DuplicateImport);
    }

    #[test]
    fn resolved_import_environment_preserves_imported_axiom_dependencies() {
        let fixture = axiom_certificate_fixture_with_axiom_dependencies(true);
        let store = ReferenceImportStore::from_source_free_certificates([fixture.bytes.as_slice()])
            .expect("source-free import store builds");
        let policy = ReferenceCheckerPolicy::default();
        let cert = empty_module_certificate_importing_std_nat(fixture.export_hash, None);

        let env =
            build_import_environment(&cert, &store, &policy).expect("import environment resolves");
        let import_env = &env.imports()[0].public_environment;

        assert_eq!(import_env.exports().len(), 1);
        assert_eq!(import_env.exports()[0].axiom_dependencies.len(), 1);
        assert_eq!(import_env.module_axioms().len(), 1);
    }

    #[test]
    fn check_certificate_runs_import_resolution_before_type_check() {
        let fixture = axiom_certificate_fixture();
        let store = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();
        let cert = empty_module_certificate_importing_std_nat(fixture.export_hash, None);

        let result = check_certificate(&cert, &store, &policy);

        assert_import_resolution(
            result.error().unwrap().clone(),
            ReferenceCheckReason::MissingImport,
        );
    }

    #[test]
    fn decode_rejects_noncanonical_uvar_with_section_and_offset() {
        let mut cert = header_bytes();
        let offset = cert.len();
        cert.extend([0x80, 0x00]);

        let error = decode_certificate(&cert).expect_err("noncanonical uvar must reject");

        assert_eq!(
            error,
            ReferenceCheckError {
                kind: ReferenceCheckErrorKind::MalformedCertificate,
                section: ReferenceCertificateSection::Imports,
                offset,
                reason: Some(ReferenceCheckReason::NonCanonicalUvar),
                reference: None,
            }
        );
    }

    #[test]
    fn decode_rejects_unknown_level_tag() {
        let mut cert = header_bytes();
        cert.extend(encode_uvar(0)); // imports
        cert.extend(encode_uvar(1));
        encode_name(&mut cert, &["Std", "Nat"]);
        cert.extend(encode_uvar(1)); // one level entry
        let offset = cert.len();
        cert.push(0xff);

        let error = decode_certificate(&cert).expect_err("unknown tag must reject");

        assert_eq!(error.kind, ReferenceCheckErrorKind::MalformedCertificate);
        assert_eq!(error.section, ReferenceCertificateSection::LevelTable);
        assert_eq!(error.offset, offset);
        assert_eq!(
            error.reason,
            Some(ReferenceCheckReason::UnknownTag { tag: 0xff })
        );
    }

    #[test]
    fn decode_rejects_duplicate_name_table_entry() {
        let duplicate: &[&str] = &["Std", "Nat"];
        let cert = certificate_with_name_table(&[duplicate, duplicate]);

        let error = decode_certificate(&cert).expect_err("duplicate names must reject");

        assert_eq!(error.kind, ReferenceCheckErrorKind::MalformedCertificate);
        assert_eq!(error.section, ReferenceCertificateSection::NameTable);
        assert_eq!(error.reason, Some(ReferenceCheckReason::DuplicateName));
        assert!(error.offset > 0);
    }

    #[test]
    fn decode_rejects_unused_name_table_entry() {
        let cert = certificate_with_name_table(&[&["Std", "Nat"], &["ZZ"]]);

        let error = decode_certificate(&cert).expect_err("unused names must reject");

        assert_eq!(error.kind, ReferenceCheckErrorKind::MalformedCertificate);
        assert_eq!(error.section, ReferenceCertificateSection::NameTable);
        assert_eq!(error.reason, Some(ReferenceCheckReason::UnusedTableEntry));
        assert!(error.offset > 0);
    }

    #[test]
    fn decode_rejects_dangling_level_reference() {
        let mut cert = header_bytes();
        cert.extend(encode_uvar(0)); // imports
        cert.extend(encode_uvar(1)); // name table
        encode_name(&mut cert, &["Std", "Nat"]);
        cert.extend(encode_uvar(1)); // level table
        let offset = cert.len();
        cert.push(0x04); // Param
        cert.extend(encode_uvar(1)); // missing name id
        cert.extend(encode_uvar(0)); // term table
        cert.extend(encode_uvar(0)); // declarations
        cert.extend(encode_uvar(0)); // export block
        cert.extend(encode_uvar(0)); // axiom report per-declaration
        cert.extend(encode_uvar(0)); // module axioms
        cert.extend([0; 96]);

        let error = decode_certificate(&cert).expect_err("dangling level name must reject");

        assert_eq!(error.kind, ReferenceCheckErrorKind::MalformedCertificate);
        assert_eq!(error.section, ReferenceCertificateSection::LevelTable);
        assert_eq!(error.offset, offset);
        assert_eq!(error.reason, Some(ReferenceCheckReason::DanglingReference));
    }

    #[test]
    fn decode_rejects_non_normalized_level_entry() {
        let mut cert = header_bytes();
        cert.extend(encode_uvar(0)); // imports
        cert.extend(encode_uvar(2)); // name table
        encode_name(&mut cert, &["Std", "Nat"]);
        encode_name(&mut cert, &["u"]);
        cert.extend(encode_uvar(3)); // level table
        cert.push(0x00); // Zero
        cert.push(0x04); // Param u
        cert.extend(encode_uvar(1));
        let offset = cert.len();
        cert.push(0x02); // Max Zero u, normalizes to u
        cert.extend(encode_uvar(0));
        cert.extend(encode_uvar(1));
        cert.extend(encode_uvar(0)); // term table
        cert.extend(encode_uvar(0)); // declarations
        cert.extend(encode_uvar(0)); // export block
        cert.extend(encode_uvar(0)); // axiom report per-declaration
        cert.extend(encode_uvar(0)); // module axioms
        cert.extend([0; 96]);

        let error = decode_certificate(&cert).expect_err("non-normalized level must reject");

        assert_eq!(error.kind, ReferenceCheckErrorKind::MalformedCertificate);
        assert_eq!(error.section, ReferenceCertificateSection::LevelTable);
        assert_eq!(error.offset, offset);
        assert_eq!(error.reason, Some(ReferenceCheckReason::NonNormalizedLevel));
    }

    #[test]
    fn decode_rejects_trailing_bytes() {
        let mut cert = empty_module_certificate();
        let offset = cert.len();
        cert.push(0);

        let error = decode_certificate(&cert).expect_err("trailing bytes must reject");

        assert_eq!(
            error,
            ReferenceCheckError {
                kind: ReferenceCheckErrorKind::MalformedCertificate,
                section: ReferenceCertificateSection::FullCertificate,
                offset,
                reason: Some(ReferenceCheckReason::TrailingBytes),
                reference: None,
            }
        );
    }

    #[test]
    fn invalid_utf8_header_is_structured_without_human_string_matching() {
        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();
        let malformed = [0x01, 0xff];

        let result = check_certificate(&malformed, &imports, &policy);

        assert_eq!(
            result.error().unwrap(),
            &ReferenceCheckError {
                kind: ReferenceCheckErrorKind::MalformedCertificate,
                section: ReferenceCertificateSection::HeaderFormat,
                offset: 1,
                reason: Some(ReferenceCheckReason::InvalidUtf8),
                reference: None,
            }
        );
    }

    #[test]
    fn module_name_validation_is_structured() {
        assert_eq!(
            ReferenceModuleName::from_dotted(""),
            Err(ReferenceNameError::EmptyComponent { index: 0 })
        );
        assert_eq!(
            ReferenceModuleName::from_dotted("Std..Nat"),
            Err(ReferenceNameError::EmptyComponent { index: 1 })
        );
        assert_eq!(
            ReferenceModuleName::from_dotted("Std.Nat.+"),
            Err(ReferenceNameError::InvalidComponent { index: 2 })
        );
        assert_eq!(
            ReferenceModuleName::from_dotted("Std.Nat.add′"),
            Err(ReferenceNameError::InvalidComponent { index: 2 })
        );

        let name = ReferenceModuleName::from_dotted("Std.Nat.add_comm'").unwrap();
        assert_eq!(name.components(), ["Std", "Nat", "add_comm'"]);
        assert_eq!(name.dotted(), "Std.Nat.add_comm'");
    }

    fn p8h13_fuzz_artifact_hash(seed: &str, bytes: &[u8]) -> ReferenceHash {
        let mut hasher = Sha256::new();
        hasher.update(b"NPA-P8H13-REFERENCE-FUZZ-0.1");
        hasher.update(seed.as_bytes());
        hasher.update([0]);
        hasher.update(bytes);
        hasher.finalize().into()
    }

    #[test]
    fn fuzz_p8h13_rejects_malformed_certificate_corpus_without_panic() {
        const SEED: &str = "p8h13-reference-fuzz-seed-0001";
        let mut noncanonical_uvar = header_bytes();
        noncanonical_uvar.extend([0x80, 0x00]);

        let mut unknown_level_tag = header_bytes();
        unknown_level_tag.extend(encode_uvar(0)); // imports
        unknown_level_tag.extend(encode_uvar(1));
        encode_name(&mut unknown_level_tag, &["Std", "Nat"]);
        unknown_level_tag.extend(encode_uvar(1)); // one level entry
        unknown_level_tag.push(0xff);

        let mut dangling_level = header_bytes();
        dangling_level.extend(encode_uvar(0)); // imports
        dangling_level.extend(encode_uvar(1)); // name table
        encode_name(&mut dangling_level, &["Std", "Nat"]);
        dangling_level.extend(encode_uvar(1)); // level table
        dangling_level.push(0x04); // Param
        dangling_level.extend(encode_uvar(1)); // missing name id
        dangling_level.extend(encode_uvar(0)); // term table
        dangling_level.extend(encode_uvar(0)); // declarations
        dangling_level.extend(encode_uvar(0)); // export block
        dangling_level.extend(encode_uvar(0)); // axiom report per-declaration
        dangling_level.extend(encode_uvar(0)); // module axioms
        dangling_level.extend([0; 96]);

        let mut trailing_bytes = empty_module_certificate();
        trailing_bytes.push(0);

        let duplicate: &[&str] = &["Std", "Nat"];
        let cases = vec![
            ("empty", Vec::new()),
            ("invalid_utf8_header", vec![0x01, 0xff]),
            ("noncanonical_uvar", noncanonical_uvar),
            ("unknown_level_tag", unknown_level_tag),
            ("dangling_level", dangling_level),
            ("trailing_bytes", trailing_bytes),
            (
                "duplicate_name_table_entry",
                certificate_with_name_table(&[duplicate, duplicate]),
            ),
        ];

        let imports = ReferenceImportStore::default();
        let policy = ReferenceCheckerPolicy::default();
        let mut observed = Vec::new();

        for (name, bytes) in cases {
            let artifact_hash = p8h13_fuzz_artifact_hash(SEED, &bytes);
            assert_ne!(artifact_hash, [0; 32], "{name}");

            let decoded = std::panic::catch_unwind(|| decode_certificate(&bytes));
            assert!(decoded.is_ok(), "{name} panicked during decode");
            assert!(decoded.unwrap().is_err(), "{name} unexpectedly decoded");

            let checked = std::panic::catch_unwind(|| check_certificate(&bytes, &imports, &policy));
            assert!(checked.is_ok(), "{name} panicked during check");
            let ReferenceCheckResult::Rejected(error) = checked.unwrap() else {
                panic!("{name} unexpectedly checked");
            };
            observed.push((name, artifact_hash, error.kind, error.reason));
        }

        let mut sorted_hashes = observed
            .iter()
            .map(|(_, hash, _, _)| *hash)
            .collect::<Vec<_>>();
        sorted_hashes.sort();
        sorted_hashes.dedup();
        assert_eq!(sorted_hashes.len(), observed.len());
        assert!(observed.iter().any(|(_, _, kind, reason)| {
            *kind == ReferenceCheckErrorKind::MalformedCertificate
                && *reason == Some(ReferenceCheckReason::NonCanonicalUvar)
        }));
        assert!(observed.iter().any(|(_, _, kind, reason)| {
            *kind == ReferenceCheckErrorKind::MalformedCertificate
                && *reason == Some(ReferenceCheckReason::TrailingBytes)
        }));
    }

    #[test]
    fn universe_constraints_reference_checker_accepts_fast_canonical_bytes() {
        let constraints = vec![
            UniverseConstraint::le(Level::succ(Level::succ(Level::zero())), Level::param("u")),
            UniverseConstraint::le(
                Level::max(Level::param("u"), Level::param("v")),
                Level::param("w"),
            ),
        ];
        let cert = build_module_cert(
            CoreModule {
                name: Name::from_dotted("Test.ReferenceUniverse"),
                declarations: vec![Decl::AxiomConstrained {
                    name: "Test.ReferenceUniverse.map".to_owned(),
                    universe_params: vec!["u".to_owned(), "v".to_owned(), "w".to_owned()],
                    universe_constraints: constraints,
                    ty: Expr::sort(Level::param("w")),
                }],
            },
            &[],
        )
        .unwrap();
        let bytes = encode_module_cert(&cert).unwrap();

        decode_certificate(&bytes).unwrap();
        assert!(check_certificate(
            &bytes,
            &ReferenceImportStore::default(),
            &ReferenceCheckerPolicy::default(),
        )
        .is_checked());
    }

    #[test]
    fn universe_constraints_reference_checker_accepts_imported_constrained_public_signature() {
        let provider_bytes = constrained_axiom_certificate();
        let import_store =
            ReferenceImportStore::from_source_free_certificates([provider_bytes.as_slice()])
                .expect("provider import store builds");
        let mut session = VerifierSession::new();
        let provider = verify_module_cert(&provider_bytes, &mut session, &AxiomPolicy::normal())
            .expect("provider verifies");
        let consumer = build_module_cert(
            use_constrained_axiom_module(vec![
                Level::zero(),
                Level::zero(),
                Level::succ(Level::zero()),
            ]),
            &[provider],
        )
        .expect("supported constrained import builds");
        let consumer_bytes = encode_module_cert(&consumer).expect("consumer encodes");

        let result = check_certificate(
            &consumer_bytes,
            &import_store,
            &ReferenceCheckerPolicy::default(),
        );

        assert!(result.is_checked(), "{result:?}");
    }

    #[test]
    fn universe_constraints_kernel_rejects_unsatisfied_imported_constrained_public_signature() {
        let provider_bytes = constrained_axiom_certificate();
        let mut session = VerifierSession::new();
        let provider = verify_module_cert(&provider_bytes, &mut session, &AxiomPolicy::normal())
            .expect("provider verifies");

        let error = build_module_cert(
            use_constrained_axiom_module(vec![
                Level::succ(Level::zero()),
                Level::zero(),
                Level::zero(),
            ]),
            &[provider],
        )
        .expect_err("unsatisfied constrained import rejects in kernel-backed producer");

        assert!(matches!(
            error,
            CertError::Kernel(Error::UniverseConstraintViolation { .. })
        ));
    }

    #[test]
    fn universe_constraint_semantics_match_kernel_for_supported_fragment() {
        let kernel_context = UniverseContext::new(
            vec!["u".to_owned(), "v".to_owned(), "w".to_owned()],
            vec![
                UniverseConstraint::le(Level::param("u"), Level::param("v")),
                UniverseConstraint::le(Level::param("v"), Level::param("w")),
            ],
        )
        .unwrap();
        kernel_context
            .entails(&[UniverseConstraint::le(
                Level::max(Level::param("u"), Level::param("v")),
                Level::param("w"),
            )])
            .unwrap();

        let reference_context = ReferenceUniverseContext::new(
            ref_params(&["u", "v", "w"]),
            vec![rc_le(rp("u"), rp("v")), rc_le(rp("v"), rp("w"))],
            0,
        )
        .unwrap();
        reference_context
            .entails(&[rc_le(rmax(rp("u"), rp("v")), rp("w"))], 0)
            .unwrap();

        kernel_context
            .entails(&[UniverseConstraint::le(
                Level::param("u"),
                Level::max(Level::param("v"), Level::param("w")),
            )])
            .unwrap();
        reference_context
            .entails(&[rc_le(rp("u"), rmax(rp("v"), rp("w")))], 0)
            .unwrap();

        assert!(!kernel_context
            .entails_level_le(
                &Level::succ(Level::param("v")),
                &Level::max(Level::param("u"), Level::param("w")),
            )
            .unwrap());
        assert!(!reference_context
            .entails_level_le(&rs(rp("v")), &rmax(rp("u"), rp("w")), 0,)
            .unwrap());

        assert!(kernel_context
            .entails_level_le(
                &Level::imax(Level::succ(Level::zero()), Level::param("u")),
                &Level::max(Level::succ(Level::zero()), Level::param("u")),
            )
            .unwrap());
        assert!(reference_context
            .entails_level_le(&rimax(rs(rz()), rp("u")), &rmax(rs(rz()), rp("u")), 0,)
            .unwrap());

        assert!(kernel_context
            .entails_level_le(
                &Level::imax(Level::succ(Level::zero()), Level::param("u")),
                &Level::param("u"),
            )
            .unwrap());
        assert!(reference_context
            .entails_level_le(&rimax(rs(rz()), rp("u")), &rp("u"), 0)
            .unwrap());

        assert!(!kernel_context
            .entails_level_le(
                &Level::imax(Level::succ(Level::succ(Level::zero())), Level::param("u"),),
                &Level::param("u"),
            )
            .unwrap());
        assert!(!reference_context
            .entails_level_le(&rimax(rs(rs(rz())), rp("u")), &rp("u"), 0)
            .unwrap());
    }

    #[test]
    fn universe_constraint_semantics_match_kernel_for_rejections() {
        let kernel_context = UniverseContext::from_params(vec!["u".to_owned()]).unwrap();
        let reference_context =
            ReferenceUniverseContext::from_params(ref_params(&["u"]), 0).unwrap();
        let kernel_rhs = Level::IMax(
            Box::new(Level::succ(Level::zero())),
            Box::new(Level::param("u")),
        );
        let reference_rhs = rimax(rs(rz()), rp("u"));

        assert!(matches!(
            kernel_context.entails_level_le(
                &Level::max(Level::succ(Level::zero()), Level::param("u")),
                &kernel_rhs,
            ),
            Err(Error::UnsupportedUniverseConstraint { .. })
        ));
        assert_eq!(
            reason(
                reference_context
                    .entails_level_le(&rmax(rs(rz()), rp("u")), &reference_rhs, 0)
                    .unwrap_err()
            ),
            Some(ReferenceCheckReason::UnsupportedUniverseConstraint)
        );

        assert_eq!(
            UniverseContext::new(
                vec!["u".to_owned()],
                vec![UniverseConstraint::le(
                    Level::succ(Level::param("u")),
                    Level::param("u")
                )],
            ),
            Err(Error::UnsatisfiableUniverseConstraints)
        );
        assert_eq!(
            reason(
                ReferenceUniverseContext::new(
                    ref_params(&["u"]),
                    vec![rc_le(rs(rp("u")), rp("u"))],
                    0,
                )
                .unwrap_err()
            ),
            Some(ReferenceCheckReason::UnsatisfiableUniverseConstraints)
        );

        assert!(matches!(
            UniverseContext::new(
                vec!["u".to_owned(), "v".to_owned(), "w".to_owned()],
                vec![UniverseConstraint::le(
                    Level::param("u"),
                    Level::max(Level::param("v"), Level::param("w")),
                )],
            ),
            Err(Error::UnsupportedUniverseConstraint { .. })
        ));
        assert_eq!(
            reason(
                ReferenceUniverseContext::new(
                    ref_params(&["u", "v", "w"]),
                    vec![rc_le(rp("u"), rmax(rp("v"), rp("w")))],
                    0,
                )
                .unwrap_err()
            ),
            Some(ReferenceCheckReason::UnsupportedUniverseConstraint)
        );

        assert_eq!(
            UniverseContext::new(
                vec!["u".to_owned(), "v".to_owned()],
                vec![
                    UniverseConstraint::le(Level::param("u"), Level::param("v")),
                    UniverseConstraint::le(Level::param("u"), Level::param("v")),
                ],
            ),
            Err(Error::DuplicateUniverseConstraint)
        );
        assert_eq!(
            reason(
                ReferenceUniverseContext::new(
                    ref_params(&["u", "v"]),
                    vec![rc_le(rp("u"), rp("v")), rc_le(rp("u"), rp("v"))],
                    0,
                )
                .unwrap_err()
            ),
            Some(ReferenceCheckReason::DuplicateUniverseConstraint)
        );

        assert!(matches!(
            UniverseContext::from_params(vec!["u".to_owned()])
                .unwrap()
                .entails(&[UniverseConstraint::le(
                    Level::succ(Level::param("u")),
                    Level::param("u"),
                )]),
            Err(Error::UniverseConstraintViolation { .. })
        ));
        assert_eq!(
            reason(
                ReferenceUniverseContext::from_params(ref_params(&["u"]), 0)
                    .unwrap()
                    .entails(&[rc_le(rs(rp("u")), rp("u"))], 0)
                    .unwrap_err()
            ),
            Some(ReferenceCheckReason::UniverseConstraintViolation)
        );

        let too_many_params = (0..MAX_UNIVERSE_CONTEXT_NODES)
            .map(|index| format!("u{index:03}"))
            .collect::<Vec<_>>();
        assert_eq!(
            UniverseContext::from_params(too_many_params),
            Err(Error::ResourceLimit {
                kind: ResourceLimitKind::UniverseConstraints,
            })
        );
        let too_many_reference_params = (0..MAX_UNIVERSE_CONTEXT_NODES)
            .map(|index| ref_name(&format!("u{index:03}")))
            .collect::<Vec<_>>();
        assert_eq!(
            reason(
                ReferenceUniverseContext::from_params(too_many_reference_params, 0).unwrap_err()
            ),
            Some(ReferenceCheckReason::ResourceLimit)
        );

        let bounded_reference_params = (0..64)
            .map(|index| ref_name(&format!("v{index:03}")))
            .collect::<Vec<_>>();
        let reference_context =
            ReferenceUniverseContext::from_params(bounded_reference_params.clone(), 0).unwrap();
        let max_level = |params: &[ReferenceModuleName]| {
            params.iter().cloned().fold(rz(), |level, param| {
                rmax(level, ReferenceCoreLevel::Param(param))
            })
        };
        assert_eq!(
            reason(
                reference_context
                    .entails_level_le(
                        &max_level(&bounded_reference_params[..32]),
                        &max_level(&bounded_reference_params[31..]),
                        0,
                    )
                    .unwrap_err()
            ),
            Some(ReferenceCheckReason::ResourceLimit)
        );
    }

    #[test]
    fn universe_constraint_substitution_matches_kernel_canonicalization() {
        let kernel_context = UniverseContext::empty();
        let mut kernel_constraints = vec![
            UniverseConstraint::le(Level::param("u"), Level::param("v")),
            UniverseConstraint::le(Level::param("v"), Level::param("u")),
        ];
        kernel_constraints.sort();
        assert_eq!(
            kernel_context
                .substitute_constraints(
                    &["u".to_owned(), "v".to_owned()],
                    &[Level::zero(), Level::zero()],
                    &kernel_constraints,
                )
                .unwrap(),
            vec![UniverseConstraint::le(Level::zero(), Level::zero())]
        );

        let reference_context = ReferenceUniverseContext::empty();
        let mut reference_constraints = vec![rc_le(rp("u"), rp("v")), rc_le(rp("v"), rp("u"))];
        reference_constraints.sort();
        assert_eq!(
            reference_context
                .substitute_constraints(
                    &ref_params(&["u", "v"]),
                    &[rz(), rz()],
                    &reference_constraints,
                    0,
                )
                .unwrap(),
            vec![rc_le(rz(), rz())]
        );

        assert_eq!(reference_context.entails(&[rc_eq(rz(), rz())], 0), Ok(()));
    }

    #[test]
    fn universe_meta_param_fixture_rejects_before_hash_trust() {
        let bytes = universe_meta_param_certificate();

        let decoded = decode_certificate(&bytes)
            .expect_err("reference checker must reject unresolved universe meta names");
        assert_eq!(decoded.kind, ReferenceCheckErrorKind::MalformedCertificate);
        assert_eq!(
            decoded.reason,
            Some(ReferenceCheckReason::InvalidNameComponent)
        );

        let checked = check_certificate(
            &bytes,
            &ReferenceImportStore::default(),
            &ReferenceCheckerPolicy::default(),
        );
        assert_eq!(checked.error(), Some(&decoded));
    }
}

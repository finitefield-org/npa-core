//! Opaque, command-local certificate contexts for non-authoritative authoring.

use std::{collections::BTreeMap, marker::PhantomData, rc::Rc, sync::Arc};

use npa_kernel::KernelExecutionOptions;
use sha2::{Digest, Sha256};

use crate::{
    canonical, verify, AxiomPolicy, AxiomReport, CoreModule, DeclCert, ExportEntry, Hash,
    ImportEntry, LevelNode, ModuleCert, Name, Result, StructuralClosureSummary, TermNode,
    VerifiedModule,
};

/// Read-only certificate data shared by ordinary and local-authoring import loaders.
///
/// This trait is crate-private so an untrusted caller cannot implement a forged
/// import capability. It deliberately has no method that returns a
/// [`VerifiedModule`] or a kernel environment.
pub(crate) trait CertificateImportView {
    fn module(&self) -> &Name;
    fn imports(&self) -> &[ImportEntry];
    fn name_table(&self) -> &[Name];
    fn level_table(&self) -> &[LevelNode];
    fn term_table(&self) -> &[TermNode];
    fn declarations(&self) -> &[DeclCert];
    fn export_hash(&self) -> Hash;
    fn certificate_hash(&self) -> Hash;
    fn export_block(&self) -> &[ExportEntry];
    fn axiom_report(&self) -> &AxiomReport;
    fn structural_closure(&self) -> &StructuralClosureSummary;
}

impl CertificateImportView for VerifiedModule {
    fn module(&self) -> &Name {
        self.module()
    }

    fn imports(&self) -> &[ImportEntry] {
        self.imports()
    }

    fn name_table(&self) -> &[Name] {
        self.name_table()
    }

    fn level_table(&self) -> &[LevelNode] {
        self.level_table()
    }

    fn term_table(&self) -> &[TermNode] {
        self.term_table()
    }

    fn declarations(&self) -> &[DeclCert] {
        self.declarations()
    }

    fn export_hash(&self) -> Hash {
        self.export_hash()
    }

    fn certificate_hash(&self) -> Hash {
        self.certificate_hash()
    }

    fn export_block(&self) -> &[ExportEntry] {
        self.export_block()
    }

    fn axiom_report(&self) -> &AxiomReport {
        self.axiom_report()
    }

    fn structural_closure(&self) -> &StructuralClosureSummary {
        self.structural_closure()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct OwnedLocalAuthoringModuleContext {
    certificate_format: String,
    core_spec: String,
    module: Name,
    imports: Vec<ImportEntry>,
    name_table: Vec<Name>,
    level_table: Vec<LevelNode>,
    term_table: Vec<TermNode>,
    declarations: Vec<DeclCert>,
    export_hash: Hash,
    certificate_hash: Hash,
    export_block: Vec<ExportEntry>,
    axiom_report: AxiomReport,
    structural_closure: StructuralClosureSummary,
    closure_used_cached_context: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum LocalAuthoringModuleContext {
    Owned(Box<OwnedLocalAuthoringModuleContext>),
    SharedVerified(Arc<VerifiedModule>),
}

impl LocalAuthoringModuleContext {
    fn from_verified(module: &VerifiedModule) -> Self {
        Self::SharedVerified(Arc::new(module.clone()))
    }

    fn from_shared_verified(module: Arc<VerifiedModule>) -> Self {
        Self::SharedVerified(module)
    }

    fn from_cert(
        cert: ModuleCert,
        structural_closure: StructuralClosureSummary,
        closure_used_cached_context: bool,
    ) -> Self {
        let cert = cert.into_parts();
        Self::Owned(Box::new(OwnedLocalAuthoringModuleContext {
            certificate_format: cert.header.format,
            core_spec: cert.header.core_spec,
            module: cert.header.module,
            imports: cert.imports,
            name_table: cert.name_table,
            level_table: cert.level_table,
            term_table: cert.term_table,
            declarations: cert.declarations,
            export_hash: cert.hashes.export_hash,
            certificate_hash: cert.hashes.certificate_hash,
            export_block: cert.export_block,
            axiom_report: cert.axiom_report,
            structural_closure,
            closure_used_cached_context,
        }))
    }

    fn certificate_format(&self) -> &str {
        match self {
            Self::Owned(context) => &context.certificate_format,
            Self::SharedVerified(module) => module.certificate_format(),
        }
    }

    fn core_spec(&self) -> &str {
        match self {
            Self::Owned(context) => &context.core_spec,
            Self::SharedVerified(module) => module.core_spec(),
        }
    }

    fn closure_used_cached_context(&self) -> bool {
        match self {
            Self::Owned(context) => context.closure_used_cached_context,
            Self::SharedVerified(_) => false,
        }
    }
}

impl CertificateImportView for LocalAuthoringModuleContext {
    fn module(&self) -> &Name {
        match self {
            Self::Owned(context) => &context.module,
            Self::SharedVerified(module) => module.module(),
        }
    }

    fn imports(&self) -> &[ImportEntry] {
        match self {
            Self::Owned(context) => &context.imports,
            Self::SharedVerified(module) => module.imports(),
        }
    }

    fn name_table(&self) -> &[Name] {
        match self {
            Self::Owned(context) => &context.name_table,
            Self::SharedVerified(module) => module.name_table(),
        }
    }

    fn level_table(&self) -> &[LevelNode] {
        match self {
            Self::Owned(context) => &context.level_table,
            Self::SharedVerified(module) => module.level_table(),
        }
    }

    fn term_table(&self) -> &[TermNode] {
        match self {
            Self::Owned(context) => &context.term_table,
            Self::SharedVerified(module) => module.term_table(),
        }
    }

    fn declarations(&self) -> &[DeclCert] {
        match self {
            Self::Owned(context) => &context.declarations,
            Self::SharedVerified(module) => module.declarations(),
        }
    }

    fn export_hash(&self) -> Hash {
        match self {
            Self::Owned(context) => context.export_hash,
            Self::SharedVerified(module) => module.export_hash(),
        }
    }

    fn certificate_hash(&self) -> Hash {
        match self {
            Self::Owned(context) => context.certificate_hash,
            Self::SharedVerified(module) => module.certificate_hash(),
        }
    }

    fn export_block(&self) -> &[ExportEntry] {
        match self {
            Self::Owned(context) => &context.export_block,
            Self::SharedVerified(module) => module.export_block(),
        }
    }

    fn axiom_report(&self) -> &AxiomReport {
        match self {
            Self::Owned(context) => &context.axiom_report,
            Self::SharedVerified(module) => module.axiom_report(),
        }
    }

    fn structural_closure(&self) -> &StructuralClosureSummary {
        match self {
            Self::Owned(context) => &context.structural_closure,
            Self::SharedVerified(module) => module.structural_closure(),
        }
    }
}

/// Expected current-certificate identity supplied by the cache orchestration layer.
///
/// Construction of this value is not evidence. Reconstruction compares every
/// field with the bounded canonical decode of `current_bytes`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalAuthoringReconstructionIdentity {
    pub(crate) certificate_file_hash: Hash,
    pub(crate) certificate_format: String,
    pub(crate) core_spec: String,
    pub(crate) module: Name,
    pub(crate) imports: Vec<ImportEntry>,
    pub(crate) export_hash: Hash,
    pub(crate) axiom_report_hash: Hash,
    pub(crate) certificate_hash: Hash,
    pub(crate) axiom_policy_hash: Hash,
}

impl LocalAuthoringReconstructionIdentity {
    /// Construct an untrusted expected identity for current certificate bytes.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        certificate_file_hash: Hash,
        certificate_format: impl Into<String>,
        core_spec: impl Into<String>,
        module: Name,
        imports: Vec<ImportEntry>,
        export_hash: Hash,
        axiom_report_hash: Hash,
        certificate_hash: Hash,
        axiom_policy_hash: Hash,
    ) -> Self {
        Self {
            certificate_file_hash,
            certificate_format: certificate_format.into(),
            core_spec: core_spec.into(),
            module,
            imports,
            export_hash,
            axiom_report_hash,
            certificate_hash,
            axiom_policy_hash,
        }
    }
}

/// Certificate identity carried by a separately parsed untrusted source interface.
///
/// This value deliberately contains no frontend runtime object. The CLI/frontend
/// adapter validates the complete interface separately, then supplies only this
/// identity for binding to the reconstructed certificate context.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalAuthoringInterfaceIdentity {
    pub(crate) module: Name,
    pub(crate) export_hash: Hash,
    pub(crate) certificate_hash: Hash,
}

impl LocalAuthoringInterfaceIdentity {
    /// Construct the identity extracted from a parsed untrusted interface.
    pub fn new(module: Name, export_hash: Hash, certificate_hash: Hash) -> Self {
        Self {
            module,
            export_hash,
            certificate_hash,
        }
    }
}

/// Structurally validated certificate context awaiting command-session adoption.
///
/// Fields are private and there is no conversion to [`VerifiedModule`].
#[derive(Debug)]
pub struct PendingLocalAuthoringContext {
    context: LocalAuthoringModuleContext,
}

impl PendingLocalAuthoringContext {
    /// Return the pending module name for bounded planner diagnostics.
    pub fn module(&self) -> &Name {
        self.context.module()
    }
}

/// Opaque read-only import capability for one retained authoring session.
///
/// The lifetime is borrowed from the session that registered or adopted the
/// context, so the capability cannot outlive its command-local owner.
#[derive(Clone, Debug)]
pub struct LocalAuthoringImportContext<'session> {
    context: Rc<LocalAuthoringModuleContext>,
    session_marker: Rc<()>,
    _session: PhantomData<&'session LocalAuthoringVerifierSession>,
}

impl LocalAuthoringImportContext<'_> {
    /// Return the certificate format represented by this authoring context.
    pub fn certificate_format(&self) -> &str {
        self.context.certificate_format()
    }

    /// Return the core specification represented by this authoring context.
    pub fn core_spec(&self) -> &str {
        self.context.core_spec()
    }

    /// Return the module identity represented by this authoring context.
    pub fn module(&self) -> &Name {
        self.context.module()
    }

    /// Return the canonical import table represented by this authoring context.
    pub fn imports(&self) -> &[ImportEntry] {
        self.context.imports()
    }

    /// Return the canonical name table needed by authoring-only projections.
    pub fn name_table(&self) -> &[Name] {
        self.context.name_table()
    }

    /// Return the canonical level table needed by authoring-only projections.
    pub fn level_table(&self) -> &[LevelNode] {
        self.context.level_table()
    }

    /// Return the canonical term table needed by authoring-only projections.
    pub fn term_table(&self) -> &[TermNode] {
        self.context.term_table()
    }

    /// Return declaration certificates needed by authoring-only projections.
    pub fn declarations(&self) -> &[DeclCert] {
        self.context.declarations()
    }

    /// Return the module export hash.
    pub fn export_hash(&self) -> Hash {
        self.context.export_hash()
    }

    /// Return the canonical certificate hash.
    pub fn certificate_hash(&self) -> Hash {
        self.context.certificate_hash()
    }

    /// Return the public export block needed by authoring-only projections.
    pub fn export_block(&self) -> &[ExportEntry] {
        self.context.export_block()
    }

    /// Return the untrusted/recomputed authoring axiom report.
    pub fn axiom_report(&self) -> &AxiomReport {
        self.context.axiom_report()
    }

    /// Reconstruct the read-only kernel declarations needed by authoring.
    ///
    /// This returns declaration data, not a kernel environment or verification
    /// capability. The caller must keep using the authoring-only path.
    pub fn kernel_declarations(&self) -> Result<Vec<npa_kernel::Decl>> {
        crate::certificate_import_to_kernel_decls(self.context.as_ref())
    }

    /// Reconstruct one certificate term for an authoring-only interface projection.
    pub fn term_expression(&self, term: crate::TermId) -> Result<npa_kernel::Expr> {
        let context: &dyn CertificateImportView = self.context.as_ref();
        crate::expr_from_term(context, term)
    }

    /// Return whether this context's closure used any cached context.
    pub fn closure_used_cached_context(&self) -> bool {
        self.context.closure_used_cached_context()
    }

    /// An authoring context alone can never authorize cache publication.
    ///
    /// Live modules may independently satisfy a writer's ordinary-evidence
    /// predicate, but projecting one into this type deliberately discards that
    /// capability.
    pub const fn is_publication_eligible(&self) -> bool {
        false
    }

    /// Local-authoring contexts never constitute proof evidence.
    pub const fn is_proof_evidence(&self) -> bool {
        false
    }
}

/// Non-authoritative observations from one local-authoring build.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalAuthoringBuildObservations {
    import_contexts: usize,
    closure_used_cached_context: bool,
}

impl LocalAuthoringBuildObservations {
    /// Return the number of exact import contexts supplied to the build.
    pub fn import_contexts(&self) -> usize {
        self.import_contexts
    }

    /// Return whether any cached context affected the build closure.
    pub fn closure_used_cached_context(&self) -> bool {
        self.closure_used_cached_context
    }

    /// Local-authoring observations never constitute proof evidence.
    pub const fn is_proof_evidence(&self) -> bool {
        false
    }
}

/// In-memory certificate built against local-authoring imports and not yet rechecked.
#[derive(Debug)]
pub struct LocalAuthoringBuiltCertificate {
    certificate: ModuleCert,
    certificate_bytes: Vec<u8>,
    observations: LocalAuthoringBuildObservations,
}

impl LocalAuthoringBuiltCertificate {
    /// Borrow the in-memory certificate for non-authoritative metadata extraction.
    pub fn certificate(&self) -> &ModuleCert {
        &self.certificate
    }

    /// Return the ephemeral canonical bytes generated for authoring comparison.
    pub fn certificate_bytes(&self) -> &[u8] {
        &self.certificate_bytes
    }

    /// Return non-authoritative build observations.
    pub fn observations(&self) -> &LocalAuthoringBuildObservations {
        &self.observations
    }

    /// In-memory authoring output never constitutes proof evidence.
    pub const fn is_proof_evidence(&self) -> bool {
        false
    }
}

/// Freshly checked authoring result and command-local import context.
#[derive(Debug)]
pub struct LocalAuthoringModuleBuild<'session> {
    certificate_bytes: Vec<u8>,
    observations: LocalAuthoringBuildObservations,
    context: LocalAuthoringImportContext<'session>,
}

impl<'session> LocalAuthoringModuleBuild<'session> {
    /// Return the ephemeral generated certificate bytes.
    pub fn certificate_bytes(&self) -> &[u8] {
        &self.certificate_bytes
    }

    /// Return non-authoritative authoring observations.
    pub fn observations(&self) -> &LocalAuthoringBuildObservations {
        &self.observations
    }

    /// Borrow the fresh context for later authoring in the same session.
    pub fn context(&self) -> &LocalAuthoringImportContext<'session> {
        &self.context
    }

    /// Local-authoring builds never constitute proof evidence.
    pub const fn is_proof_evidence(&self) -> bool {
        false
    }

    /// Separate the ephemeral bytes, observations, and fresh context.
    ///
    /// None of these values can be promoted to [`VerifiedModule`] or used as a
    /// cache-publication capability.
    pub fn into_parts(
        self,
    ) -> (
        Vec<u8>,
        LocalAuthoringBuildObservations,
        LocalAuthoringImportContext<'session>,
    ) {
        (self.certificate_bytes, self.observations, self.context)
    }
}

/// Retained command-local session for structurally reconstructed and fresh contexts.
///
/// ```compile_fail
/// use npa_cert::{
///     LocalAuthoringImportContext, LocalAuthoringVerifierSession, VerifiedModule,
/// };
///
/// fn escape<'a>(module: &VerifiedModule) -> LocalAuthoringImportContext<'a> {
///     let session = LocalAuthoringVerifierSession::new();
///     session.register_verified_module(module)
/// }
/// ```
///
/// ```compile_fail
/// use npa_cert::{LocalAuthoringImportContext, VerifiedModule};
///
/// fn promote(context: LocalAuthoringImportContext<'_>) -> VerifiedModule {
///     context.into()
/// }
/// ```
///
/// ```compile_fail
/// use npa_cert::{LocalAuthoringModuleBuild, VerifiedModule};
///
/// fn promote(build: LocalAuthoringModuleBuild<'_>) -> VerifiedModule {
///     build.into()
/// }
/// ```
///
/// ```compile_fail
/// use npa_cert::{
///     verify_module_cert_with_import_refs, AxiomPolicy, LocalAuthoringImportContext,
/// };
///
/// fn ordinary_loader(bytes: &[u8], cached: &LocalAuthoringImportContext<'_>) {
///     let _ = verify_module_cert_with_import_refs(bytes, &[cached], &AxiomPolicy::normal());
/// }
/// ```
///
/// ```compile_fail
/// use npa_cert::PendingLocalAuthoringContext;
///
/// fn forge() -> PendingLocalAuthoringContext {
///     PendingLocalAuthoringContext { context: panic!("untrusted context") }
/// }
/// ```
#[derive(Debug, Default)]
pub struct LocalAuthoringVerifierSession {
    marker: Rc<()>,
}

impl LocalAuthoringVerifierSession {
    /// Create an empty command-local authoring session.
    pub fn new() -> Self {
        Self::default()
    }

    /// Project and retain a live verified module as a one-way authoring context.
    pub fn register_verified_module<'session>(
        &'session self,
        module: &VerifiedModule,
    ) -> LocalAuthoringImportContext<'session> {
        self.retain(LocalAuthoringModuleContext::from_verified(module))
    }

    /// Project shared live evidence into a one-way authoring context without
    /// cloning its verified-module backing owner.
    ///
    /// Dropping the last returned context releases this session's shared owner;
    /// the context still cannot be converted back into [`VerifiedModule`].
    pub fn register_shared_verified_module<'session>(
        &'session self,
        module: Arc<VerifiedModule>,
    ) -> LocalAuthoringImportContext<'session> {
        self.retain(LocalAuthoringModuleContext::from_shared_verified(module))
    }

    /// Reconstruct a pending context from exact current certificate bytes.
    ///
    /// This performs bounded canonical decode, byte/identity/import/feature and
    /// policy checks. It deliberately skips recursive dependency verification
    /// and the cached module's kernel check.
    pub fn reconstruct_pending_context(
        &self,
        current_bytes: &[u8],
        expected: &LocalAuthoringReconstructionIdentity,
        interface: &LocalAuthoringInterfaceIdentity,
        imports: &[&LocalAuthoringImportContext<'_>],
        policy: &AxiomPolicy,
    ) -> Result<PendingLocalAuthoringContext> {
        let import_views = self.import_views(imports)?;
        let (certificate, structural_closure) = verify::reconstruct_local_authoring_context(
            current_bytes,
            expected,
            interface,
            &import_views,
            policy,
        )?;
        Ok(PendingLocalAuthoringContext {
            context: LocalAuthoringModuleContext::from_cert(certificate, structural_closure, true),
        })
    }

    /// Reconstruct a pending context against ordinary live evidence and other
    /// still-unadopted pending contexts.
    ///
    /// This cache-planning seam keeps prerequisite hits unregistered until
    /// subtree promotion can no longer bypass them. Neither input kind can be
    /// converted through this API, and the returned context remains pending.
    pub fn reconstruct_pending_context_with_unadopted_imports(
        &self,
        current_bytes: &[u8],
        expected: &LocalAuthoringReconstructionIdentity,
        interface: &LocalAuthoringInterfaceIdentity,
        verified_imports: &[&VerifiedModule],
        pending_imports: &[&PendingLocalAuthoringContext],
        policy: &AxiomPolicy,
    ) -> Result<PendingLocalAuthoringContext> {
        let mut import_views: Vec<&dyn CertificateImportView> =
            Vec::with_capacity(verified_imports.len().saturating_add(pending_imports.len()));
        import_views.extend(
            verified_imports
                .iter()
                .map(|module| *module as &dyn CertificateImportView),
        );
        import_views.extend(
            pending_imports
                .iter()
                .map(|pending| &pending.context as &dyn CertificateImportView),
        );
        let (certificate, structural_closure) = verify::reconstruct_local_authoring_context(
            current_bytes,
            expected,
            interface,
            &import_views,
            policy,
        )?;
        Ok(PendingLocalAuthoringContext {
            context: LocalAuthoringModuleContext::from_cert(certificate, structural_closure, true),
        })
    }

    /// Infallibly adopt an already reconstructed pending context by move.
    pub fn adopt_pending_context<'session>(
        &'session self,
        pending: PendingLocalAuthoringContext,
    ) -> LocalAuthoringImportContext<'session> {
        self.retain(pending.context)
    }

    /// Build an in-memory certificate against authoring-only import contexts.
    pub fn build_module_cert(
        &self,
        module: CoreModule,
        imports: &[&LocalAuthoringImportContext<'_>],
        preferred_imports: &BTreeMap<Name, ImportEntry>,
    ) -> Result<LocalAuthoringBuiltCertificate> {
        let import_views = self.import_views(imports)?;
        let certificate =
            canonical::build_module_cert_from_context_refs_with_preferred_imports_impl(
                module,
                &import_views,
                preferred_imports,
            )?;
        let certificate_bytes = crate::encode_module_cert(&certificate)?;
        Ok(LocalAuthoringBuiltCertificate {
            certificate,
            certificate_bytes,
            observations: LocalAuthoringBuildObservations {
                import_contexts: imports.len(),
                closure_used_cached_context: imports
                    .iter()
                    .any(|context| context.context.closure_used_cached_context()),
            },
        })
    }

    /// Recheck a freshly built certificate and retain its fresh authoring context.
    pub fn check_built_module_cert<'session>(
        &'session self,
        mut built: LocalAuthoringBuiltCertificate,
        imports: &[&LocalAuthoringImportContext<'_>],
        policy: &AxiomPolicy,
    ) -> Result<LocalAuthoringModuleBuild<'session>> {
        let import_views = self.import_views(imports)?;
        let structural_closure = verify::verify_built_local_authoring_module_cert(
            &built.certificate,
            &import_views,
            policy,
            KernelExecutionOptions::default(),
        )?;
        built.observations.closure_used_cached_context |= imports
            .iter()
            .any(|context| context.context.closure_used_cached_context());
        let context = self.retain(LocalAuthoringModuleContext::from_cert(
            built.certificate,
            structural_closure,
            built.observations.closure_used_cached_context,
        ));
        Ok(LocalAuthoringModuleBuild {
            certificate_bytes: built.certificate_bytes,
            observations: built.observations,
            context,
        })
    }

    fn retain<'session>(
        &'session self,
        context: LocalAuthoringModuleContext,
    ) -> LocalAuthoringImportContext<'session> {
        let context = Rc::new(context);
        LocalAuthoringImportContext {
            context,
            session_marker: Rc::clone(&self.marker),
            _session: PhantomData,
        }
    }

    fn import_views<'a>(
        &self,
        imports: &'a [&'a LocalAuthoringImportContext<'_>],
    ) -> Result<Vec<&'a dyn CertificateImportView>> {
        let mut views: Vec<&'a dyn CertificateImportView> = Vec::with_capacity(imports.len());
        for context in imports {
            if !Rc::ptr_eq(&self.marker, &context.session_marker) {
                return Err(crate::CertError::ImportNotVerifiedInSession {
                    module: context.context.module().clone(),
                });
            }
            views.push(context.context.as_ref());
        }
        Ok(views)
    }
}

pub(crate) fn certificate_file_hash(bytes: &[u8]) -> Hash {
    let digest = Sha256::digest(bytes);
    let mut hash = [0_u8; 32];
    hash.copy_from_slice(&digest);
    hash
}

//! Private targeted-authoring compile and Human-interface cache adapters.

// The local-hit command boundary is intentionally private to npa-cli. Later
// cache-planning tasks extend these closed types without exposing an
// authoring-context-to-live-evidence conversion.
#![allow(dead_code)]

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
    path::Path,
    sync::Arc,
    time::Instant,
};

use npa_cert::{
    AxiomPolicy, ImportEntry, LocalAuthoringBuildObservations, LocalAuthoringImportContext,
    LocalAuthoringInterfaceIdentity, LocalAuthoringReconstructionIdentity,
    LocalAuthoringVerifierSession, Name, PendingLocalAuthoringContext, VerifiedModule,
};
use npa_frontend::{
    compile_human_source_to_authoring_certificate_output_with_available_imports_and_axiom_policy,
    DefinitionReducibility, FileId, HumanAuthoringCertificateCompileOutput, HumanAuthoringImport,
    HumanBinderInfo, HumanCompilationObservations, HumanCompileOptions,
    HumanGeneratedDeclarationKind, HumanGeneratedDeclarationMetadata, HumanImportedSourceInterface,
    HumanName, HumanNotationAssociativity, HumanNotationKind, HumanResult,
    HumanSourceBinderMetadata, HumanSourceDeclarationKind, HumanSourceDeclarationMetadata,
    HumanSourceInterface, HumanSourceNotationMetadata, HumanTypeclassClassMetadata,
    HumanTypeclassFieldMetadata, HumanTypeclassInstanceMetadata, HumanUniverseParam, Span,
};
use npa_kernel::KernelWorkCounterSink;
use npa_package::{
    package_file_hash, refresh_targeted_authoring_support_context_entry,
    validate_targeted_authoring_support_context_source_bytes, PackageCacheNamespaceDigest,
    PackageGraph, PackageHash, PackageId, PackageModule, PackageVersion,
    ResolvedModuleImportIdentity, ResolvedModuleImportKind,
    TargetedAuthoringAcceptedCertificateIdentity, TargetedAuthoringCacheError,
    TargetedAuthoringDefinitionReducibility, TargetedAuthoringExternalModuleInput,
    TargetedAuthoringHumanBinder, TargetedAuthoringHumanBinderInfo,
    TargetedAuthoringHumanDeclaration, TargetedAuthoringHumanDeclarationKind,
    TargetedAuthoringHumanGeneratedDeclaration, TargetedAuthoringHumanGeneratedDeclarationKind,
    TargetedAuthoringHumanImportedSourceInterface, TargetedAuthoringHumanName,
    TargetedAuthoringHumanNotation, TargetedAuthoringHumanNotationAssociativity,
    TargetedAuthoringHumanNotationKind, TargetedAuthoringHumanSourceInterface,
    TargetedAuthoringHumanTypeclassClass, TargetedAuthoringHumanTypeclassField,
    TargetedAuthoringHumanTypeclassInstance, TargetedAuthoringHumanUniverseParameter,
    TargetedAuthoringIncrementalSupportKey, TargetedAuthoringInterfaceProfile,
    TargetedAuthoringLocalModuleInput, TargetedAuthoringSourceIdentity, TargetedAuthoringSpan,
    TargetedAuthoringSpanOrigin, TargetedAuthoringSupportContextEntry,
    TargetedAuthoringSupportKeyAccumulator, TargetedAuthoringSupportKeyContext,
    PACKAGE_TARGETED_AUTHORING_HUMAN_INTERFACE_SCHEMA,
    PACKAGE_TARGETED_AUTHORING_LIVE_CLOSURE_CLAIM, PACKAGE_TARGETED_AUTHORING_POLICY,
    PACKAGE_TARGETED_AUTHORING_SUPPORT_CONTEXT_SCHEMA,
    PACKAGE_TARGETED_AUTHORING_SUPPORT_TRUST_BOUNDARY, TARGETED_AUTHORING_CACHE_LIMITS_V1,
};

use npa_api::{
    PerformanceMeasurementLabel, PerformanceMeasurementRecorder,
    LEGACY_STD_PACKAGE_PRODUCER_PROFILE, STD_PACKAGE_PRODUCER_PROFILE,
};

use crate::{
    diagnostic::{CommandDiagnostic, CommandResult, DiagnosticKind},
    package::LoadedPackageRoot,
    package_build_cache::{
        prepare_targeted_authoring_support_cache_session,
        targeted_authoring_semantic_compiler_options, TargetedAuthoringSupportCacheSession,
        TargetedAuthoringSupportContextPublishOutcome, TargetedAuthoringSupportContextStoreBudget,
        TargetedAuthoringSupportContextStoreLookup,
        TargetedAuthoringSupportContextWriterValidation,
        TARGETED_AUTHORING_INTERFACE_RECONSTRUCTION_VERSION,
    },
};

const HUMAN_SOURCE_PRODUCER_PROFILE: &str = "human-surface-explicit-term";
const TARGETED_AUTHORING_LOCAL_ONLY_REASON: &str = "targeted_authoring_cache_local_only";
const TARGETED_AUTHORING_LOCAL_ONLY_FIELD: &str = "targeted_authoring_cache";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum TargetedAuthoringPublicationOrigin {
    TargetedReadThroughSupport,
    TargetedLocalHitSupport,
    FullReadThroughRetainedModule,
    ExplicitTarget,
    PostTargetSupport,
    FullReadThroughUnretainedModule,
}

impl TargetedAuthoringPublicationOrigin {
    const fn is_allowed(self) -> bool {
        matches!(
            self,
            Self::TargetedReadThroughSupport
                | Self::TargetedLocalHitSupport
                | Self::FullReadThroughRetainedModule
        )
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TargetedAuthoringAcceptanceKind {
    CheckedCertificate,
    FullSourceBuild,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct TargetedAuthoringModuleAcceptance {
    kind: TargetedAuthoringAcceptanceKind,
    completed: u16,
}

impl TargetedAuthoringModuleAcceptance {
    const SOURCE_PIN: u16 = 1 << 0;
    const CERTIFICATE_PIN: u16 = 1 << 1;
    const AXIOM_POLICY: u16 = 1 << 2;
    const LIVE_VERIFICATION: u16 = 1 << 3;
    const MODULE_AND_IMPORT_TABLE: u16 = 1 << 4;
    const INTERFACE_DRIFT: u16 = 1 << 5;
    const INTERFACE_RECONSTRUCTION: u16 = 1 << 6;
    const OBSERVABLE_IMPORTS: u16 = 1 << 7;
    const GENERATED_MANIFEST_HASHES: u16 = 1 << 8;
    const CHECKED_IN_CERTIFICATE_BYTES: u16 = 1 << 9;

    const CHECKED_CERTIFICATE_REQUIRED: u16 = Self::SOURCE_PIN
        | Self::CERTIFICATE_PIN
        | Self::AXIOM_POLICY
        | Self::LIVE_VERIFICATION
        | Self::MODULE_AND_IMPORT_TABLE
        | Self::INTERFACE_DRIFT
        | Self::INTERFACE_RECONSTRUCTION;
    const FULL_SOURCE_REQUIRED: u16 = Self::CHECKED_CERTIFICATE_REQUIRED
        | Self::OBSERVABLE_IMPORTS
        | Self::GENERATED_MANIFEST_HASHES
        | Self::CHECKED_IN_CERTIFICATE_BYTES;

    pub(crate) const fn checked_certificate_complete() -> Self {
        Self {
            kind: TargetedAuthoringAcceptanceKind::CheckedCertificate,
            completed: Self::CHECKED_CERTIFICATE_REQUIRED,
        }
    }

    pub(crate) const fn full_source_complete() -> Self {
        Self {
            kind: TargetedAuthoringAcceptanceKind::FullSourceBuild,
            completed: Self::FULL_SOURCE_REQUIRED,
        }
    }

    const fn is_complete(self) -> bool {
        let required = match self.kind {
            TargetedAuthoringAcceptanceKind::CheckedCertificate => {
                Self::CHECKED_CERTIFICATE_REQUIRED
            }
            TargetedAuthoringAcceptanceKind::FullSourceBuild => Self::FULL_SOURCE_REQUIRED,
        };
        self.completed & required == required
    }
}

#[derive(Debug)]
pub(crate) struct TargetedAuthoringSupportPublicationPlanner {
    namespace: Option<PackageCacheNamespaceDigest>,
    context: Option<TargetedAuthoringSupportKeyContext>,
    accumulator: Option<TargetedAuthoringSupportKeyAccumulator>,
    budget: TargetedAuthoringSupportContextStoreBudget,
    entries_written: usize,
    diagnostics: Vec<CommandDiagnostic>,
    detailed_diagnostics: bool,
}

impl TargetedAuthoringSupportPublicationPlanner {
    pub(crate) fn disabled(reason: &'static str, detailed_diagnostics: bool) -> Self {
        Self {
            namespace: None,
            context: None,
            accumulator: None,
            budget: TargetedAuthoringSupportContextStoreBudget::new(),
            entries_written: 0,
            diagnostics: vec![targeted_authoring_publication_diagnostic(None, reason)],
            detailed_diagnostics,
        }
    }

    pub(crate) fn new(
        namespace: Option<PackageCacheNamespaceDigest>,
        toolchain: Option<npa_package::TargetedAuthoringToolchainIdentity>,
        external_inputs: Vec<TargetedAuthoringExternalModuleInput>,
        policy: &AxiomPolicy,
        detailed_diagnostics: bool,
    ) -> Self {
        let mut diagnostics = Vec::new();
        let (context, accumulator) = match (namespace.as_ref(), toolchain) {
            (Some(_), Some(toolchain)) => {
                match TargetedAuthoringSupportKeyAccumulator::new(external_inputs) {
                    Ok(accumulator) => (
                        Some(targeted_authoring_support_key_context(toolchain, policy)),
                        Some(accumulator),
                    ),
                    Err(_) => {
                        diagnostics.push(targeted_authoring_publication_diagnostic(
                            None,
                            "key_planning_unavailable",
                        ));
                        (None, None)
                    }
                }
            }
            _ => (None, None),
        };
        Self {
            namespace,
            context,
            accumulator,
            budget: TargetedAuthoringSupportContextStoreBudget::new(),
            entries_written: 0,
            diagnostics,
            detailed_diagnostics,
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn observe_local(
        &mut self,
        loaded: &LoadedPackageRoot,
        module_index: usize,
        artifact: TargetedAuthoringLocalModuleInput,
        source: &str,
        interface: &HumanImportedSourceInterface,
        verified: &VerifiedModule,
        origin: TargetedAuthoringPublicationOrigin,
        closure_used_cached_context: bool,
        acceptance: TargetedAuthoringModuleAcceptance,
    ) -> Option<TargetedAuthoringSupportContextEntry> {
        let (Some(namespace), Some(context), Some(accumulator)) = (
            self.namespace.as_ref(),
            self.context.as_ref(),
            self.accumulator.as_mut(),
        ) else {
            return None;
        };
        let construct_key = origin.is_allowed();
        let planned = match accumulator.push_local(
            &loaded.validated,
            context,
            module_index,
            artifact,
            construct_key,
        ) {
            Ok(planned) => planned,
            Err(_) => {
                self.record_publication_failure(module_index, "key_construction_failed");
                self.context = None;
                self.accumulator = None;
                return None;
            }
        };
        let planned = planned?;
        match build_accepted_targeted_authoring_support_entry(
            loaded,
            module_index,
            namespace,
            &planned,
            source,
            interface,
            verified,
            origin,
            closure_used_cached_context,
            acceptance,
        ) {
            Ok(entry) => Some(entry),
            Err(reason) => {
                self.record_ineligible(module_index, reason);
                None
            }
        }
    }

    pub(crate) fn budget_mut(&mut self) -> &mut TargetedAuthoringSupportContextStoreBudget {
        &mut self.budget
    }

    pub(crate) fn record_publish_outcome(
        &mut self,
        module_index: usize,
        outcome: TargetedAuthoringSupportContextPublishOutcome,
    ) {
        match outcome {
            TargetedAuthoringSupportContextPublishOutcome::Published => {
                self.entries_written = self.entries_written.saturating_add(1);
            }
            TargetedAuthoringSupportContextPublishOutcome::ExistingEqual => {}
            TargetedAuthoringSupportContextPublishOutcome::Conflict(validation) => {
                self.record_publication_collision(module_index, validation);
            }
            TargetedAuthoringSupportContextPublishOutcome::Invalid => {
                self.record_publication_failure(module_index, "publication_invalid")
            }
            TargetedAuthoringSupportContextPublishOutcome::Unavailable => {
                self.record_publication_failure(module_index, "publication_unavailable")
            }
        }
    }

    pub(crate) fn entries_written(&self) -> usize {
        self.entries_written
    }

    pub(crate) fn observed_cache_bytes(&self) -> (usize, usize) {
        (
            self.budget.loaded_bytes(),
            self.budget.written_bytes_for_summary(),
        )
    }

    pub(crate) fn take_diagnostics(&mut self) -> Vec<CommandDiagnostic> {
        std::mem::take(&mut self.diagnostics)
    }

    fn record_ineligible(&mut self, module_index: usize, reason: &'static str) {
        if self.diagnostics.len() >= TARGETED_AUTHORING_CACHE_LIMITS_V1.detailed_diagnostics {
            return;
        }
        self.diagnostics.push(
            CommandDiagnostic::info(
                DiagnosticKind::GeneratedArtifact,
                "targeted_authoring_module_ineligible",
            )
            .with_path(format!("modules[{module_index}]"))
            .with_field("targeted_authoring_cache")
            .with_actual_value(reason),
        );
    }

    fn record_publication_failure(&mut self, module_index: usize, reason: &'static str) {
        if self.diagnostics.len() >= TARGETED_AUTHORING_CACHE_LIMITS_V1.detailed_diagnostics {
            return;
        }
        self.diagnostics
            .push(targeted_authoring_publication_diagnostic(
                Some(module_index),
                reason,
            ));
    }

    fn record_publication_collision(
        &mut self,
        module_index: usize,
        validation: TargetedAuthoringSupportContextWriterValidation,
    ) {
        if !self.detailed_diagnostics
            || self.diagnostics.len() >= TARGETED_AUTHORING_CACHE_LIMITS_V1.detailed_diagnostics
        {
            return;
        }
        let reason_code = match validation {
            TargetedAuthoringSupportContextWriterValidation::Stale => {
                "targeted_authoring_cache_entry_stale"
            }
            TargetedAuthoringSupportContextWriterValidation::Invalid => {
                "targeted_authoring_cache_entry_invalid"
            }
        };
        self.diagnostics.push(
            CommandDiagnostic::info(DiagnosticKind::GeneratedArtifact, reason_code)
                .with_path(format!("modules[{module_index}]"))
                .with_field("targeted_authoring_cache")
                .with_actual_value("operation=publication_collision"),
        );
    }
}

fn targeted_authoring_publication_diagnostic(
    module_index: Option<usize>,
    reason: &'static str,
) -> CommandDiagnostic {
    let diagnostic = CommandDiagnostic::info(
        DiagnosticKind::GeneratedArtifact,
        "targeted_authoring_cache_publication_failed",
    )
    .with_field("targeted_authoring_cache")
    .with_actual_value(reason);
    match module_index {
        Some(index) => diagnostic.with_path(format!("modules[{index}]")),
        None => diagnostic,
    }
}

fn targeted_authoring_support_key_context(
    toolchain: npa_package::TargetedAuthoringToolchainIdentity,
    policy: &AxiomPolicy,
) -> TargetedAuthoringSupportKeyContext {
    TargetedAuthoringSupportKeyContext {
        toolchain,
        default_producer_profile: HUMAN_SOURCE_PRODUCER_PROFILE.to_owned(),
        semantic_compiler_options: targeted_authoring_semantic_compiler_options(),
        axiom_policy_hash: PackageHash::from(policy.policy_hash()),
        source_interface_schema: PACKAGE_TARGETED_AUTHORING_HUMAN_INTERFACE_SCHEMA.to_owned(),
        source_interface_reconstruction_version:
            TARGETED_AUTHORING_INTERFACE_RECONSTRUCTION_VERSION.to_owned(),
    }
}

#[allow(clippy::too_many_arguments)]
fn build_accepted_targeted_authoring_support_entry(
    loaded: &LoadedPackageRoot,
    module_index: usize,
    namespace: &PackageCacheNamespaceDigest,
    planned: &TargetedAuthoringIncrementalSupportKey,
    source: &str,
    interface: &HumanImportedSourceInterface,
    verified: &VerifiedModule,
    origin: TargetedAuthoringPublicationOrigin,
    closure_used_cached_context: bool,
    acceptance: TargetedAuthoringModuleAcceptance,
) -> Result<TargetedAuthoringSupportContextEntry, &'static str> {
    let module = loaded
        .validated
        .manifest()
        .modules
        .get(module_index)
        .ok_or("module_index_out_of_range")?;
    let producer_profile = module
        .producer_profile
        .as_deref()
        .unwrap_or(HUMAN_SOURCE_PRODUCER_PROFILE);
    validate_targeted_authoring_publication_gate(
        origin,
        closure_used_cached_context,
        acceptance,
        producer_profile,
    )?;
    if planned.key_input.producer_profile != producer_profile {
        return Err("producer_profile_identity_mismatch");
    }
    if package_file_hash(source.as_bytes()) != planned.key_input.current_source_hash
        || verified.module() != &planned.key_input.module
        || PackageHash::from(verified.export_hash()) != planned.key_input.actual_export_hash
        || PackageHash::from(verified.certificate_hash())
            != planned.key_input.actual_certificate_hash
        || planned.closure_commitment != planned.key_input.dependency_closure_commitment
    {
        return Err("accepted_identity_mismatch");
    }
    let authoring_import = HumanAuthoringImport::from_verified_module(verified);
    let adapter = HumanInterfaceCacheAdapterContext::new(
        &loaded.validated.manifest().package,
        &loaded.validated.manifest().version,
        HUMAN_SOURCE_PRODUCER_PROFILE,
        &planned.key_input.manifest_human_imports,
        module_index,
        source,
        &authoring_import,
    );
    let source_interface =
        human_interface_to_cache_dto(interface, &adapter).map_err(|error| error.reason_code())?;
    refresh_targeted_authoring_support_context_entry(&TargetedAuthoringSupportContextEntry {
        schema: PACKAGE_TARGETED_AUTHORING_SUPPORT_CONTEXT_SCHEMA.to_owned(),
        cache_key: planned.cache_key.clone(),
        namespace: namespace.clone(),
        key_input: planned.key_input.clone(),
        closure_commitment: planned.closure_commitment,
        producer_profile: HUMAN_SOURCE_PRODUCER_PROFILE.to_owned(),
        interface_profile: TargetedAuthoringInterfaceProfile::HumanSource,
        authoring_policy: PACKAGE_TARGETED_AUTHORING_POLICY.to_owned(),
        accepted_certificate: TargetedAuthoringAcceptedCertificateIdentity {
            module: planned.key_input.module.clone(),
            certificate_file_hash: planned.key_input.current_certificate_file_hash,
            export_hash: planned.key_input.actual_export_hash,
            axiom_report_hash: planned.key_input.actual_axiom_report_hash,
            certificate_hash: planned.key_input.actual_certificate_hash,
        },
        source_interface,
        integrity_digest: PackageHash::new([0; 32]),
        trusted: false,
        build_evidence: false,
        proof_evidence: false,
        live_closure_eligibility: PACKAGE_TARGETED_AUTHORING_LIVE_CLOSURE_CLAIM.to_owned(),
        trust_boundary: PACKAGE_TARGETED_AUTHORING_SUPPORT_TRUST_BOUNDARY.to_owned(),
    })
    .map_err(|_| "canonical_entry_invalid")
}

fn validate_targeted_authoring_publication_gate(
    origin: TargetedAuthoringPublicationOrigin,
    closure_used_cached_context: bool,
    acceptance: TargetedAuthoringModuleAcceptance,
    producer_profile: &str,
) -> Result<(), &'static str> {
    if !origin.is_allowed() {
        return Err("writer_origin_ineligible");
    }
    if closure_used_cached_context {
        return Err("closure_used_cached_context");
    }
    if !acceptance.is_complete() {
        return Err("module_acceptance_incomplete");
    }
    if producer_profile != HUMAN_SOURCE_PRODUCER_PROFILE {
        return Err("unsupported_producer_profile");
    }
    Ok(())
}

#[derive(Debug, Default)]
pub(crate) struct TargetedAuthoringBuildSession {
    verifier: LocalAuthoringVerifierSession,
}

impl TargetedAuthoringBuildSession {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn register_verified_module<'session>(
        &'session self,
        module: &VerifiedModule,
    ) -> npa_cert::Result<HumanAuthoringImport<'session>> {
        let context = self.verifier.register_verified_module(module);
        HumanAuthoringImport::from_local_authoring_context(&context)
    }

    pub(crate) fn register_live_support<'session>(
        &'session self,
        module: &VerifiedModule,
    ) -> TargetedAuthoringImportContext<'session> {
        TargetedAuthoringImportContext::LiveSupport(LiveTargetedSupportContext {
            context: self.verifier.register_verified_module(module),
        })
    }

    pub(crate) fn register_shared_live_support<'session>(
        &'session self,
        module: Arc<VerifiedModule>,
    ) -> TargetedAuthoringImportContext<'session> {
        TargetedAuthoringImportContext::LiveSupport(LiveTargetedSupportContext {
            context: self.verifier.register_shared_verified_module(module),
        })
    }

    pub(crate) fn register_shared_fresh_target<'session>(
        &'session self,
        module: Arc<VerifiedModule>,
    ) -> TargetedAuthoringImportContext<'session> {
        TargetedAuthoringImportContext::FreshTarget(FreshTargetedAuthoringContext {
            context: self.verifier.register_shared_verified_module(module),
        })
    }

    pub(crate) fn adopt_cached_support<'session>(
        &'session self,
        pending: PendingLocalAuthoringContext,
    ) -> TargetedAuthoringImportContext<'session> {
        TargetedAuthoringImportContext::CachedSupport(CachedTargetedSupportContext {
            context: self.verifier.adopt_pending_context(pending),
        })
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn compile_human_target<'session>(
        &'session self,
        file_id: FileId,
        module_name: Name,
        source: &str,
        direct_authoring_imports: &[HumanAuthoringImport<'session>],
        available_authoring_imports: &[HumanAuthoringImport<'session>],
        imported_source_interfaces: &[HumanImportedSourceInterface],
        options: &HumanCompileOptions,
        axiom_policy: &AxiomPolicy,
        work_counter_sink: Option<&KernelWorkCounterSink>,
        collect_declaration_details: bool,
    ) -> HumanResult<TargetedAuthoringModuleBuild<'session>> {
        compile_human_source_to_authoring_certificate_output_with_available_imports_and_axiom_policy(
            &self.verifier,
            file_id,
            module_name,
            source,
            direct_authoring_imports,
            available_authoring_imports,
            imported_source_interfaces,
            options,
            axiom_policy,
            work_counter_sink,
            collect_declaration_details,
        )
        .map(TargetedAuthoringModuleBuild::from_frontend)
    }
}

#[derive(Clone, Debug)]
pub(crate) enum TargetedAuthoringImportContext<'session> {
    LiveSupport(LiveTargetedSupportContext<'session>),
    CachedSupport(CachedTargetedSupportContext<'session>),
    FreshTarget(FreshTargetedAuthoringContext<'session>),
}

impl<'session> TargetedAuthoringImportContext<'session> {
    pub(crate) fn authoring_import(&self) -> npa_cert::Result<HumanAuthoringImport<'session>> {
        let context = match self {
            Self::LiveSupport(context) => &context.context,
            Self::CachedSupport(context) => &context.context,
            Self::FreshTarget(context) => &context.context,
        };
        HumanAuthoringImport::from_local_authoring_context(context)
    }

    pub(crate) fn closure_used_cached_context(&self) -> bool {
        match self {
            Self::LiveSupport(context) => context.context.closure_used_cached_context(),
            Self::CachedSupport(_) => true,
            Self::FreshTarget(context) => context.closure_used_cached_context(),
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct LiveTargetedSupportContext<'session> {
    context: LocalAuthoringImportContext<'session>,
}

#[derive(Clone, Debug)]
pub(crate) struct CachedTargetedSupportContext<'session> {
    context: LocalAuthoringImportContext<'session>,
}

#[derive(Debug)]
pub(crate) struct TargetedAuthoringCurrentSnapshot {
    source: String,
    certificate_bytes: Vec<u8>,
}

impl TargetedAuthoringCurrentSnapshot {
    pub(crate) fn new(source: String, certificate_bytes: Vec<u8>) -> Self {
        Self {
            source,
            certificate_bytes,
        }
    }

    pub(crate) fn loaded_bytes(&self) -> Option<usize> {
        self.source.len().checked_add(self.certificate_bytes.len())
    }

    pub(crate) fn source(&self) -> &str {
        &self.source
    }

    pub(crate) fn into_parts(self) -> (String, Vec<u8>) {
        (self.source, self.certificate_bytes)
    }
}

#[derive(Debug)]
struct PendingCachedTargetedSupportContext {
    pending: PendingLocalAuthoringContext,
    source_interface: HumanImportedSourceInterface,
    snapshot: TargetedAuthoringCurrentSnapshot,
    retained_bytes: usize,
}

#[derive(Debug)]
pub(crate) struct AdoptedCachedTargetedSupportContext<'session> {
    module_index: usize,
    context: TargetedAuthoringImportContext<'session>,
    source_interface: HumanImportedSourceInterface,
}

impl<'session> AdoptedCachedTargetedSupportContext<'session> {
    pub(crate) fn module_index(&self) -> usize {
        self.module_index
    }

    pub(crate) fn context(&self) -> &TargetedAuthoringImportContext<'session> {
        &self.context
    }

    pub(crate) fn source_interface(&self) -> &HumanImportedSourceInterface {
        &self.source_interface
    }

    pub(crate) fn into_parts(
        self,
    ) -> (
        usize,
        TargetedAuthoringImportContext<'session>,
        HumanImportedSourceInterface,
    ) {
        (self.module_index, self.context, self.source_interface)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TargetedAuthoringLookupMiss {
    Missing,
    Stale,
    SchemaMiss,
    Invalid,
    Unavailable,
}

impl TargetedAuthoringLookupMiss {
    const fn detail_reason(self) -> Option<&'static str> {
        match self {
            Self::Stale => Some("targeted_authoring_cache_entry_stale"),
            Self::SchemaMiss => Some("targeted_authoring_cache_entry_schema_miss"),
            Self::Invalid => Some("targeted_authoring_cache_entry_invalid"),
            Self::Missing | Self::Unavailable => None,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TargetedAuthoringForcedLiveReason {
    ProducerProfile,
    CoreBuilderConsumerRequiresLive,
    PostTargetSupportRequiresLiveOrder,
}

impl TargetedAuthoringForcedLiveReason {
    const fn as_str(self) -> &'static str {
        match self {
            Self::ProducerProfile => "producer_profile",
            Self::CoreBuilderConsumerRequiresLive => "core_builder_consumer_requires_live",
            Self::PostTargetSupportRequiresLiveOrder => "post_target_support_requires_live_order",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TargetedAuthoringInitialRole {
    EligiblePreTargetSupport,
    ForcedLiveSupport(TargetedAuthoringForcedLiveReason),
    FreshTarget,
    ForcedLiveTarget(TargetedAuthoringForcedLiveReason),
}

impl TargetedAuthoringInitialRole {
    const fn forced_live_reason(self) -> Option<TargetedAuthoringForcedLiveReason> {
        match self {
            Self::ForcedLiveSupport(reason) | Self::ForcedLiveTarget(reason) => Some(reason),
            Self::EligiblePreTargetSupport | Self::FreshTarget => None,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TargetedAuthoringProducerProfile {
    HumanSurface,
    StdCoreBuilder,
    Unsupported,
}

impl TargetedAuthoringProducerProfile {
    fn classify(profile: Option<&str>) -> Self {
        match profile.unwrap_or(HUMAN_SOURCE_PRODUCER_PROFILE) {
            HUMAN_SOURCE_PRODUCER_PROFILE => Self::HumanSurface,
            LEGACY_STD_PACKAGE_PRODUCER_PROFILE | STD_PACKAGE_PRODUCER_PROFILE => {
                Self::StdCoreBuilder
            }
            _ => Self::Unsupported,
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct TargetedAuthoringPlannerInput {
    combined_topological_order: Vec<usize>,
    local_dependencies: BTreeMap<usize, Vec<usize>>,
    producer_profiles: BTreeMap<usize, TargetedAuthoringProducerProfile>,
    selected_targets: BTreeSet<usize>,
    selected_support: BTreeSet<usize>,
    external_order: Vec<usize>,
    local_module_count: usize,
    external_module_count: usize,
}

impl TargetedAuthoringPlannerInput {
    pub(crate) fn from_package_graph(
        modules: &[PackageModule],
        graph: &PackageGraph,
        selected_targets: &[usize],
        selected_support: &BTreeSet<usize>,
        external_order: Vec<usize>,
        external_module_count: usize,
    ) -> Result<Self, CommandDiagnostic> {
        if modules.len() != graph.resolved_module_imports.len() {
            return Err(targeted_authoring_plan_invalid("module_table_shape"));
        }
        let selected_targets = selected_targets.iter().copied().collect::<BTreeSet<_>>();
        let selected_local_count = selected_targets
            .len()
            .checked_add(selected_support.len())
            .ok_or_else(|| targeted_authoring_plan_invalid("selected_local_overflow"))?;
        if selected_local_count > TARGETED_AUTHORING_CACHE_LIMITS_V1.closure_modules {
            return Err(targeted_authoring_plan_invalid(
                "selected_local_out_of_bounds",
            ));
        }
        let selected_local = selected_targets
            .union(selected_support)
            .copied()
            .collect::<BTreeSet<_>>();
        if selected_local.iter().any(|index| *index >= modules.len()) {
            return Err(targeted_authoring_plan_invalid(
                "selected_index_out_of_range",
            ));
        }
        let combined_topological_order = graph
            .topological_order
            .iter()
            .copied()
            .filter(|index| selected_local.contains(index))
            .collect::<Vec<_>>();
        let mut local_dependencies = BTreeMap::new();
        let mut dependency_edges = 0usize;
        let mut producer_profiles = BTreeMap::new();
        for &module_index in &selected_local {
            let mut dependencies = Vec::new();
            for import in &graph.resolved_module_imports[module_index] {
                let ResolvedModuleImportKind::Local { module_index } = import.kind else {
                    continue;
                };
                dependency_edges = dependency_edges
                    .checked_add(1)
                    .ok_or_else(|| targeted_authoring_plan_invalid("dependency_edge_overflow"))?;
                if dependency_edges > TARGETED_AUTHORING_CACHE_LIMITS_V1.closure_dependency_edges {
                    return Err(targeted_authoring_plan_invalid(
                        "dependency_edges_out_of_bounds",
                    ));
                }
                dependencies.push(module_index);
            }
            local_dependencies.insert(module_index, dependencies);
            let module = &modules[module_index];
            producer_profiles.insert(
                module_index,
                TargetedAuthoringProducerProfile::classify(module.producer_profile.as_deref()),
            );
        }
        Ok(Self {
            combined_topological_order,
            local_dependencies,
            producer_profiles,
            selected_targets,
            selected_support: selected_support.clone(),
            external_order,
            local_module_count: modules.len(),
            external_module_count,
        })
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct TargetedAuthoringExecutionPlan {
    combined_local_order: Vec<usize>,
    local_dependencies: BTreeMap<usize, Vec<usize>>,
    lifetime_dependencies: BTreeMap<usize, Vec<usize>>,
    pre_target_support: Vec<usize>,
    explicit_targets: Vec<usize>,
    post_target_support: Vec<usize>,
    external_order: Vec<usize>,
    initial_roles: BTreeMap<usize, TargetedAuthoringInitialRole>,
    force_live_local: BTreeSet<usize>,
    forced_live_support: BTreeSet<usize>,
    forced_live_targets: BTreeSet<usize>,
    eligible_support_lookup: Vec<usize>,
    remaining_local_uses: BTreeMap<usize, u64>,
}

impl TargetedAuthoringExecutionPlan {
    pub(crate) fn external_order(&self) -> &[usize] {
        &self.external_order
    }

    pub(crate) fn requests_support_store(&self) -> bool {
        !self.eligible_support_lookup.is_empty()
    }

    pub(crate) fn combined_local_order(&self) -> &[usize] {
        &self.combined_local_order
    }

    pub(crate) fn is_explicit_target(&self, module_index: usize) -> bool {
        matches!(
            self.initial_roles.get(&module_index),
            Some(
                TargetedAuthoringInitialRole::FreshTarget
                    | TargetedAuthoringInitialRole::ForcedLiveTarget(_)
            )
        )
    }

    pub(crate) fn is_forced_live(&self, module_index: usize) -> bool {
        self.force_live_local.contains(&module_index)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct TargetedAuthoringProducerViews {
    ordinary: bool,
    authoring: bool,
}

impl TargetedAuthoringProducerViews {
    const CACHED_SUPPORT: Self = Self {
        ordinary: false,
        authoring: true,
    };
    const LIVE_SUPPORT_OR_FORCED_TARGET: Self = Self {
        ordinary: true,
        authoring: true,
    };
    const FRESH_TARGET: Self = Self {
        ordinary: false,
        authoring: true,
    };
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct TargetedAuthoringProducerLifetime {
    remaining_uses: u64,
    views: TargetedAuthoringProducerViews,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct TargetedAuthoringProducerLifetimeLedger {
    planned_uses: BTreeMap<usize, u64>,
    dependencies: BTreeMap<usize, Vec<usize>>,
    retained: BTreeMap<usize, TargetedAuthoringProducerLifetime>,
    processed_consumers: BTreeSet<usize>,
}

impl TargetedAuthoringProducerLifetimeLedger {
    fn from_execution_plan(plan: &TargetedAuthoringExecutionPlan) -> Self {
        Self {
            planned_uses: plan.remaining_local_uses.clone(),
            dependencies: plan.lifetime_dependencies.clone(),
            retained: BTreeMap::new(),
            processed_consumers: BTreeSet::new(),
        }
    }

    fn register(
        &mut self,
        module_index: usize,
        views: TargetedAuthoringProducerViews,
    ) -> Result<bool, CommandDiagnostic> {
        if self.retained.contains_key(&module_index) {
            return Err(targeted_authoring_plan_invalid(
                "producer_lifetime_registered_twice",
            ));
        }
        let remaining_uses = self
            .planned_uses
            .get(&module_index)
            .copied()
            .unwrap_or_default();
        if remaining_uses == 0 {
            return Ok(false);
        }
        self.retained.insert(
            module_index,
            TargetedAuthoringProducerLifetime {
                remaining_uses,
                views,
            },
        );
        Ok(true)
    }

    fn consume_consumer(&mut self, consumer_index: usize) -> Result<Vec<usize>, CommandDiagnostic> {
        if !self.processed_consumers.insert(consumer_index) {
            return Err(targeted_authoring_plan_invalid(
                "producer_lifetime_consumer_repeated",
            ));
        }
        let dependencies = self
            .dependencies
            .get(&consumer_index)
            .ok_or_else(|| targeted_authoring_plan_invalid("producer_lifetime_row_missing"))?
            .clone();
        let mut release = Vec::new();
        for dependency in dependencies {
            let lifetime = self.retained.get_mut(&dependency).ok_or_else(|| {
                targeted_authoring_plan_invalid("producer_lifetime_dependency_unavailable")
            })?;
            lifetime.remaining_uses = lifetime.remaining_uses.checked_sub(1).ok_or_else(|| {
                targeted_authoring_plan_invalid("producer_lifetime_use_underflow")
            })?;
            if lifetime.remaining_uses == 0 {
                self.retained.remove(&dependency);
                release.push(dependency);
            }
        }
        Ok(release)
    }

    fn retained(&self, module_index: usize) -> Option<TargetedAuthoringProducerLifetime> {
        self.retained.get(&module_index).copied()
    }
}

pub(crate) fn build_targeted_authoring_execution_plan(
    input: TargetedAuthoringPlannerInput,
) -> Result<TargetedAuthoringExecutionPlan, CommandDiagnostic> {
    let module_count = input.local_module_count;
    let selected_local_count = input
        .selected_targets
        .len()
        .checked_add(input.selected_support.len())
        .ok_or_else(|| targeted_authoring_plan_invalid("selected_local_overflow"))?;
    if selected_local_count > TARGETED_AUTHORING_CACHE_LIMITS_V1.closure_modules {
        return Err(targeted_authoring_plan_invalid(
            "selected_local_out_of_bounds",
        ));
    }
    if !input.selected_targets.is_disjoint(&input.selected_support) {
        return Err(targeted_authoring_plan_invalid("target_support_overlap"));
    }
    if input.selected_targets.is_empty() && !input.selected_support.is_empty() {
        return Err(targeted_authoring_plan_invalid("support_without_target"));
    }

    let selected_local = input
        .selected_targets
        .union(&input.selected_support)
        .copied()
        .collect::<BTreeSet<_>>();
    let mut topological_positions = BTreeMap::new();
    for (position, &module_index) in input.combined_topological_order.iter().enumerate() {
        if module_index >= module_count {
            return Err(targeted_authoring_plan_invalid(
                "topological_index_out_of_range",
            ));
        }
        if topological_positions
            .insert(module_index, position)
            .is_some()
        {
            return Err(targeted_authoring_plan_invalid(
                "topological_index_duplicate",
            ));
        }
    }
    if selected_local.iter().any(|index| *index >= module_count) {
        return Err(targeted_authoring_plan_invalid(
            "selected_index_out_of_range",
        ));
    }
    if selected_local.iter().any(|index| {
        !input.local_dependencies.contains_key(index)
            || !input.producer_profiles.contains_key(index)
    }) {
        return Err(targeted_authoring_plan_invalid("selected_row_missing"));
    }

    let combined_local_order = input.combined_topological_order.clone();
    if combined_local_order.len() != selected_local_count
        || combined_local_order
            .iter()
            .any(|index| !selected_local.contains(index))
    {
        return Err(targeted_authoring_plan_invalid(
            "selected_index_missing_from_order",
        ));
    }
    let first_target_position = combined_local_order
        .iter()
        .position(|index| input.selected_targets.contains(index));
    let mut pre_target_support = Vec::new();
    let mut explicit_targets = Vec::new();
    let mut post_target_support = Vec::new();
    for (position, &module_index) in combined_local_order.iter().enumerate() {
        if input.selected_targets.contains(&module_index) {
            explicit_targets.push(module_index);
        } else if first_target_position.is_some_and(|first| position < first) {
            pre_target_support.push(module_index);
        } else {
            post_target_support.push(module_index);
        }
    }
    if explicit_targets.len() != input.selected_targets.len()
        || pre_target_support.len() + post_target_support.len() != input.selected_support.len()
    {
        return Err(targeted_authoring_plan_invalid("partition_count_mismatch"));
    }

    let mut dependency_edges = 0usize;
    for &consumer in &combined_local_order {
        let consumer_position = topological_positions[&consumer];
        let dependencies = input
            .local_dependencies
            .get(&consumer)
            .ok_or_else(|| targeted_authoring_plan_invalid("dependency_row_missing"))?;
        for &dependency in dependencies {
            dependency_edges = dependency_edges
                .checked_add(1)
                .ok_or_else(|| targeted_authoring_plan_invalid("dependency_edge_overflow"))?;
            if dependency_edges > TARGETED_AUTHORING_CACHE_LIMITS_V1.closure_dependency_edges {
                return Err(targeted_authoring_plan_invalid(
                    "dependency_edges_out_of_bounds",
                ));
            }
            if dependency >= module_count
                || !selected_local.contains(&dependency)
                || topological_positions
                    .get(&dependency)
                    .is_none_or(|position| *position >= consumer_position)
            {
                return Err(targeted_authoring_plan_invalid(
                    "local_dependency_inconsistent",
                ));
            }
        }
    }

    let mut lifetime_dependencies = BTreeMap::new();
    let mut remaining_local_uses = BTreeMap::<usize, u64>::new();
    let mut lifetime_edges = 0usize;
    for &consumer in &combined_local_order {
        let mut closure = BTreeSet::new();
        let mut pending = input
            .local_dependencies
            .get(&consumer)
            .cloned()
            .ok_or_else(|| targeted_authoring_plan_invalid("dependency_row_missing"))?;
        while let Some(dependency) = pending.pop() {
            if !closure.insert(dependency) {
                continue;
            }
            pending.extend(
                input
                    .local_dependencies
                    .get(&dependency)
                    .ok_or_else(|| targeted_authoring_plan_invalid("dependency_row_missing"))?
                    .iter()
                    .copied(),
            );
        }
        let ordered_closure = combined_local_order
            .iter()
            .copied()
            .filter(|dependency| closure.contains(dependency))
            .collect::<Vec<_>>();
        lifetime_edges = lifetime_edges
            .checked_add(ordered_closure.len())
            .ok_or_else(|| targeted_authoring_plan_invalid("lifetime_edge_overflow"))?;
        if lifetime_edges > TARGETED_AUTHORING_CACHE_LIMITS_V1.closure_dependency_edges {
            return Err(targeted_authoring_plan_invalid(
                "lifetime_edges_out_of_bounds",
            ));
        }
        for &dependency in &ordered_closure {
            let uses = remaining_local_uses.entry(dependency).or_default();
            *uses = uses
                .checked_add(1)
                .ok_or_else(|| targeted_authoring_plan_invalid("remaining_use_overflow"))?;
        }
        lifetime_dependencies.insert(consumer, ordered_closure);
    }

    validate_external_order(
        &input.external_order,
        input.external_module_count,
        TARGETED_AUTHORING_CACHE_LIMITS_V1.closure_modules,
    )?;
    let selected_identity_count = selected_local_count
        .checked_add(input.external_order.len())
        .ok_or_else(|| targeted_authoring_plan_invalid("selected_identity_overflow"))?;
    if selected_identity_count > TARGETED_AUTHORING_CACHE_LIMITS_V1.closure_modules {
        return Err(targeted_authoring_plan_invalid(
            "selected_identity_out_of_bounds",
        ));
    }

    let mut initial_roles = BTreeMap::new();
    for &module_index in &pre_target_support {
        initial_roles.insert(
            module_index,
            TargetedAuthoringInitialRole::EligiblePreTargetSupport,
        );
    }
    for &module_index in &post_target_support {
        initial_roles.insert(
            module_index,
            TargetedAuthoringInitialRole::EligiblePreTargetSupport,
        );
    }
    for &module_index in &explicit_targets {
        initial_roles.insert(module_index, TargetedAuthoringInitialRole::FreshTarget);
    }

    let mut forced_closure_complete = BTreeSet::new();
    for &module_index in &post_target_support {
        force_local_prerequisite_closure(
            module_index,
            TargetedAuthoringForcedLiveReason::PostTargetSupportRequiresLiveOrder,
            false,
            &input.local_dependencies,
            &input.selected_targets,
            &input.selected_support,
            &mut initial_roles,
            &mut forced_closure_complete,
        )?;
    }

    for &module_index in &explicit_targets {
        if input.producer_profiles[&module_index]
            == TargetedAuthoringProducerProfile::StdCoreBuilder
        {
            force_local_node(
                module_index,
                TargetedAuthoringForcedLiveReason::ProducerProfile,
                true,
                &input.selected_targets,
                &input.selected_support,
                &mut initial_roles,
            )?;
            for &dependency in &input.local_dependencies[&module_index] {
                force_local_prerequisite_closure(
                    dependency,
                    TargetedAuthoringForcedLiveReason::CoreBuilderConsumerRequiresLive,
                    false,
                    &input.local_dependencies,
                    &input.selected_targets,
                    &input.selected_support,
                    &mut initial_roles,
                    &mut forced_closure_complete,
                )?;
            }
        }
    }

    for &module_index in &combined_local_order {
        if input.producer_profiles[&module_index] == TargetedAuthoringProducerProfile::Unsupported {
            force_local_prerequisite_closure(
                module_index,
                TargetedAuthoringForcedLiveReason::ProducerProfile,
                false,
                &input.local_dependencies,
                &input.selected_targets,
                &input.selected_support,
                &mut initial_roles,
                &mut forced_closure_complete,
            )?;
        }
    }

    let force_live_local = initial_roles
        .iter()
        .filter_map(|(index, role)| role.forced_live_reason().map(|_| *index))
        .collect::<BTreeSet<_>>();
    let forced_live_support = force_live_local
        .intersection(&input.selected_support)
        .copied()
        .collect::<BTreeSet<_>>();
    let forced_live_targets = force_live_local
        .intersection(&input.selected_targets)
        .copied()
        .collect::<BTreeSet<_>>();
    let eligible_support_lookup = pre_target_support
        .iter()
        .copied()
        .filter(|index| !forced_live_support.contains(index))
        .collect::<Vec<_>>();

    Ok(TargetedAuthoringExecutionPlan {
        combined_local_order,
        local_dependencies: input.local_dependencies,
        lifetime_dependencies,
        pre_target_support,
        explicit_targets,
        post_target_support,
        external_order: input.external_order,
        initial_roles,
        force_live_local,
        forced_live_support,
        forced_live_targets,
        eligible_support_lookup,
        remaining_local_uses,
    })
}

fn validate_external_order(
    external_order: &[usize],
    external_module_count: usize,
    limit: usize,
) -> Result<(), CommandDiagnostic> {
    if external_order.len() > limit {
        return Err(targeted_authoring_plan_invalid(
            "external_order_out_of_bounds",
        ));
    }
    let mut seen = BTreeSet::new();
    for &index in external_order {
        if index >= external_module_count {
            return Err(targeted_authoring_plan_invalid(
                "external_index_out_of_range",
            ));
        }
        if !seen.insert(index) {
            return Err(targeted_authoring_plan_invalid("external_index_duplicate"));
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn force_local_prerequisite_closure(
    seed: usize,
    reason: TargetedAuthoringForcedLiveReason,
    overwrite_seed: bool,
    local_dependencies: &BTreeMap<usize, Vec<usize>>,
    selected_targets: &BTreeSet<usize>,
    selected_support: &BTreeSet<usize>,
    initial_roles: &mut BTreeMap<usize, TargetedAuthoringInitialRole>,
    closure_complete: &mut BTreeSet<usize>,
) -> Result<(), CommandDiagnostic> {
    let mut pending = vec![(seed, overwrite_seed)];
    while let Some((module_index, overwrite)) = pending.pop() {
        if !closure_complete.insert(module_index) {
            continue;
        }
        if !selected_targets.contains(&module_index) && !selected_support.contains(&module_index) {
            return Err(targeted_authoring_plan_invalid(
                "forced_dependency_not_selected",
            ));
        }
        force_local_node(
            module_index,
            reason,
            overwrite,
            selected_targets,
            selected_support,
            initial_roles,
        )?;
        let dependencies = local_dependencies
            .get(&module_index)
            .ok_or_else(|| targeted_authoring_plan_invalid("forced_index_out_of_range"))?;
        pending.extend(
            dependencies
                .iter()
                .copied()
                .map(|dependency| (dependency, false)),
        );
    }
    Ok(())
}

fn force_local_node(
    module_index: usize,
    reason: TargetedAuthoringForcedLiveReason,
    overwrite: bool,
    selected_targets: &BTreeSet<usize>,
    selected_support: &BTreeSet<usize>,
    initial_roles: &mut BTreeMap<usize, TargetedAuthoringInitialRole>,
) -> Result<(), CommandDiagnostic> {
    let Some(role) = initial_roles.get_mut(&module_index) else {
        return Err(targeted_authoring_plan_invalid("forced_role_missing"));
    };
    if role.forced_live_reason().is_some() && !overwrite {
        return Ok(());
    }
    *role = if selected_targets.contains(&module_index) {
        TargetedAuthoringInitialRole::ForcedLiveTarget(reason)
    } else if selected_support.contains(&module_index) {
        TargetedAuthoringInitialRole::ForcedLiveSupport(reason)
    } else {
        return Err(targeted_authoring_plan_invalid("forced_role_unclassified"));
    };
    Ok(())
}

fn targeted_authoring_plan_invalid(reason: &'static str) -> CommandDiagnostic {
    CommandDiagnostic::error(DiagnosticKind::Internal, "targeted_authoring_plan_invalid")
        .with_field("plan")
        .with_actual_value(reason)
}

fn targeted_authoring_key_plan_invalid(error: TargetedAuthoringCacheError) -> CommandDiagnostic {
    CommandDiagnostic::error(DiagnosticKind::Internal, "targeted_authoring_plan_invalid")
        .with_field("support_key_plan")
        .with_actual_value(error.to_string())
}

fn reconstruct_pending_cached_support(
    entry: &TargetedAuthoringSupportContextEntry,
    snapshot: &TargetedAuthoringCurrentSnapshot,
    module_index: usize,
    verified_modules_by_module: &BTreeMap<Name, Arc<VerifiedModule>>,
    pending_contexts: &BTreeMap<usize, PendingCachedTargetedSupportContext>,
    pending_context_indices_by_module: &BTreeMap<Name, usize>,
    policy: &AxiomPolicy,
) -> Result<(PendingLocalAuthoringContext, HumanImportedSourceInterface), &'static str> {
    let current_certificate = npa_cert::decode_module_cert(&snapshot.certificate_bytes)
        .map_err(|_| "certificate_decode")?;
    let certificate_imports = entry
        .key_input
        .certificate_imports
        .iter()
        .map(|import| ImportEntry {
            module: import.module.clone(),
            export_hash: import.export_hash.into_bytes(),
            certificate_hash: import.certificate_hash.map(PackageHash::into_bytes),
        })
        .collect::<Vec<_>>();
    let expected = LocalAuthoringReconstructionIdentity::new(
        entry.key_input.current_certificate_file_hash.into_bytes(),
        current_certificate.header().format.clone(),
        current_certificate.header().core_spec.clone(),
        entry.key_input.module.clone(),
        certificate_imports,
        entry.key_input.actual_export_hash.into_bytes(),
        entry.key_input.actual_axiom_report_hash.into_bytes(),
        entry.key_input.actual_certificate_hash.into_bytes(),
        entry.key_input.axiom_policy_hash.into_bytes(),
    );
    let interface_identity = LocalAuthoringInterfaceIdentity::new(
        entry.source_interface.module.clone(),
        entry.source_interface.export_hash.into_bytes(),
        entry.source_interface.certificate_hash.into_bytes(),
    );
    let verifier = LocalAuthoringVerifierSession::new();
    let mut verified_imports = Vec::new();
    let mut pending_imports = Vec::new();
    for import in &entry.key_input.certificate_imports {
        if let Some(module) = verified_modules_by_module.get(&import.module) {
            verified_imports.push(module.as_ref());
            continue;
        }
        let pending_index = pending_context_indices_by_module
            .get(&import.module)
            .ok_or("certificate_import_missing")?;
        let pending = pending_contexts
            .get(pending_index)
            .ok_or("certificate_import_index_missing")?;
        pending_imports.push(&pending.pending);
    }
    let preview = verifier
        .reconstruct_pending_context_with_unadopted_imports(
            &snapshot.certificate_bytes,
            &expected,
            &interface_identity,
            &verified_imports,
            &pending_imports,
            policy,
        )
        .map_err(|_| "certificate_reconstruction")?;
    let preview = verifier.adopt_pending_context(preview);
    let authoring_import = HumanAuthoringImport::from_local_authoring_context(&preview)
        .map_err(|_| "authoring_import")?;
    let adapter_context = HumanInterfaceCacheAdapterContext::new(
        &entry.key_input.package,
        &entry.key_input.version,
        &entry.key_input.producer_profile,
        &entry.key_input.manifest_human_imports,
        module_index,
        &snapshot.source,
        &authoring_import,
    );
    let source_interface =
        cache_entry_to_human_interface(entry, &adapter_context).map_err(|_| "source_interface")?;
    let pending = verifier
        .reconstruct_pending_context_with_unadopted_imports(
            &snapshot.certificate_bytes,
            &expected,
            &interface_identity,
            &verified_imports,
            &pending_imports,
            policy,
        )
        .map_err(|_| "pending_reconstruction")?;
    Ok((pending, source_interface))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TargetedAuthoringStoreAvailability {
    NotRequested,
    Available,
    Unavailable,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct TargetedAuthoringDurationTotals {
    tool_identity_ns: u64,
    current_byte_validation_ns: u64,
    reconstruction_ns: u64,
    live_support_ns: u64,
    source_interface_resolution_ns: u64,
    fresh_target_ns: u64,
    support_lookup_ns: u64,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TargetedAuthoringDurationKind {
    CurrentByteValidation,
    Reconstruction,
    LiveSupport,
    SourceInterfaceResolution,
    FreshTarget,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct TargetedAuthoringCheckPlan {
    selected_targets: u64,
    selected_support: u64,
    selected_external: u64,
    forced_live_support: u64,
    forced_live_targets: u64,
    count_overflowed: bool,
}

impl TargetedAuthoringCheckPlan {
    pub(crate) fn new(
        selected_targets: usize,
        selected_support: usize,
        selected_external: usize,
    ) -> Self {
        let (selected_targets, target_overflowed) = bounded_count(selected_targets);
        let (selected_support, support_overflowed) = bounded_count(selected_support);
        let (selected_external, external_overflowed) = bounded_count(selected_external);
        Self {
            selected_targets,
            selected_support,
            selected_external,
            forced_live_support: 0,
            forced_live_targets: 0,
            count_overflowed: target_overflowed || support_overflowed || external_overflowed,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct TargetedAuthoringCheckRunState {
    visited_support: u64,
    visited_targets: u64,
    visited_external: u64,
    completed_support: u64,
    completed_targets: u64,
    completed_external: u64,
    context_hits: u64,
    context_bypassed_hits: u64,
    context_misses: u64,
    context_stale: u64,
    context_schema_misses: u64,
    context_invalid: u64,
    context_ineligible: u64,
    live_support_checks: u64,
    avoided_kernel_checks: u64,
    avoided_source_interface_resolutions: u64,
    target_attempts: u64,
    target_fresh_builds: u64,
    targets_forced_live: u64,
    entries_written: u64,
    bytes_loaded: u64,
    bytes_written: u64,
    tool_identity_attempted: bool,
    tool_identity_bytes: u64,
    durations: TargetedAuthoringDurationTotals,
    store_availability: TargetedAuthoringStoreAvailability,
    count_overflowed: bool,
}

impl Default for TargetedAuthoringCheckRunState {
    fn default() -> Self {
        Self {
            visited_support: 0,
            visited_targets: 0,
            visited_external: 0,
            completed_support: 0,
            completed_targets: 0,
            completed_external: 0,
            context_hits: 0,
            context_bypassed_hits: 0,
            context_misses: 0,
            context_stale: 0,
            context_schema_misses: 0,
            context_invalid: 0,
            context_ineligible: 0,
            live_support_checks: 0,
            avoided_kernel_checks: 0,
            avoided_source_interface_resolutions: 0,
            target_attempts: 0,
            target_fresh_builds: 0,
            targets_forced_live: 0,
            entries_written: 0,
            bytes_loaded: 0,
            bytes_written: 0,
            tool_identity_attempted: false,
            tool_identity_bytes: 0,
            durations: TargetedAuthoringDurationTotals::default(),
            store_availability: TargetedAuthoringStoreAvailability::NotRequested,
            count_overflowed: false,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct TargetedAuthoringCheckSummary {
    plan: TargetedAuthoringCheckPlan,
    run: TargetedAuthoringCheckRunState,
    completed: bool,
}

impl TargetedAuthoringCheckSummary {
    fn validate(self, provenance: TargetedAuthoringProvenance) -> Result<(), &'static str> {
        let local_limit = TARGETED_AUTHORING_CACHE_LIMITS_V1.closure_modules as u64;
        let local_selected = self
            .plan
            .selected_targets
            .checked_add(self.plan.selected_support)
            .ok_or("selected_local_overflow")?;
        let selected_identities = local_selected
            .checked_add(self.plan.selected_external)
            .ok_or("selected_identity_overflow")?;
        if self.plan.count_overflowed
            || self.run.count_overflowed
            || selected_identities > local_limit
        {
            return Err("selected_count_out_of_bounds");
        }
        if self.run.visited_support > self.plan.selected_support
            || self.run.visited_targets > self.plan.selected_targets
            || self.run.target_attempts != self.run.visited_targets
            || self.run.target_fresh_builds != self.run.target_attempts
            || self.run.targets_forced_live > self.run.target_attempts
            || self.run.targets_forced_live > self.plan.forced_live_targets
            || self.run.visited_external > self.plan.selected_external
            || self.run.completed_support > self.run.visited_support
            || self.run.completed_targets > self.run.visited_targets
            || self.run.completed_external > self.run.visited_external
            || self.plan.forced_live_support > self.plan.selected_support
            || self.plan.forced_live_targets > self.plan.selected_targets
            || self.run.live_support_checks > self.run.visited_support
            || self.run.entries_written > self.run.live_support_checks
        {
            return Err("visited_count_inconsistent");
        }
        let support_outcomes = self
            .run
            .context_hits
            .checked_add(self.run.context_bypassed_hits)
            .and_then(|value| value.checked_add(self.run.context_misses))
            .and_then(|value| value.checked_add(self.run.context_ineligible))
            .ok_or("support_outcome_overflow")?;
        let classified_miss_subsets = self
            .run
            .context_stale
            .checked_add(self.run.context_schema_misses)
            .and_then(|value| value.checked_add(self.run.context_invalid))
            .ok_or("support_miss_subset_overflow")?;
        if support_outcomes > self.run.visited_support
            || classified_miss_subsets > self.run.context_misses
            || self.run.avoided_kernel_checks != self.run.context_hits
            || self.run.avoided_source_interface_resolutions != self.run.context_hits
            || provenance.locally_accelerated != (self.run.context_hits > 0)
        {
            return Err("support_outcome_inconsistent");
        }
        if self.completed
            && (self.run.visited_support != self.plan.selected_support
                || self.run.visited_targets != self.plan.selected_targets
                || self.run.visited_external != self.plan.selected_external
                || self.run.completed_support != self.plan.selected_support
                || self.run.completed_targets != self.plan.selected_targets
                || self.run.completed_external != self.plan.selected_external
                || self.run.targets_forced_live != self.plan.forced_live_targets
                || support_outcomes != self.plan.selected_support
                || self.run.live_support_checks
                    != self
                        .run
                        .context_bypassed_hits
                        .checked_add(self.run.context_misses)
                        .and_then(|value| value.checked_add(self.run.context_ineligible))
                        .ok_or("live_support_equation_overflow")?
                || self.plan.selected_support
                    != self
                        .run
                        .context_hits
                        .checked_add(self.run.live_support_checks)
                        .ok_or("selected_support_equation_overflow")?)
        {
            return Err("completed_visit_count_inconsistent");
        }
        if self.run.bytes_loaded > TARGETED_AUTHORING_CACHE_LIMITS_V1.command_loaded_bytes as u64
            || self.run.bytes_written
                > TARGETED_AUTHORING_CACHE_LIMITS_V1.command_written_bytes as u64
        {
            return Err("byte_count_out_of_bounds");
        }
        Ok(())
    }

    fn diagnostic(self, provenance: TargetedAuthoringProvenance) -> CommandDiagnostic {
        CommandDiagnostic::info(
            DiagnosticKind::GeneratedArtifact,
            "targeted_authoring_cache_summary",
        )
        .with_field("targeted_authoring_cache")
        .with_actual_value(format!(
            "mode=local-hit;complete={};support_selected={};targets_selected={};external_selected={};forced_live_support={};targets_forced_live={};visited_support={};visited_targets={};visited_external={};context_hits={};context_bypassed_hits={};context_misses={};context_stale={};context_schema_misses={};context_invalid={};context_ineligible={};live_prerequisite_checks={};avoided_kernel_checks={};avoided_source_interface_resolutions={};target_fresh_builds={};entries_written={};bytes_loaded={};bytes_written={};trusted={};build_evidence={};proof_evidence={}",
            self.completed,
            self.plan.selected_support,
            self.plan.selected_targets,
            self.plan.selected_external,
            self.plan.forced_live_support,
            self.run.targets_forced_live,
            self.run.visited_support,
            self.run.visited_targets,
            self.run.visited_external,
            self.run.context_hits,
            self.run.context_bypassed_hits,
            self.run.context_misses,
            self.run.context_stale,
            self.run.context_schema_misses,
            self.run.context_invalid,
            self.run.context_ineligible,
            self.run.live_support_checks,
            self.run.avoided_kernel_checks,
            self.run.avoided_source_interface_resolutions,
            self.run.target_fresh_builds,
            self.run.entries_written,
            self.run.bytes_loaded,
            self.run.bytes_written,
            provenance.trusted,
            provenance.build_evidence,
            provenance.proof_evidence,
        ))
    }

    fn measurement_snapshot(self) -> TargetedAuthoringMeasurementSnapshot {
        TargetedAuthoringMeasurementSnapshot {
            support_selected: self.plan.selected_support,
            targets_forced_live: self.run.targets_forced_live,
            context_hits: self.run.context_hits,
            context_bypassed_hits: self.run.context_bypassed_hits,
            context_misses: self.run.context_misses,
            context_stale: self.run.context_stale,
            context_schema_misses: self.run.context_schema_misses,
            context_ineligible: self.run.context_ineligible,
            live_prerequisite_checks: self.run.live_support_checks,
            avoided_kernel_checks: self.run.avoided_kernel_checks,
            avoided_source_interface_resolutions: self.run.avoided_source_interface_resolutions,
            target_fresh_builds: self.run.target_fresh_builds,
            tool_identity_attempted: self.run.tool_identity_attempted,
            tool_identity_bytes: self.run.tool_identity_bytes,
            tool_identity_elapsed_ns: self.run.durations.tool_identity_ns,
            current_byte_validation_elapsed_ns: self.run.durations.current_byte_validation_ns,
            reconstruction_elapsed_ns: self.run.durations.reconstruction_ns,
            live_support_elapsed_ns: self.run.durations.live_support_ns,
            source_interface_resolution_elapsed_ns: self
                .run
                .durations
                .source_interface_resolution_ns,
            fresh_target_elapsed_ns: self.run.durations.fresh_target_ns,
            bytes_loaded: self.run.bytes_loaded,
            bytes_written: self.run.bytes_written,
            cache_lookup_ms: self.run.durations.support_lookup_ns / 1_000_000,
            local_hit_outcomes: true,
        }
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct TargetedAuthoringMeasurementSnapshot {
    support_selected: u64,
    targets_forced_live: u64,
    context_hits: u64,
    context_bypassed_hits: u64,
    context_misses: u64,
    context_stale: u64,
    context_schema_misses: u64,
    context_ineligible: u64,
    live_prerequisite_checks: u64,
    avoided_kernel_checks: u64,
    avoided_source_interface_resolutions: u64,
    target_fresh_builds: u64,
    tool_identity_attempted: bool,
    tool_identity_bytes: u64,
    tool_identity_elapsed_ns: u64,
    current_byte_validation_elapsed_ns: u64,
    reconstruction_elapsed_ns: u64,
    live_support_elapsed_ns: u64,
    source_interface_resolution_elapsed_ns: u64,
    fresh_target_elapsed_ns: u64,
    bytes_loaded: u64,
    bytes_written: u64,
    cache_lookup_ms: u64,
    local_hit_outcomes: bool,
}

impl TargetedAuthoringMeasurementSnapshot {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn read_through(
        support_selected: usize,
        live_prerequisite_checks: usize,
        target_fresh_builds: usize,
        live_support_elapsed_ns: u64,
        source_interface_resolution_elapsed_ns: u64,
        fresh_target_elapsed_ns: u64,
        bytes_loaded: usize,
        bytes_written: usize,
    ) -> Self {
        Self {
            support_selected: u64::try_from(support_selected).unwrap_or(u64::MAX),
            live_prerequisite_checks: u64::try_from(live_prerequisite_checks).unwrap_or(u64::MAX),
            target_fresh_builds: u64::try_from(target_fresh_builds).unwrap_or(u64::MAX),
            live_support_elapsed_ns,
            source_interface_resolution_elapsed_ns,
            fresh_target_elapsed_ns,
            bytes_loaded: u64::try_from(bytes_loaded).unwrap_or(u64::MAX),
            bytes_written: u64::try_from(bytes_written).unwrap_or(u64::MAX),
            ..Self::default()
        }
    }

    pub(crate) fn record(self, recorder: &mut PerformanceMeasurementRecorder) {
        for (label, value) in [
            (
                PerformanceMeasurementLabel::CacheSupportSelected,
                self.support_selected,
            ),
            (
                PerformanceMeasurementLabel::CacheLivePrerequisiteChecks,
                self.live_prerequisite_checks,
            ),
            (
                PerformanceMeasurementLabel::CacheAvoidedKernelChecks,
                self.avoided_kernel_checks,
            ),
            (
                PerformanceMeasurementLabel::CacheAvoidedSourceInterfaceResolutions,
                self.avoided_source_interface_resolutions,
            ),
            (
                PerformanceMeasurementLabel::CacheTargetFreshBuilds,
                self.target_fresh_builds,
            ),
            (
                PerformanceMeasurementLabel::CacheLiveSupportElapsed,
                self.live_support_elapsed_ns,
            ),
            (
                PerformanceMeasurementLabel::CacheSourceInterfaceResolutionElapsed,
                self.source_interface_resolution_elapsed_ns,
            ),
            (
                PerformanceMeasurementLabel::CacheFreshTargetElapsed,
                self.fresh_target_elapsed_ns,
            ),
            (
                PerformanceMeasurementLabel::CacheBytesLoaded,
                self.bytes_loaded,
            ),
            (
                PerformanceMeasurementLabel::CacheBytesWritten,
                self.bytes_written,
            ),
        ] {
            recorder.add_counter(label, value);
        }
        if self.local_hit_outcomes {
            for (label, value) in [
                (
                    PerformanceMeasurementLabel::CacheTargetsForcedLive,
                    self.targets_forced_live,
                ),
                (
                    PerformanceMeasurementLabel::CacheContextHits,
                    self.context_hits,
                ),
                (
                    PerformanceMeasurementLabel::CacheContextBypassedHits,
                    self.context_bypassed_hits,
                ),
                (
                    PerformanceMeasurementLabel::CacheContextMisses,
                    self.context_misses,
                ),
                (
                    PerformanceMeasurementLabel::CacheContextStale,
                    self.context_stale,
                ),
                (
                    PerformanceMeasurementLabel::CacheContextSchemaMisses,
                    self.context_schema_misses,
                ),
                (
                    PerformanceMeasurementLabel::CacheContextIneligible,
                    self.context_ineligible,
                ),
                (
                    PerformanceMeasurementLabel::CacheCurrentByteValidationElapsed,
                    self.current_byte_validation_elapsed_ns,
                ),
                (
                    PerformanceMeasurementLabel::CacheReconstructionElapsed,
                    self.reconstruction_elapsed_ns,
                ),
            ] {
                recorder.add_counter(label, value);
            }
        }
        if self.tool_identity_attempted {
            recorder.add_counter(
                PerformanceMeasurementLabel::CacheToolIdentityBytes,
                self.tool_identity_bytes,
            );
            recorder.add_counter(
                PerformanceMeasurementLabel::CacheToolIdentityElapsed,
                self.tool_identity_elapsed_ns,
            );
        }
    }

    pub(crate) const fn cache_lookup_ms(self) -> u64 {
        self.cache_lookup_ms
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct TargetedAuthoringProvenance {
    trusted: bool,
    build_evidence: bool,
    proof_evidence: bool,
    locally_accelerated: bool,
}

impl TargetedAuthoringProvenance {
    const LOCAL_ONLY: Self = Self {
        trusted: false,
        build_evidence: false,
        proof_evidence: false,
        locally_accelerated: false,
    };

    fn actual_value(self) -> String {
        format!(
            "trusted={};build_evidence={};proof_evidence={};locally_accelerated={}",
            self.trusted, self.build_evidence, self.proof_evidence, self.locally_accelerated
        )
    }
}

#[derive(Debug)]
pub(crate) struct TargetedAuthoringCheckRun {
    plan: TargetedAuthoringCheckPlan,
    state: TargetedAuthoringCheckRunState,
    provenance: TargetedAuthoringProvenance,
    pre_target_support: BTreeSet<usize>,
    combined_local_order: Vec<usize>,
    eligible_support_lookup: BTreeSet<usize>,
    local_dependencies: BTreeMap<usize, Vec<usize>>,
    force_live_local: BTreeSet<usize>,
    forced_live_support: BTreeSet<usize>,
    forced_live_support_reasons: BTreeMap<usize, TargetedAuthoringForcedLiveReason>,
    explicit_targets: BTreeSet<usize>,
    forced_live_targets: BTreeSet<usize>,
    attempted_targets: BTreeSet<usize>,
    target_attempt_order: Vec<usize>,
    support_cache_session: Option<TargetedAuthoringSupportCacheSession>,
    support_key_context: Option<TargetedAuthoringSupportKeyContext>,
    support_key_accumulator: Option<TargetedAuthoringSupportKeyAccumulator>,
    publication_keys: BTreeMap<usize, TargetedAuthoringIncrementalSupportKey>,
    support_store_budget: TargetedAuthoringSupportContextStoreBudget,
    lookup_misses: BTreeMap<usize, TargetedAuthoringLookupMiss>,
    pending_contexts: BTreeMap<usize, PendingCachedTargetedSupportContext>,
    pending_context_indices_by_module: BTreeMap<Name, usize>,
    retained_snapshots: BTreeMap<usize, TargetedAuthoringCurrentSnapshot>,
    retained_context_bytes: usize,
    live_support: BTreeSet<usize>,
    publication_suppressed: BTreeSet<usize>,
    producer_lifetimes: TargetedAuthoringProducerLifetimeLedger,
    cache_diagnostics: Vec<CommandDiagnostic>,
    unavailable_diagnostic_recorded: bool,
    measurement_enabled: bool,
    detailed_cache_diagnostics: bool,
}

impl TargetedAuthoringCheckRun {
    fn new(plan: TargetedAuthoringCheckPlan) -> Self {
        Self::new_with_measurements(plan, false, false)
    }

    fn new_with_measurements(
        plan: TargetedAuthoringCheckPlan,
        measurement_enabled: bool,
        detailed_cache_diagnostics: bool,
    ) -> Self {
        Self {
            plan,
            state: TargetedAuthoringCheckRunState::default(),
            provenance: TargetedAuthoringProvenance::LOCAL_ONLY,
            pre_target_support: BTreeSet::new(),
            combined_local_order: Vec::new(),
            eligible_support_lookup: BTreeSet::new(),
            local_dependencies: BTreeMap::new(),
            force_live_local: BTreeSet::new(),
            forced_live_support: BTreeSet::new(),
            forced_live_support_reasons: BTreeMap::new(),
            explicit_targets: BTreeSet::new(),
            forced_live_targets: BTreeSet::new(),
            attempted_targets: BTreeSet::new(),
            target_attempt_order: Vec::new(),
            support_cache_session: None,
            support_key_context: None,
            support_key_accumulator: None,
            publication_keys: BTreeMap::new(),
            support_store_budget: TargetedAuthoringSupportContextStoreBudget::new(),
            lookup_misses: BTreeMap::new(),
            pending_contexts: BTreeMap::new(),
            pending_context_indices_by_module: BTreeMap::new(),
            retained_snapshots: BTreeMap::new(),
            retained_context_bytes: 0,
            live_support: BTreeSet::new(),
            publication_suppressed: BTreeSet::new(),
            producer_lifetimes: TargetedAuthoringProducerLifetimeLedger::default(),
            cache_diagnostics: Vec::new(),
            unavailable_diagnostic_recorded: false,
            measurement_enabled,
            detailed_cache_diagnostics,
        }
    }

    pub(crate) const fn measurement_enabled(&self) -> bool {
        self.measurement_enabled
    }

    pub(crate) fn time_current_byte_validation<T>(&mut self, run: impl FnOnce() -> T) -> T {
        self.time_duration(TargetedAuthoringDurationKind::CurrentByteValidation, run)
    }

    pub(crate) fn time_current_byte_validation_for<T>(
        &mut self,
        module_index: usize,
        operation: impl FnOnce() -> T,
    ) -> T {
        if self.eligible_support_lookup.contains(&module_index) {
            self.time_current_byte_validation(operation)
        } else {
            operation()
        }
    }

    pub(crate) fn record_source_interface_resolution_elapsed(&mut self, elapsed_ns: u64) {
        self.add_duration(
            TargetedAuthoringDurationKind::SourceInterfaceResolution,
            elapsed_ns,
        );
    }

    pub(crate) fn record_live_support_elapsed(&mut self, elapsed_ns: u64) {
        self.add_duration(TargetedAuthoringDurationKind::LiveSupport, elapsed_ns);
    }

    pub(crate) fn record_fresh_target_verification_elapsed(&mut self, elapsed_ns: u64) {
        self.add_duration(TargetedAuthoringDurationKind::FreshTarget, elapsed_ns);
    }

    fn time_duration<T>(
        &mut self,
        kind: TargetedAuthoringDurationKind,
        run: impl FnOnce() -> T,
    ) -> T {
        let started = self.measurement_enabled.then(Instant::now);
        let value = run();
        if let Some(started) = started {
            self.add_duration(kind, elapsed_ns(started));
        }
        value
    }

    fn add_duration(&mut self, kind: TargetedAuthoringDurationKind, elapsed_ns: u64) {
        let target = match kind {
            TargetedAuthoringDurationKind::CurrentByteValidation => {
                &mut self.state.durations.current_byte_validation_ns
            }
            TargetedAuthoringDurationKind::Reconstruction => {
                &mut self.state.durations.reconstruction_ns
            }
            TargetedAuthoringDurationKind::LiveSupport => &mut self.state.durations.live_support_ns,
            TargetedAuthoringDurationKind::SourceInterfaceResolution => {
                &mut self.state.durations.source_interface_resolution_ns
            }
            TargetedAuthoringDurationKind::FreshTarget => &mut self.state.durations.fresh_target_ns,
        };
        *target = target.saturating_add(elapsed_ns);
    }

    fn adopt_execution_plan(
        &mut self,
        execution_plan: &TargetedAuthoringExecutionPlan,
    ) -> Result<(), CommandDiagnostic> {
        let (selected_targets, target_overflowed) =
            bounded_count(execution_plan.explicit_targets.len());
        let selected_support_count = execution_plan
            .pre_target_support
            .len()
            .checked_add(execution_plan.post_target_support.len())
            .ok_or_else(|| targeted_authoring_plan_invalid("selected_support_overflow"))?;
        let (selected_support, support_overflowed) = bounded_count(selected_support_count);
        if target_overflowed
            || support_overflowed
            || selected_targets != self.plan.selected_targets
            || selected_support != self.plan.selected_support
        {
            return Err(targeted_authoring_plan_invalid(
                "selection_summary_mismatch",
            ));
        }
        let (selected_external, external_overflowed) =
            bounded_count(execution_plan.external_order.len());
        let (forced_live_support, forced_support_overflowed) =
            bounded_count(execution_plan.forced_live_support.len());
        let (forced_live_targets, forced_target_overflowed) =
            bounded_count(execution_plan.forced_live_targets.len());
        self.plan.selected_external = selected_external;
        self.plan.forced_live_support = forced_live_support;
        self.plan.forced_live_targets = forced_live_targets;
        self.plan.count_overflowed |=
            external_overflowed || forced_support_overflowed || forced_target_overflowed;
        self.pre_target_support = execution_plan.pre_target_support.iter().copied().collect();
        self.combined_local_order = execution_plan.combined_local_order.clone();
        self.eligible_support_lookup = execution_plan
            .eligible_support_lookup
            .iter()
            .copied()
            .collect();
        self.local_dependencies = execution_plan.local_dependencies.clone();
        self.force_live_local = execution_plan.force_live_local.clone();
        self.forced_live_support = execution_plan.forced_live_support.clone();
        self.forced_live_support_reasons = execution_plan
            .initial_roles
            .iter()
            .filter_map(|(module_index, role)| match role {
                TargetedAuthoringInitialRole::ForcedLiveSupport(reason) => {
                    Some((*module_index, *reason))
                }
                _ => None,
            })
            .collect();
        self.explicit_targets = execution_plan.explicit_targets.iter().copied().collect();
        self.forced_live_targets = execution_plan.forced_live_targets.clone();
        self.producer_lifetimes =
            TargetedAuthoringProducerLifetimeLedger::from_execution_plan(execution_plan);
        Ok(())
    }

    pub(crate) fn prepare_support_lookup(
        &mut self,
        loaded: &LoadedPackageRoot,
        override_base: Option<&Path>,
        external_inputs: Vec<TargetedAuthoringExternalModuleInput>,
        policy: &AxiomPolicy,
    ) -> Result<(), CommandDiagnostic> {
        if self.eligible_support_lookup.is_empty() {
            self.state.store_availability = TargetedAuthoringStoreAvailability::NotRequested;
            return Ok(());
        }
        let session = prepare_targeted_authoring_support_cache_session(
            loaded,
            override_base,
            self.measurement_enabled,
        );
        let tool_observation = session.tool_identity_observation();
        self.state.tool_identity_attempted = tool_observation.attempted;
        self.state.tool_identity_bytes = tool_observation.bytes;
        self.state.durations.tool_identity_ns = tool_observation.elapsed_ns;
        let Some(toolchain) = session.toolchain().cloned() else {
            self.state.store_availability = TargetedAuthoringStoreAvailability::Unavailable;
            self.support_cache_session = Some(session);
            self.record_unavailable_diagnostic();
            return Ok(());
        };
        let manifest = loaded.validated.manifest();
        let context = targeted_authoring_support_key_context(toolchain, policy);
        let accumulator = TargetedAuthoringSupportKeyAccumulator::new(external_inputs)
            .map_err(targeted_authoring_key_plan_invalid)?;
        if manifest.modules.len() != loaded.validated.graph().resolved_module_imports.len() {
            return Err(targeted_authoring_plan_invalid("module_table_shape"));
        }
        self.state.store_availability = TargetedAuthoringStoreAvailability::Available;
        self.support_cache_session = Some(session);
        self.support_key_context = Some(context);
        self.support_key_accumulator = Some(accumulator);
        Ok(())
    }

    pub(crate) fn should_capture_pre_target_snapshot(&mut self, module_index: usize) -> bool {
        if !self.pre_target_support.contains(&module_index) {
            return false;
        }
        true
    }

    pub(crate) fn lookup_pre_target_support(
        &mut self,
        loaded: &LoadedPackageRoot,
        module_index: usize,
        artifact: TargetedAuthoringLocalModuleInput,
        snapshot: TargetedAuthoringCurrentSnapshot,
        verified_modules_by_module: &BTreeMap<Name, Arc<VerifiedModule>>,
        policy: &AxiomPolicy,
    ) -> Result<(), CommandDiagnostic> {
        if !self.pre_target_support.contains(&module_index) {
            return Err(targeted_authoring_plan_invalid(
                "lookup_module_outside_pre_target_support",
            ));
        }
        let Some(snapshot_bytes) = snapshot.loaded_bytes() else {
            self.disable_support_lookup_for_resource_limit();
            self.retained_snapshots.insert(module_index, snapshot);
            if self.eligible_support_lookup.contains(&module_index) {
                self.record_lookup_miss(module_index, TargetedAuthoringLookupMiss::Unavailable);
            }
            return Ok(());
        };
        let construct_key = self.eligible_support_lookup.contains(&module_index);
        let Some(context) = self.support_key_context.as_ref() else {
            self.retained_snapshots.insert(module_index, snapshot);
            if construct_key {
                self.record_lookup_miss(module_index, TargetedAuthoringLookupMiss::Unavailable);
            }
            return Ok(());
        };
        let planned = self
            .support_key_accumulator
            .as_mut()
            .ok_or_else(|| targeted_authoring_plan_invalid("support_key_accumulator_missing"))?
            .push_local(
                &loaded.validated,
                context,
                module_index,
                artifact,
                construct_key,
            )
            .map_err(targeted_authoring_key_plan_invalid)?;
        if !construct_key {
            self.retained_snapshots.insert(module_index, snapshot);
            return Ok(());
        }
        let planned = planned.ok_or_else(|| {
            targeted_authoring_plan_invalid("eligible_support_key_not_constructed")
        })?;
        self.publication_keys.insert(module_index, planned.clone());
        let (lookup, lookup_elapsed_ns) = self
            .support_cache_session
            .as_mut()
            .ok_or_else(|| targeted_authoring_plan_invalid("support_cache_session_missing"))?
            .lookup_observed(
                &planned.cache_key,
                &mut self.support_store_budget,
                self.measurement_enabled,
            );
        self.state.durations.support_lookup_ns = self
            .state
            .durations
            .support_lookup_ns
            .saturating_add(lookup_elapsed_ns);
        match lookup {
            TargetedAuthoringSupportContextStoreLookup::Hit(entry) => {
                if entry.key_input != planned.key_input
                    || entry.closure_commitment != planned.closure_commitment
                {
                    self.retained_snapshots.insert(module_index, snapshot);
                    self.record_lookup_miss(module_index, TargetedAuthoringLookupMiss::Stale);
                    return Ok(());
                }
                let pending_context_count =
                    self.pending_contexts.len().checked_add(1).ok_or_else(|| {
                        targeted_authoring_plan_invalid("retained_context_count_overflow")
                    })?;
                let retained_context_bytes = self
                    .retained_context_bytes
                    .checked_add(snapshot_bytes)
                    .ok_or_else(|| {
                        targeted_authoring_plan_invalid("retained_context_bytes_overflow")
                    })?;
                if pending_context_count > TARGETED_AUTHORING_CACHE_LIMITS_V1.retained_contexts
                    || retained_context_bytes
                        > TARGETED_AUTHORING_CACHE_LIMITS_V1.retained_context_bytes
                {
                    self.retained_snapshots.insert(module_index, snapshot);
                    self.record_lookup_miss(module_index, TargetedAuthoringLookupMiss::Invalid);
                    return Ok(());
                }
                let reconstruction_started = self.measurement_enabled.then(Instant::now);
                let reconstructed = reconstruct_pending_cached_support(
                    &entry,
                    &snapshot,
                    module_index,
                    verified_modules_by_module,
                    &self.pending_contexts,
                    &self.pending_context_indices_by_module,
                    policy,
                );
                if let Some(started) = reconstruction_started {
                    self.add_duration(
                        TargetedAuthoringDurationKind::Reconstruction,
                        elapsed_ns(started),
                    );
                }
                match reconstructed {
                    Ok((pending, source_interface)) => {
                        self.retained_context_bytes = retained_context_bytes;
                        let pending_module = pending.module().clone();
                        if self
                            .pending_context_indices_by_module
                            .insert(pending_module, module_index)
                            .is_some()
                        {
                            return Err(targeted_authoring_plan_invalid(
                                "pending_context_module_duplicate",
                            ));
                        }
                        self.pending_contexts.insert(
                            module_index,
                            PendingCachedTargetedSupportContext {
                                pending,
                                source_interface,
                                snapshot,
                                retained_bytes: snapshot_bytes,
                            },
                        );
                    }
                    Err(reason) => {
                        self.retained_snapshots.insert(module_index, snapshot);
                        self.record_late_support_ineligibility(module_index, reason);
                        self.record_lookup_miss(module_index, TargetedAuthoringLookupMiss::Invalid);
                    }
                }
            }
            TargetedAuthoringSupportContextStoreLookup::Missing => {
                self.retained_snapshots.insert(module_index, snapshot);
                self.record_lookup_miss(module_index, TargetedAuthoringLookupMiss::Missing);
            }
            TargetedAuthoringSupportContextStoreLookup::Stale => {
                self.retained_snapshots.insert(module_index, snapshot);
                self.record_lookup_miss(module_index, TargetedAuthoringLookupMiss::Stale);
            }
            TargetedAuthoringSupportContextStoreLookup::SchemaMiss => {
                self.retained_snapshots.insert(module_index, snapshot);
                self.record_lookup_miss(module_index, TargetedAuthoringLookupMiss::SchemaMiss);
            }
            TargetedAuthoringSupportContextStoreLookup::Invalid => {
                self.retained_snapshots.insert(module_index, snapshot);
                self.record_lookup_miss(module_index, TargetedAuthoringLookupMiss::Invalid);
            }
            TargetedAuthoringSupportContextStoreLookup::Unavailable => {
                self.retained_snapshots.insert(module_index, snapshot);
                self.state.store_availability = TargetedAuthoringStoreAvailability::Unavailable;
                self.support_key_context = None;
                self.support_key_accumulator = None;
                self.record_unavailable_diagnostic();
                self.record_lookup_miss(module_index, TargetedAuthoringLookupMiss::Unavailable);
            }
        }
        Ok(())
    }

    /// Resolve the reached support node into either a retained pending hit or
    /// an ordinary live fallback closure in dependency-first order.
    pub(crate) fn resolve_reached_pre_target_support(
        &mut self,
        module_index: usize,
    ) -> Result<Vec<usize>, CommandDiagnostic> {
        if !self.pre_target_support.contains(&module_index) {
            return Err(targeted_authoring_plan_invalid(
                "support_resolution_outside_pre_target_prefix",
            ));
        }
        if self.pending_contexts.contains_key(&module_index) {
            return Ok(Vec::new());
        }
        if !self.force_live_local.contains(&module_index)
            && !self.lookup_misses.contains_key(&module_index)
        {
            return Err(targeted_authoring_plan_invalid(
                "support_resolution_without_outcome",
            ));
        }

        let mut promoted = BTreeSet::new();
        let mut pending = vec![module_index];
        while let Some(index) = pending.pop() {
            if !promoted.insert(index) {
                continue;
            }
            let dependencies = self.local_dependencies.get(&index).ok_or_else(|| {
                targeted_authoring_plan_invalid("support_promotion_dependency_row_missing")
            })?;
            pending.extend(dependencies.iter().copied());
        }
        self.force_live_local.extend(promoted.iter().copied());

        for &index in &promoted {
            let Some(pending) = self.pending_contexts.remove(&index) else {
                continue;
            };
            self.pending_context_indices_by_module
                .remove(pending.pending.module());
            self.retained_context_bytes = self
                .retained_context_bytes
                .checked_sub(pending.retained_bytes)
                .ok_or_else(|| {
                    targeted_authoring_plan_invalid("retained_context_bytes_underflow")
                })?;
            self.retained_snapshots.insert(index, pending.snapshot);
            checked_increment(
                &mut self.state.context_bypassed_hits,
                &mut self.state.count_overflowed,
            );
            if self.detailed_cache_diagnostics
                && self.cache_diagnostics.len()
                    < TARGETED_AUTHORING_CACHE_LIMITS_V1.detailed_diagnostics
            {
                self.cache_diagnostics.push(
                    CommandDiagnostic::info(
                        DiagnosticKind::GeneratedArtifact,
                        "targeted_authoring_cache_hit_bypassed",
                    )
                    .with_field("targeted_authoring_cache")
                    .with_actual_value(format!("module_index={index}")),
                );
            }
        }

        Ok(self
            .combined_local_order
            .iter()
            .copied()
            .filter(|index| promoted.contains(index) && !self.live_support.contains(index))
            .collect())
    }

    pub(crate) fn take_retained_snapshot(
        &mut self,
        module_index: usize,
    ) -> Result<TargetedAuthoringCurrentSnapshot, CommandDiagnostic> {
        self.retained_snapshots
            .remove(&module_index)
            .ok_or_else(|| targeted_authoring_plan_invalid("promoted_support_snapshot_missing"))
    }

    pub(crate) fn record_live_support_completion(
        &mut self,
        module_index: usize,
    ) -> Result<(), CommandDiagnostic> {
        if !self.live_support.insert(module_index) {
            return Err(targeted_authoring_plan_invalid(
                "live_support_completed_twice",
            ));
        }
        checked_increment(
            &mut self.state.live_support_checks,
            &mut self.state.count_overflowed,
        );
        self.producer_lifetimes.register(
            module_index,
            TargetedAuthoringProducerViews::LIVE_SUPPORT_OR_FORCED_TARGET,
        )?;
        self.record_support_completion();
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn publish_accepted_live_support(
        &mut self,
        loaded: &LoadedPackageRoot,
        module_index: usize,
        source: &str,
        interface: &HumanImportedSourceInterface,
        verified: &VerifiedModule,
        closure_used_cached_context: bool,
    ) {
        if self.publication_suppressed.contains(&module_index) {
            return;
        }
        let (Some(planned), Some(session)) = (
            self.publication_keys.get(&module_index),
            self.support_cache_session.as_mut(),
        ) else {
            return;
        };
        let Some(namespace) = session.namespace().cloned() else {
            return;
        };
        let entry = match build_accepted_targeted_authoring_support_entry(
            loaded,
            module_index,
            &namespace,
            planned,
            source,
            interface,
            verified,
            TargetedAuthoringPublicationOrigin::TargetedLocalHitSupport,
            closure_used_cached_context,
            TargetedAuthoringModuleAcceptance::checked_certificate_complete(),
        ) {
            Ok(entry) => entry,
            Err(reason) => {
                self.record_late_support_ineligibility(module_index, reason);
                return;
            }
        };
        let outcome = session.publish(&entry, &mut self.support_store_budget);
        self.record_publication_outcome(module_index, outcome);
    }

    fn record_publication_outcome(
        &mut self,
        module_index: usize,
        outcome: TargetedAuthoringSupportContextPublishOutcome,
    ) {
        match outcome {
            TargetedAuthoringSupportContextPublishOutcome::Published => checked_increment(
                &mut self.state.entries_written,
                &mut self.state.count_overflowed,
            ),
            TargetedAuthoringSupportContextPublishOutcome::ExistingEqual => {}
            TargetedAuthoringSupportContextPublishOutcome::Conflict(validation) => {
                self.record_publication_collision(module_index, validation);
            }
            TargetedAuthoringSupportContextPublishOutcome::Invalid => {
                self.record_publication_diagnostic(module_index, "publication_invalid")
            }
            TargetedAuthoringSupportContextPublishOutcome::Unavailable => {
                self.record_publication_diagnostic(module_index, "publication_unavailable")
            }
        }
    }

    fn record_publication_diagnostic(&mut self, module_index: usize, reason: &'static str) {
        if !self.detailed_cache_diagnostics
            || self.cache_diagnostics.len()
                >= TARGETED_AUTHORING_CACHE_LIMITS_V1.detailed_diagnostics
        {
            return;
        }
        self.cache_diagnostics.push(
            CommandDiagnostic::info(
                DiagnosticKind::GeneratedArtifact,
                "targeted_authoring_cache_publication_failed",
            )
            .with_path(format!("modules[{module_index}]"))
            .with_field("targeted_authoring_cache")
            .with_actual_value(reason),
        );
    }

    fn record_publication_collision(
        &mut self,
        module_index: usize,
        validation: TargetedAuthoringSupportContextWriterValidation,
    ) {
        if !self.detailed_cache_diagnostics
            || self.cache_diagnostics.len()
                >= TARGETED_AUTHORING_CACHE_LIMITS_V1.detailed_diagnostics
        {
            return;
        }
        let reason_code = match validation {
            TargetedAuthoringSupportContextWriterValidation::Stale => {
                "targeted_authoring_cache_entry_stale"
            }
            TargetedAuthoringSupportContextWriterValidation::Invalid => {
                "targeted_authoring_cache_entry_invalid"
            }
        };
        self.cache_diagnostics.push(
            CommandDiagnostic::info(DiagnosticKind::GeneratedArtifact, reason_code)
                .with_path(format!("modules[{module_index}]"))
                .with_field("targeted_authoring_cache")
                .with_actual_value("operation=publication_collision"),
        );
    }

    pub(crate) fn adopt_remaining_cached_support<'session>(
        &mut self,
        session: &'session TargetedAuthoringBuildSession,
    ) -> Result<Vec<AdoptedCachedTargetedSupportContext<'session>>, CommandDiagnostic> {
        self.take_pending_contexts_in_dependency_order()?
            .into_iter()
            .map(|(module_index, pending)| {
                let context = session.adopt_cached_support(pending.pending);
                Ok(AdoptedCachedTargetedSupportContext {
                    module_index,
                    context,
                    source_interface: pending.source_interface,
                })
            })
            .collect()
    }

    pub(crate) fn consume_local_consumer(
        &mut self,
        consumer_index: usize,
    ) -> Result<Vec<usize>, CommandDiagnostic> {
        self.producer_lifetimes.consume_consumer(consumer_index)
    }

    pub(crate) fn register_target_lifetime(
        &mut self,
        module_index: usize,
        forced_live: bool,
    ) -> Result<bool, CommandDiagnostic> {
        let views = if forced_live {
            TargetedAuthoringProducerViews::LIVE_SUPPORT_OR_FORCED_TARGET
        } else {
            TargetedAuthoringProducerViews::FRESH_TARGET
        };
        self.producer_lifetimes.register(module_index, views)
    }

    pub(crate) fn record_late_support_ineligibility(
        &mut self,
        module_index: usize,
        reason: &'static str,
    ) {
        if !self.publication_suppressed.insert(module_index) {
            return;
        }
        if self.cache_diagnostics.len() < TARGETED_AUTHORING_CACHE_LIMITS_V1.detailed_diagnostics {
            self.cache_diagnostics.push(
                CommandDiagnostic::info(
                    DiagnosticKind::GeneratedArtifact,
                    "targeted_authoring_module_ineligible",
                )
                .with_path(format!("modules[{module_index}]"))
                .with_field("targeted_authoring_cache")
                .with_actual_value(reason),
            );
        }
    }

    fn record_cached_support_adoption(
        &mut self,
        module_index: usize,
    ) -> Result<(), CommandDiagnostic> {
        checked_increment(
            &mut self.state.context_hits,
            &mut self.state.count_overflowed,
        );
        checked_increment(
            &mut self.state.avoided_kernel_checks,
            &mut self.state.count_overflowed,
        );
        checked_increment(
            &mut self.state.avoided_source_interface_resolutions,
            &mut self.state.count_overflowed,
        );
        self.provenance.locally_accelerated = true;
        self.record_support_completion();
        self.producer_lifetimes
            .register(module_index, TargetedAuthoringProducerViews::CACHED_SUPPORT)?;
        Ok(())
    }

    fn take_pending_contexts_in_dependency_order(
        &mut self,
    ) -> Result<Vec<(usize, PendingCachedTargetedSupportContext)>, CommandDiagnostic> {
        let mut ordered = Vec::with_capacity(self.pending_contexts.len());
        for module_index in self.combined_local_order.clone() {
            let Some(pending) = self.pending_contexts.remove(&module_index) else {
                continue;
            };
            self.pending_context_indices_by_module
                .remove(pending.pending.module());
            self.retained_context_bytes = self
                .retained_context_bytes
                .checked_sub(pending.retained_bytes)
                .ok_or_else(|| {
                    targeted_authoring_plan_invalid("retained_context_bytes_underflow")
                })?;
            self.record_cached_support_adoption(module_index)?;
            ordered.push((module_index, pending));
        }
        if !self.pending_contexts.is_empty()
            || !self.pending_context_indices_by_module.is_empty()
            || self.retained_context_bytes != 0
        {
            return Err(targeted_authoring_plan_invalid(
                "pending_context_order_inconsistent",
            ));
        }
        Ok(ordered)
    }

    pub(crate) fn record_live_support_visit(&mut self, module_index: usize) {
        checked_increment(
            &mut self.state.visited_support,
            &mut self.state.count_overflowed,
        );
        if self.forced_live_support.contains(&module_index) {
            checked_increment(
                &mut self.state.context_ineligible,
                &mut self.state.count_overflowed,
            );
            if self.cache_diagnostics.len()
                < TARGETED_AUTHORING_CACHE_LIMITS_V1.detailed_diagnostics
            {
                let Some(reason) = self.forced_live_support_reasons.get(&module_index) else {
                    self.state.count_overflowed = true;
                    return;
                };
                self.cache_diagnostics.push(
                    CommandDiagnostic::info(
                        DiagnosticKind::GeneratedArtifact,
                        "targeted_authoring_module_ineligible",
                    )
                    .with_path(format!("modules[{module_index}]"))
                    .with_field("targeted_authoring_cache")
                    .with_actual_value(reason.as_str()),
                );
            }
        }
    }

    fn record_lookup_miss(&mut self, module_index: usize, outcome: TargetedAuthoringLookupMiss) {
        if self.lookup_misses.insert(module_index, outcome).is_some() {
            self.state.count_overflowed = true;
            return;
        }
        checked_increment(
            &mut self.state.context_misses,
            &mut self.state.count_overflowed,
        );
        let subset = match outcome {
            TargetedAuthoringLookupMiss::Stale => Some(&mut self.state.context_stale),
            TargetedAuthoringLookupMiss::SchemaMiss => Some(&mut self.state.context_schema_misses),
            TargetedAuthoringLookupMiss::Invalid => Some(&mut self.state.context_invalid),
            TargetedAuthoringLookupMiss::Missing | TargetedAuthoringLookupMiss::Unavailable => None,
        };
        if let Some(subset) = subset {
            checked_increment(subset, &mut self.state.count_overflowed);
        }
        if self.detailed_cache_diagnostics {
            if let Some(reason_code) = outcome.detail_reason() {
                if self.cache_diagnostics.len()
                    < TARGETED_AUTHORING_CACHE_LIMITS_V1.detailed_diagnostics
                {
                    self.cache_diagnostics.push(
                        CommandDiagnostic::info(DiagnosticKind::GeneratedArtifact, reason_code)
                            .with_field("targeted_authoring_cache")
                            .with_actual_value(format!("module_index={module_index}")),
                    );
                }
            }
        }
    }

    fn record_unavailable_diagnostic(&mut self) {
        if self.unavailable_diagnostic_recorded {
            return;
        }
        let diagnostic = self
            .support_cache_session
            .as_ref()
            .and_then(TargetedAuthoringSupportCacheSession::unavailable_diagnostic);
        if let Some(diagnostic) = diagnostic {
            self.cache_diagnostics.push(diagnostic);
            self.unavailable_diagnostic_recorded = true;
        }
    }

    fn disable_support_lookup_for_resource_limit(&mut self) {
        self.state.store_availability = TargetedAuthoringStoreAvailability::Unavailable;
        if let Some(session) = self.support_cache_session.as_mut() {
            session.disable_for_resource_limit();
        }
        self.support_key_context = None;
        self.support_key_accumulator = None;
        self.record_unavailable_diagnostic();
    }

    pub(crate) fn record_target_attempt(
        &mut self,
        module_index: usize,
        forced_live: bool,
    ) -> Result<(), CommandDiagnostic> {
        if !self.explicit_targets.contains(&module_index) {
            return Err(targeted_authoring_plan_invalid(
                "target_attempt_outside_explicit_targets",
            ));
        }
        if forced_live != self.forced_live_targets.contains(&module_index) {
            return Err(targeted_authoring_plan_invalid(
                "target_attempt_forced_role_mismatch",
            ));
        }
        if !self.attempted_targets.insert(module_index) {
            return Err(targeted_authoring_plan_invalid("target_attempt_repeated"));
        }
        self.target_attempt_order.push(module_index);
        checked_increment(
            &mut self.state.visited_targets,
            &mut self.state.count_overflowed,
        );
        checked_increment(
            &mut self.state.target_attempts,
            &mut self.state.count_overflowed,
        );
        checked_increment(
            &mut self.state.target_fresh_builds,
            &mut self.state.count_overflowed,
        );
        if forced_live {
            checked_increment(
                &mut self.state.targets_forced_live,
                &mut self.state.count_overflowed,
            );
        }
        Ok(())
    }

    pub(crate) fn record_support_completion(&mut self) {
        checked_increment(
            &mut self.state.completed_support,
            &mut self.state.count_overflowed,
        );
    }

    pub(crate) fn record_target_completion(&mut self) {
        checked_increment(
            &mut self.state.completed_targets,
            &mut self.state.count_overflowed,
        );
    }

    pub(crate) fn record_completed_external_visits(&mut self) {
        self.state.visited_external = self.plan.selected_external;
        self.state.completed_external = self.plan.selected_external;
    }

    fn finish(
        mut self,
        completed: bool,
        primary_diagnostic: Option<CommandDiagnostic>,
    ) -> TargetedAuthoringCheckBuild {
        let (loaded_bytes, loaded_overflowed) =
            bounded_count(self.support_store_budget.loaded_bytes());
        self.state.bytes_loaded = loaded_bytes;
        let (written_bytes, written_overflowed) =
            bounded_count(self.support_store_budget.written_bytes_for_summary());
        self.state.bytes_written = written_bytes;
        self.state.count_overflowed |= loaded_overflowed || written_overflowed;
        TargetedAuthoringCheckBuild {
            provenance: self.provenance,
            summary: TargetedAuthoringCheckSummary {
                plan: self.plan,
                run: self.state,
                completed,
            },
            primary_diagnostic,
            cache_diagnostics: self.cache_diagnostics,
        }
    }
}

#[derive(Debug)]
pub(crate) struct TargetedAuthoringCheckBuild {
    provenance: TargetedAuthoringProvenance,
    summary: TargetedAuthoringCheckSummary,
    primary_diagnostic: Option<CommandDiagnostic>,
    cache_diagnostics: Vec<CommandDiagnostic>,
}

impl TargetedAuthoringCheckBuild {
    fn into_command_output(
        self,
        command: &str,
        root: String,
        selection_diagnostic: CommandDiagnostic,
    ) -> TargetedAuthoringCommandOutput {
        let mut diagnostics = vec![selection_diagnostic];
        let failed = self.primary_diagnostic.is_some();
        if let Some(primary) = self.primary_diagnostic {
            diagnostics.push(primary);
        }
        diagnostics.extend(self.cache_diagnostics);
        diagnostics.push(self.summary.diagnostic(self.provenance));
        diagnostics.push(
            CommandDiagnostic::info(
                DiagnosticKind::GeneratedArtifact,
                TARGETED_AUTHORING_LOCAL_ONLY_REASON,
            )
            .with_field(TARGETED_AUTHORING_LOCAL_ONLY_FIELD)
            .with_actual_value(self.provenance.actual_value()),
        );
        if let Err(reason) = self.summary.validate(self.provenance) {
            diagnostics.push(
                CommandDiagnostic::error(
                    DiagnosticKind::Internal,
                    "targeted_authoring_result_invalid",
                )
                .with_field("targeted_authoring_cache")
                .with_actual_value(reason),
            );
        }
        let result = if failed
            || diagnostics
                .iter()
                .any(|diagnostic| diagnostic.kind == DiagnosticKind::Internal)
        {
            CommandResult::failed(command, root, diagnostics)
        } else {
            let mut result = CommandResult::passed(command, root);
            result.diagnostics = diagnostics;
            result
        };
        TargetedAuthoringCommandOutput {
            result,
            measurements: self.summary.measurement_snapshot(),
        }
    }
}

#[derive(Debug)]
pub(crate) struct TargetedAuthoringCommandOutput {
    result: CommandResult,
    measurements: TargetedAuthoringMeasurementSnapshot,
}

impl TargetedAuthoringCommandOutput {
    pub(crate) fn into_parts(self) -> (CommandResult, TargetedAuthoringMeasurementSnapshot) {
        (self.result, self.measurements)
    }
}

#[derive(Debug)]
pub(crate) struct TargetedAuthoringExecutionOutcome {
    completed: bool,
    primary_diagnostic: Option<CommandDiagnostic>,
}

impl TargetedAuthoringExecutionOutcome {
    pub(crate) fn completed(primary_diagnostic: Option<CommandDiagnostic>) -> Self {
        Self {
            completed: true,
            primary_diagnostic,
        }
    }

    pub(crate) fn stopped(primary_diagnostic: CommandDiagnostic) -> Self {
        Self {
            completed: false,
            primary_diagnostic: Some(primary_diagnostic),
        }
    }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn run_targeted_authoring_local_hit(
    command: &str,
    root: String,
    selection_diagnostic: CommandDiagnostic,
    plan: TargetedAuthoringCheckPlan,
    measurement_enabled: bool,
    detailed_cache_diagnostics: bool,
    build_execution_plan: impl FnOnce() -> Result<TargetedAuthoringExecutionPlan, CommandDiagnostic>,
    execute: impl FnOnce(
        &TargetedAuthoringExecutionPlan,
        &mut TargetedAuthoringCheckRun,
    ) -> TargetedAuthoringExecutionOutcome,
) -> TargetedAuthoringCommandOutput {
    let mut run = TargetedAuthoringCheckRun::new_with_measurements(
        plan,
        measurement_enabled,
        detailed_cache_diagnostics,
    );
    let execution_plan = match build_execution_plan() {
        Ok(plan) => plan,
        Err(diagnostic) => {
            return run.finish(false, Some(diagnostic)).into_command_output(
                command,
                root,
                selection_diagnostic,
            );
        }
    };
    if let Err(diagnostic) = run.adopt_execution_plan(&execution_plan) {
        return run.finish(false, Some(diagnostic)).into_command_output(
            command,
            root,
            selection_diagnostic,
        );
    }
    let outcome = execute(&execution_plan, &mut run);
    run.finish(outcome.completed, outcome.primary_diagnostic)
        .into_command_output(command, root, selection_diagnostic)
}

fn bounded_count(value: usize) -> (u64, bool) {
    match u64::try_from(value) {
        Ok(value) => (value, false),
        Err(_) => (u64::MAX, true),
    }
}

fn elapsed_ns(started: Instant) -> u64 {
    u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX)
}

fn checked_increment(value: &mut u64, overflowed: &mut bool) {
    let (next, did_overflow) = value.overflowing_add(1);
    *value = if did_overflow { u64::MAX } else { next };
    *overflowed |= did_overflow;
}

#[derive(Debug)]
pub(crate) struct TargetedAuthoringModuleBuild<'session> {
    certificate_bytes: Vec<u8>,
    compilation_observations: HumanCompilationObservations,
    authoring_observations: LocalAuthoringBuildObservations,
    source_interface: HumanSourceInterface,
    fresh_context: FreshTargetedAuthoringContext<'session>,
}

impl<'session> TargetedAuthoringModuleBuild<'session> {
    fn from_frontend(output: HumanAuthoringCertificateCompileOutput<'session>) -> Self {
        let (
            certificate_bytes,
            compilation_observations,
            authoring_observations,
            source_interface,
            fresh_context,
        ) = output.into_parts();
        debug_assert_eq!(
            authoring_observations.closure_used_cached_context(),
            fresh_context.closure_used_cached_context()
        );
        Self {
            certificate_bytes,
            compilation_observations,
            authoring_observations,
            source_interface,
            fresh_context: FreshTargetedAuthoringContext {
                context: fresh_context,
            },
        }
    }

    pub(crate) fn certificate_bytes(&self) -> &[u8] {
        &self.certificate_bytes
    }

    pub(crate) fn compilation_observations(&self) -> &HumanCompilationObservations {
        &self.compilation_observations
    }

    pub(crate) fn authoring_observations(&self) -> &LocalAuthoringBuildObservations {
        &self.authoring_observations
    }

    pub(crate) fn source_interface(&self) -> &HumanSourceInterface {
        &self.source_interface
    }

    pub(crate) fn imported_source_interface(&self) -> HumanImportedSourceInterface {
        HumanImportedSourceInterface {
            module: self.fresh_context.context.module().clone(),
            export_hash: self.fresh_context.context.export_hash(),
            certificate_hash: Some(self.fresh_context.context.certificate_hash()),
            source_interface: self.source_interface.clone(),
        }
    }

    pub(crate) fn fresh_context(&self) -> &FreshTargetedAuthoringContext<'session> {
        &self.fresh_context
    }

    pub(crate) fn fresh_import_context(&self) -> TargetedAuthoringImportContext<'session> {
        TargetedAuthoringImportContext::FreshTarget(self.fresh_context.clone())
    }

    pub(crate) const fn is_proof_evidence(&self) -> bool {
        false
    }

    pub(crate) const fn is_publication_eligible(&self) -> bool {
        false
    }
}

#[derive(Clone, Debug)]
pub(crate) struct FreshTargetedAuthoringContext<'session> {
    context: LocalAuthoringImportContext<'session>,
}

impl<'session> FreshTargetedAuthoringContext<'session> {
    pub(crate) fn authoring_import(&self) -> npa_cert::Result<HumanAuthoringImport<'session>> {
        HumanAuthoringImport::from_local_authoring_context(&self.context)
    }

    pub(crate) fn closure_used_cached_context(&self) -> bool {
        self.context.closure_used_cached_context()
    }

    pub(crate) const fn is_publication_eligible(&self) -> bool {
        false
    }

    pub(crate) const fn is_proof_evidence(&self) -> bool {
        false
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum HumanInterfaceCacheAdapterErrorKind {
    Unsupported,
    Invalid,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct HumanInterfaceCacheAdapterError {
    kind: HumanInterfaceCacheAdapterErrorKind,
    reason_code: &'static str,
    path: String,
}

impl HumanInterfaceCacheAdapterError {
    fn unsupported(reason_code: &'static str, path: impl Into<String>) -> Self {
        Self {
            kind: HumanInterfaceCacheAdapterErrorKind::Unsupported,
            reason_code,
            path: path.into(),
        }
    }

    fn invalid(reason_code: &'static str, path: impl Into<String>) -> Self {
        Self {
            kind: HumanInterfaceCacheAdapterErrorKind::Invalid,
            reason_code,
            path: path.into(),
        }
    }

    pub(crate) const fn kind(&self) -> HumanInterfaceCacheAdapterErrorKind {
        self.kind
    }

    pub(crate) const fn reason_code(&self) -> &'static str {
        self.reason_code
    }
}

impl fmt::Display for HumanInterfaceCacheAdapterError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{} at {}", self.reason_code, self.path)
    }
}

impl std::error::Error for HumanInterfaceCacheAdapterError {}

pub(crate) struct HumanInterfaceCacheAdapterContext<'context, 'session> {
    package: &'context PackageId,
    version: &'context PackageVersion,
    producer_profile: &'context str,
    direct_imports: &'context [ResolvedModuleImportIdentity],
    current_module_index: usize,
    source: &'context str,
    authoring_import: &'context HumanAuthoringImport<'session>,
}

impl<'context, 'session> HumanInterfaceCacheAdapterContext<'context, 'session> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        package: &'context PackageId,
        version: &'context PackageVersion,
        producer_profile: &'context str,
        direct_imports: &'context [ResolvedModuleImportIdentity],
        current_module_index: usize,
        source: &'context str,
        authoring_import: &'context HumanAuthoringImport<'session>,
    ) -> Self {
        Self {
            package,
            version,
            producer_profile,
            direct_imports,
            current_module_index,
            source,
            authoring_import,
        }
    }

    fn profile(
        &self,
    ) -> Result<TargetedAuthoringInterfaceProfile, HumanInterfaceCacheAdapterError> {
        match self.producer_profile {
            HUMAN_SOURCE_PRODUCER_PROFILE => Ok(TargetedAuthoringInterfaceProfile::HumanSource),
            LEGACY_STD_PACKAGE_PRODUCER_PROFILE | STD_PACKAGE_PRODUCER_PROFILE => {
                Ok(TargetedAuthoringInterfaceProfile::SyntheticCertificateFallback)
            }
            _ => Err(HumanInterfaceCacheAdapterError::unsupported(
                "unsupported_producer_profile",
                "producer_profile",
            )),
        }
    }

    fn file_id(
        &self,
        profile: TargetedAuthoringInterfaceProfile,
    ) -> Result<FileId, HumanInterfaceCacheAdapterError> {
        match profile {
            TargetedAuthoringInterfaceProfile::HumanSource => {
                checked_current_module_file_id(self.current_module_index)
            }
            TargetedAuthoringInterfaceProfile::SyntheticCertificateFallback => Ok(FileId(0)),
        }
    }
}

pub(crate) fn checked_current_module_file_id(
    current_module_index: usize,
) -> Result<FileId, HumanInterfaceCacheAdapterError> {
    u32::try_from(current_module_index)
        .map(FileId)
        .map_err(|_| {
            HumanInterfaceCacheAdapterError::invalid(
                "module_index_out_of_range",
                "current_module_index",
            )
        })
}

pub(crate) fn human_interface_to_cache_dto(
    interface: &HumanImportedSourceInterface,
    context: &HumanInterfaceCacheAdapterContext<'_, '_>,
) -> Result<TargetedAuthoringHumanImportedSourceInterface, HumanInterfaceCacheAdapterError> {
    let profile = context.profile()?;
    let file_id = context.file_id(profile)?;
    validate_runtime_outer_identity(interface, context)?;
    validate_runtime_profile(interface, profile)?;

    let source_interface = TargetedAuthoringHumanSourceInterface {
        module: interface.source_interface.module.clone(),
        declarations: interface
            .source_interface
            .declarations
            .iter()
            .enumerate()
            .map(|(index, declaration)| {
                declaration_to_dto(
                    declaration,
                    context,
                    profile,
                    file_id,
                    &format!("source_interface.declarations[{index}]"),
                )
            })
            .collect::<Result<_, _>>()?,
        notations: interface
            .source_interface
            .notations
            .iter()
            .enumerate()
            .map(|(index, notation)| {
                notation_to_dto(
                    notation,
                    context,
                    profile,
                    file_id,
                    &format!("source_interface.notations[{index}]"),
                )
            })
            .collect::<Result<_, _>>()?,
        generated_declarations: interface
            .source_interface
            .generated_declarations
            .iter()
            .enumerate()
            .map(|(index, generated)| {
                generated_to_dto(
                    generated,
                    context,
                    profile,
                    file_id,
                    &format!("source_interface.generated_declarations[{index}]"),
                )
            })
            .collect::<Result<_, _>>()?,
        typeclass_classes: interface
            .source_interface
            .typeclass_classes
            .iter()
            .enumerate()
            .map(|(index, class)| {
                class_to_dto(
                    class,
                    context,
                    profile,
                    file_id,
                    &format!("source_interface.typeclass_classes[{index}]"),
                )
            })
            .collect::<Result<_, _>>()?,
        typeclass_instances: interface
            .source_interface
            .typeclass_instances
            .iter()
            .enumerate()
            .map(|(index, instance)| {
                instance_to_dto(
                    instance,
                    context,
                    profile,
                    file_id,
                    &format!("source_interface.typeclass_instances[{index}]"),
                )
            })
            .collect::<Result<_, _>>()?,
    };

    validate_dto_catalog(&source_interface, context.direct_imports)?;
    validate_dto_interface_hashes(&source_interface, context)?;

    Ok(TargetedAuthoringHumanImportedSourceInterface {
        schema: PACKAGE_TARGETED_AUTHORING_HUMAN_INTERFACE_SCHEMA.to_owned(),
        module: interface.module.clone(),
        export_hash: PackageHash::from(interface.export_hash),
        certificate_hash: PackageHash::from(interface.certificate_hash.ok_or_else(|| {
            HumanInterfaceCacheAdapterError::unsupported(
                "certificate_hash_unrepresentable",
                "certificate_hash",
            )
        })?),
        source: TargetedAuthoringSourceIdentity {
            package: context.package.clone(),
            version: context.version.clone(),
            module: interface.module.clone(),
            source_hash: package_file_hash(context.source.as_bytes()),
        },
        producer_profile: context.producer_profile.to_owned(),
        direct_imports: context.direct_imports.to_vec(),
        source_interface,
    })
}

fn validate_runtime_profile(
    interface: &HumanImportedSourceInterface,
    profile: TargetedAuthoringInterfaceProfile,
) -> Result<(), HumanInterfaceCacheAdapterError> {
    let source = &interface.source_interface;
    match profile {
        TargetedAuthoringInterfaceProfile::HumanSource => {
            if source
                .declarations
                .iter()
                .any(|declaration| declaration.kind == HumanSourceDeclarationKind::Imported)
            {
                return Err(HumanInterfaceCacheAdapterError::unsupported(
                    "interface_profile_unrepresentable",
                    "source_interface.declarations",
                ));
            }
        }
        TargetedAuthoringInterfaceProfile::SyntheticCertificateFallback => {
            if !source.notations.is_empty()
                || !source.generated_declarations.is_empty()
                || !source.typeclass_classes.is_empty()
                || !source.typeclass_instances.is_empty()
                || source.declarations.iter().any(|declaration| {
                    declaration.kind != HumanSourceDeclarationKind::Imported
                        || !declaration.binders.is_empty()
                })
            {
                return Err(HumanInterfaceCacheAdapterError::unsupported(
                    "interface_profile_unrepresentable",
                    "source_interface",
                ));
            }
        }
    }
    Ok(())
}

pub(crate) fn cache_entry_to_human_interface(
    entry: &TargetedAuthoringSupportContextEntry,
    context: &HumanInterfaceCacheAdapterContext<'_, '_>,
) -> Result<HumanImportedSourceInterface, HumanInterfaceCacheAdapterError> {
    let profile = context.profile()?;
    if entry.interface_profile != profile {
        return Err(HumanInterfaceCacheAdapterError::unsupported(
            "interface_profile_unsupported",
            "interface_profile",
        ));
    }
    let file_id = context.file_id(profile)?;

    validate_targeted_authoring_support_context_source_bytes(entry, context.source.as_bytes())
        .map_err(|error| {
            HumanInterfaceCacheAdapterError::invalid(
                "support_context_entry_invalid",
                format!("{:?}:{}", error.reason_code, error.path),
            )
        })?;
    validate_cache_entry_live_identity(entry, context)?;
    validate_dto_interface_hashes(&entry.source_interface.source_interface, context)?;

    Ok(HumanImportedSourceInterface {
        module: entry.source_interface.module.clone(),
        export_hash: entry.source_interface.export_hash.into_bytes(),
        certificate_hash: Some(entry.source_interface.certificate_hash.into_bytes()),
        source_interface: HumanSourceInterface {
            module: entry.source_interface.source_interface.module.clone(),
            declarations: entry
                .source_interface
                .source_interface
                .declarations
                .iter()
                .map(|declaration| declaration_from_dto(declaration, file_id))
                .collect(),
            notations: entry
                .source_interface
                .source_interface
                .notations
                .iter()
                .map(|notation| notation_from_dto(notation, file_id))
                .collect(),
            generated_declarations: entry
                .source_interface
                .source_interface
                .generated_declarations
                .iter()
                .map(|generated| generated_from_dto(generated, file_id))
                .collect(),
            typeclass_classes: entry
                .source_interface
                .source_interface
                .typeclass_classes
                .iter()
                .map(|class| class_from_dto(class, file_id))
                .collect(),
            typeclass_instances: entry
                .source_interface
                .source_interface
                .typeclass_instances
                .iter()
                .map(|instance| instance_from_dto(instance, file_id))
                .collect(),
        },
    })
}

fn validate_runtime_outer_identity(
    interface: &HumanImportedSourceInterface,
    context: &HumanInterfaceCacheAdapterContext<'_, '_>,
) -> Result<(), HumanInterfaceCacheAdapterError> {
    if &interface.module != context.authoring_import.module()
        || interface.source_interface.module != interface.module
    {
        return Err(HumanInterfaceCacheAdapterError::invalid(
            "module_identity_mismatch",
            "module",
        ));
    }
    if interface.export_hash != context.authoring_import.export_hash() {
        return Err(HumanInterfaceCacheAdapterError::invalid(
            "export_hash_mismatch",
            "export_hash",
        ));
    }
    let Some(certificate_hash) = interface.certificate_hash else {
        return Err(HumanInterfaceCacheAdapterError::unsupported(
            "certificate_hash_unrepresentable",
            "certificate_hash",
        ));
    };
    if Some(certificate_hash) != context.authoring_import.certificate_hash() {
        return Err(HumanInterfaceCacheAdapterError::invalid(
            "certificate_hash_mismatch",
            "certificate_hash",
        ));
    }
    Ok(())
}

fn validate_cache_entry_live_identity(
    entry: &TargetedAuthoringSupportContextEntry,
    context: &HumanInterfaceCacheAdapterContext<'_, '_>,
) -> Result<(), HumanInterfaceCacheAdapterError> {
    let dto = &entry.source_interface;
    if &entry.key_input.package != context.package
        || &entry.key_input.version != context.version
        || entry.key_input.producer_profile != context.producer_profile
        || dto.source.package != *context.package
        || dto.source.version != *context.version
        || dto.producer_profile != context.producer_profile
    {
        return Err(HumanInterfaceCacheAdapterError::invalid(
            "source_identity_mismatch",
            "key_input/source_interface",
        ));
    }
    if entry.key_input.manifest_human_imports != context.direct_imports
        || dto.direct_imports != context.direct_imports
    {
        return Err(HumanInterfaceCacheAdapterError::invalid(
            "direct_import_identity_mismatch",
            "direct_imports",
        ));
    }
    if &dto.module != context.authoring_import.module()
        || dto.source.module != dto.module
        || dto.source_interface.module != dto.module
    {
        return Err(HumanInterfaceCacheAdapterError::invalid(
            "module_identity_mismatch",
            "source_interface.module",
        ));
    }
    if dto.export_hash.into_bytes() != context.authoring_import.export_hash() {
        return Err(HumanInterfaceCacheAdapterError::invalid(
            "export_hash_mismatch",
            "source_interface.export_hash",
        ));
    }
    if Some(dto.certificate_hash.into_bytes()) != context.authoring_import.certificate_hash() {
        return Err(HumanInterfaceCacheAdapterError::invalid(
            "certificate_hash_mismatch",
            "source_interface.certificate_hash",
        ));
    }
    Ok(())
}

fn span_to_dto(
    span: Span,
    profile: TargetedAuthoringInterfaceProfile,
    expected_file_id: FileId,
    source: &str,
    path: &str,
) -> Result<TargetedAuthoringSpan, HumanInterfaceCacheAdapterError> {
    let expected_origin = match profile {
        TargetedAuthoringInterfaceProfile::HumanSource => {
            TargetedAuthoringSpanOrigin::CurrentModule
        }
        TargetedAuthoringInterfaceProfile::SyntheticCertificateFallback => {
            TargetedAuthoringSpanOrigin::SyntheticFallback
        }
    };
    if span.file_id != expected_file_id {
        return Err(HumanInterfaceCacheAdapterError::unsupported(
            "span_origin_unrepresentable",
            path,
        ));
    }
    if span.start.0 > span.end.0 {
        return Err(HumanInterfaceCacheAdapterError::invalid(
            "span_offsets_invalid",
            path,
        ));
    }
    match profile {
        TargetedAuthoringInterfaceProfile::HumanSource => {
            let start = usize::try_from(span.start.0).map_err(|_| {
                HumanInterfaceCacheAdapterError::invalid("span_offsets_invalid", path)
            })?;
            let end = usize::try_from(span.end.0).map_err(|_| {
                HumanInterfaceCacheAdapterError::invalid("span_offsets_invalid", path)
            })?;
            if end > source.len()
                || !source.is_char_boundary(start)
                || !source.is_char_boundary(end)
            {
                return Err(HumanInterfaceCacheAdapterError::invalid(
                    "span_utf8_boundary_invalid",
                    path,
                ));
            }
        }
        TargetedAuthoringInterfaceProfile::SyntheticCertificateFallback => {
            if span.start.0 != 0 || span.end.0 != 0 {
                return Err(HumanInterfaceCacheAdapterError::unsupported(
                    "synthetic_span_unrepresentable",
                    path,
                ));
            }
        }
    }
    Ok(TargetedAuthoringSpan {
        origin: expected_origin,
        start: span.start.0,
        end: span.end.0,
    })
}

fn name_to_dto(
    name: &HumanName,
    profile: TargetedAuthoringInterfaceProfile,
    file_id: FileId,
    source: &str,
    path: &str,
) -> Result<TargetedAuthoringHumanName, HumanInterfaceCacheAdapterError> {
    Ok(TargetedAuthoringHumanName {
        parts: name.parts.clone(),
        span: span_to_dto(name.span, profile, file_id, source, path)?,
    })
}

fn declaration_to_dto(
    declaration: &HumanSourceDeclarationMetadata,
    context: &HumanInterfaceCacheAdapterContext<'_, '_>,
    profile: TargetedAuthoringInterfaceProfile,
    file_id: FileId,
    path: &str,
) -> Result<TargetedAuthoringHumanDeclaration, HumanInterfaceCacheAdapterError> {
    Ok(TargetedAuthoringHumanDeclaration {
        kind: declaration_kind_to_dto(declaration.kind),
        definition_reducibility: declaration.definition_reducibility.map(reducibility_to_dto),
        name: name_to_dto(
            &declaration.name,
            profile,
            file_id,
            context.source,
            &format!("{path}.name"),
        )?,
        universe_params: declaration
            .universe_params
            .iter()
            .enumerate()
            .map(|(index, parameter)| {
                Ok(TargetedAuthoringHumanUniverseParameter {
                    name: parameter.name.clone(),
                    span: span_to_dto(
                        parameter.span,
                        profile,
                        file_id,
                        context.source,
                        &format!("{path}.universe_params[{index}].span"),
                    )?,
                })
            })
            .collect::<Result<_, _>>()?,
        binders: declaration
            .binders
            .iter()
            .enumerate()
            .map(|(index, binder)| {
                binder_to_dto(
                    binder,
                    profile,
                    file_id,
                    context.source,
                    &format!("{path}.binders[{index}]"),
                )
            })
            .collect::<Result<_, _>>()?,
        decl_interface_hash: declaration.decl_interface_hash.map(PackageHash::from),
        span: span_to_dto(
            declaration.span,
            profile,
            file_id,
            context.source,
            &format!("{path}.span"),
        )?,
    })
}

fn binder_to_dto(
    binder: &HumanSourceBinderMetadata,
    profile: TargetedAuthoringInterfaceProfile,
    file_id: FileId,
    source: &str,
    path: &str,
) -> Result<TargetedAuthoringHumanBinder, HumanInterfaceCacheAdapterError> {
    Ok(TargetedAuthoringHumanBinder {
        name: binder
            .name
            .as_ref()
            .map(|name| name_to_dto(name, profile, file_id, source, &format!("{path}.name")))
            .transpose()?,
        binder_info: binder_info_to_dto(binder.binder_info),
        span: span_to_dto(
            binder.span,
            profile,
            file_id,
            source,
            &format!("{path}.span"),
        )?,
    })
}

fn notation_to_dto(
    notation: &HumanSourceNotationMetadata,
    context: &HumanInterfaceCacheAdapterContext<'_, '_>,
    profile: TargetedAuthoringInterfaceProfile,
    file_id: FileId,
    path: &str,
) -> Result<TargetedAuthoringHumanNotation, HumanInterfaceCacheAdapterError> {
    Ok(TargetedAuthoringHumanNotation {
        kind: notation_kind_to_dto(notation.kind),
        associativity: notation_associativity_to_dto(notation.associativity),
        precedence: notation.precedence,
        token: notation.token.clone(),
        target: name_to_dto(
            &notation.target,
            profile,
            file_id,
            context.source,
            &format!("{path}.target"),
        )?,
        namespace: notation.namespace.clone(),
        span: span_to_dto(
            notation.span,
            profile,
            file_id,
            context.source,
            &format!("{path}.span"),
        )?,
    })
}

fn generated_to_dto(
    generated: &HumanGeneratedDeclarationMetadata,
    context: &HumanInterfaceCacheAdapterContext<'_, '_>,
    profile: TargetedAuthoringInterfaceProfile,
    file_id: FileId,
    path: &str,
) -> Result<TargetedAuthoringHumanGeneratedDeclaration, HumanInterfaceCacheAdapterError> {
    Ok(TargetedAuthoringHumanGeneratedDeclaration {
        kind: generated_kind_to_dto(generated.kind),
        parent: name_to_dto(
            &generated.parent,
            profile,
            file_id,
            context.source,
            &format!("{path}.parent"),
        )?,
        name: name_to_dto(
            &generated.name,
            profile,
            file_id,
            context.source,
            &format!("{path}.name"),
        )?,
        decl_interface_hash: generated.decl_interface_hash.map(PackageHash::from),
        span: span_to_dto(
            generated.span,
            profile,
            file_id,
            context.source,
            &format!("{path}.span"),
        )?,
    })
}

fn class_to_dto(
    class: &HumanTypeclassClassMetadata,
    context: &HumanInterfaceCacheAdapterContext<'_, '_>,
    profile: TargetedAuthoringInterfaceProfile,
    file_id: FileId,
    path: &str,
) -> Result<TargetedAuthoringHumanTypeclassClass, HumanInterfaceCacheAdapterError> {
    Ok(TargetedAuthoringHumanTypeclassClass {
        name: name_to_dto(
            &class.name,
            profile,
            file_id,
            context.source,
            &format!("{path}.name"),
        )?,
        constructor: name_to_dto(
            &class.constructor,
            profile,
            file_id,
            context.source,
            &format!("{path}.constructor"),
        )?,
        fields: class
            .fields
            .iter()
            .enumerate()
            .map(|(index, field)| {
                field_to_dto(
                    field,
                    context,
                    profile,
                    file_id,
                    &format!("{path}.fields[{index}]"),
                )
            })
            .collect::<Result<_, _>>()?,
        decl_interface_hash: class.decl_interface_hash.map(PackageHash::from),
        span: span_to_dto(
            class.span,
            profile,
            file_id,
            context.source,
            &format!("{path}.span"),
        )?,
    })
}

fn field_to_dto(
    field: &HumanTypeclassFieldMetadata,
    context: &HumanInterfaceCacheAdapterContext<'_, '_>,
    profile: TargetedAuthoringInterfaceProfile,
    file_id: FileId,
    path: &str,
) -> Result<TargetedAuthoringHumanTypeclassField, HumanInterfaceCacheAdapterError> {
    Ok(TargetedAuthoringHumanTypeclassField {
        name: name_to_dto(
            &field.name,
            profile,
            file_id,
            context.source,
            &format!("{path}.name"),
        )?,
        projection: name_to_dto(
            &field.projection,
            profile,
            file_id,
            context.source,
            &format!("{path}.projection"),
        )?,
        decl_interface_hash: field.decl_interface_hash.map(PackageHash::from),
        span: span_to_dto(
            field.span,
            profile,
            file_id,
            context.source,
            &format!("{path}.span"),
        )?,
    })
}

fn instance_to_dto(
    instance: &HumanTypeclassInstanceMetadata,
    context: &HumanInterfaceCacheAdapterContext<'_, '_>,
    profile: TargetedAuthoringInterfaceProfile,
    file_id: FileId,
    path: &str,
) -> Result<TargetedAuthoringHumanTypeclassInstance, HumanInterfaceCacheAdapterError> {
    Ok(TargetedAuthoringHumanTypeclassInstance {
        name: name_to_dto(
            &instance.name,
            profile,
            file_id,
            context.source,
            &format!("{path}.name"),
        )?,
        class: instance
            .class
            .as_ref()
            .map(|class| {
                name_to_dto(
                    class,
                    profile,
                    file_id,
                    context.source,
                    &format!("{path}.class"),
                )
            })
            .transpose()?,
        priority: instance.priority,
        decl_interface_hash: instance.decl_interface_hash.map(PackageHash::from),
        span: span_to_dto(
            instance.span,
            profile,
            file_id,
            context.source,
            &format!("{path}.span"),
        )?,
    })
}

fn declaration_kind_to_dto(
    kind: HumanSourceDeclarationKind,
) -> TargetedAuthoringHumanDeclarationKind {
    match kind {
        HumanSourceDeclarationKind::Def => TargetedAuthoringHumanDeclarationKind::Def,
        HumanSourceDeclarationKind::Theorem => TargetedAuthoringHumanDeclarationKind::Theorem,
        HumanSourceDeclarationKind::Axiom => TargetedAuthoringHumanDeclarationKind::Axiom,
        HumanSourceDeclarationKind::Inductive => TargetedAuthoringHumanDeclarationKind::Inductive,
        HumanSourceDeclarationKind::Class => TargetedAuthoringHumanDeclarationKind::Class,
        HumanSourceDeclarationKind::ClassField => TargetedAuthoringHumanDeclarationKind::ClassField,
        HumanSourceDeclarationKind::Instance => TargetedAuthoringHumanDeclarationKind::Instance,
        HumanSourceDeclarationKind::Imported => TargetedAuthoringHumanDeclarationKind::Imported,
    }
}

fn reducibility_to_dto(value: DefinitionReducibility) -> TargetedAuthoringDefinitionReducibility {
    match value {
        DefinitionReducibility::Reducible => TargetedAuthoringDefinitionReducibility::Reducible,
        DefinitionReducibility::Opaque => TargetedAuthoringDefinitionReducibility::Opaque,
    }
}

fn binder_info_to_dto(value: HumanBinderInfo) -> TargetedAuthoringHumanBinderInfo {
    match value {
        HumanBinderInfo::Explicit => TargetedAuthoringHumanBinderInfo::Explicit,
        HumanBinderInfo::Implicit => TargetedAuthoringHumanBinderInfo::Implicit,
    }
}

fn notation_kind_to_dto(value: HumanNotationKind) -> TargetedAuthoringHumanNotationKind {
    match value {
        HumanNotationKind::Notation => TargetedAuthoringHumanNotationKind::Notation,
        HumanNotationKind::Prefix => TargetedAuthoringHumanNotationKind::Prefix,
        HumanNotationKind::Postfix => TargetedAuthoringHumanNotationKind::Postfix,
        HumanNotationKind::Infix => TargetedAuthoringHumanNotationKind::Infix,
        HumanNotationKind::Infixl => TargetedAuthoringHumanNotationKind::Infixl,
        HumanNotationKind::Infixr => TargetedAuthoringHumanNotationKind::Infixr,
    }
}

fn notation_associativity_to_dto(
    value: HumanNotationAssociativity,
) -> TargetedAuthoringHumanNotationAssociativity {
    match value {
        HumanNotationAssociativity::Left => TargetedAuthoringHumanNotationAssociativity::Left,
        HumanNotationAssociativity::Right => TargetedAuthoringHumanNotationAssociativity::Right,
        HumanNotationAssociativity::NonAssoc => {
            TargetedAuthoringHumanNotationAssociativity::NonAssoc
        }
    }
}

fn generated_kind_to_dto(
    value: HumanGeneratedDeclarationKind,
) -> TargetedAuthoringHumanGeneratedDeclarationKind {
    match value {
        HumanGeneratedDeclarationKind::Constructor => {
            TargetedAuthoringHumanGeneratedDeclarationKind::Constructor
        }
        HumanGeneratedDeclarationKind::Recursor => {
            TargetedAuthoringHumanGeneratedDeclarationKind::Recursor
        }
    }
}

fn span_from_dto(span: TargetedAuthoringSpan, file_id: FileId) -> Span {
    Span::new(file_id, span.start, span.end)
}

fn name_from_dto(name: &TargetedAuthoringHumanName, file_id: FileId) -> HumanName {
    HumanName::new(name.parts.clone(), span_from_dto(name.span, file_id))
}

fn declaration_from_dto(
    declaration: &TargetedAuthoringHumanDeclaration,
    file_id: FileId,
) -> HumanSourceDeclarationMetadata {
    HumanSourceDeclarationMetadata {
        kind: match declaration.kind {
            TargetedAuthoringHumanDeclarationKind::Def => HumanSourceDeclarationKind::Def,
            TargetedAuthoringHumanDeclarationKind::Theorem => HumanSourceDeclarationKind::Theorem,
            TargetedAuthoringHumanDeclarationKind::Axiom => HumanSourceDeclarationKind::Axiom,
            TargetedAuthoringHumanDeclarationKind::Inductive => {
                HumanSourceDeclarationKind::Inductive
            }
            TargetedAuthoringHumanDeclarationKind::Class => HumanSourceDeclarationKind::Class,
            TargetedAuthoringHumanDeclarationKind::ClassField => {
                HumanSourceDeclarationKind::ClassField
            }
            TargetedAuthoringHumanDeclarationKind::Instance => HumanSourceDeclarationKind::Instance,
            TargetedAuthoringHumanDeclarationKind::Imported => HumanSourceDeclarationKind::Imported,
        },
        definition_reducibility: declaration
            .definition_reducibility
            .map(|value| match value {
                TargetedAuthoringDefinitionReducibility::Reducible => {
                    DefinitionReducibility::Reducible
                }
                TargetedAuthoringDefinitionReducibility::Opaque => DefinitionReducibility::Opaque,
            }),
        name: name_from_dto(&declaration.name, file_id),
        universe_params: declaration
            .universe_params
            .iter()
            .map(|parameter| HumanUniverseParam {
                name: parameter.name.clone(),
                span: span_from_dto(parameter.span, file_id),
            })
            .collect(),
        binders: declaration
            .binders
            .iter()
            .map(|binder| HumanSourceBinderMetadata {
                name: binder
                    .name
                    .as_ref()
                    .map(|name| name_from_dto(name, file_id)),
                binder_info: match binder.binder_info {
                    TargetedAuthoringHumanBinderInfo::Explicit => HumanBinderInfo::Explicit,
                    TargetedAuthoringHumanBinderInfo::Implicit => HumanBinderInfo::Implicit,
                },
                span: span_from_dto(binder.span, file_id),
            })
            .collect(),
        decl_interface_hash: declaration.decl_interface_hash.map(PackageHash::into_bytes),
        span: span_from_dto(declaration.span, file_id),
    }
}

fn notation_from_dto(
    notation: &TargetedAuthoringHumanNotation,
    file_id: FileId,
) -> HumanSourceNotationMetadata {
    HumanSourceNotationMetadata {
        kind: match notation.kind {
            TargetedAuthoringHumanNotationKind::Notation => HumanNotationKind::Notation,
            TargetedAuthoringHumanNotationKind::Prefix => HumanNotationKind::Prefix,
            TargetedAuthoringHumanNotationKind::Postfix => HumanNotationKind::Postfix,
            TargetedAuthoringHumanNotationKind::Infix => HumanNotationKind::Infix,
            TargetedAuthoringHumanNotationKind::Infixl => HumanNotationKind::Infixl,
            TargetedAuthoringHumanNotationKind::Infixr => HumanNotationKind::Infixr,
        },
        associativity: match notation.associativity {
            TargetedAuthoringHumanNotationAssociativity::Left => HumanNotationAssociativity::Left,
            TargetedAuthoringHumanNotationAssociativity::Right => HumanNotationAssociativity::Right,
            TargetedAuthoringHumanNotationAssociativity::NonAssoc => {
                HumanNotationAssociativity::NonAssoc
            }
        },
        precedence: notation.precedence,
        token: notation.token.clone(),
        target: name_from_dto(&notation.target, file_id),
        namespace: notation.namespace.clone(),
        span: span_from_dto(notation.span, file_id),
    }
}

fn generated_from_dto(
    generated: &TargetedAuthoringHumanGeneratedDeclaration,
    file_id: FileId,
) -> HumanGeneratedDeclarationMetadata {
    HumanGeneratedDeclarationMetadata {
        kind: match generated.kind {
            TargetedAuthoringHumanGeneratedDeclarationKind::Constructor => {
                HumanGeneratedDeclarationKind::Constructor
            }
            TargetedAuthoringHumanGeneratedDeclarationKind::Recursor => {
                HumanGeneratedDeclarationKind::Recursor
            }
        },
        parent: name_from_dto(&generated.parent, file_id),
        name: name_from_dto(&generated.name, file_id),
        decl_interface_hash: generated.decl_interface_hash.map(PackageHash::into_bytes),
        span: span_from_dto(generated.span, file_id),
    }
}

fn class_from_dto(
    class: &TargetedAuthoringHumanTypeclassClass,
    file_id: FileId,
) -> HumanTypeclassClassMetadata {
    HumanTypeclassClassMetadata {
        name: name_from_dto(&class.name, file_id),
        constructor: name_from_dto(&class.constructor, file_id),
        fields: class
            .fields
            .iter()
            .map(|field| HumanTypeclassFieldMetadata {
                name: name_from_dto(&field.name, file_id),
                projection: name_from_dto(&field.projection, file_id),
                decl_interface_hash: field.decl_interface_hash.map(PackageHash::into_bytes),
                span: span_from_dto(field.span, file_id),
            })
            .collect(),
        decl_interface_hash: class.decl_interface_hash.map(PackageHash::into_bytes),
        span: span_from_dto(class.span, file_id),
    }
}

fn instance_from_dto(
    instance: &TargetedAuthoringHumanTypeclassInstance,
    file_id: FileId,
) -> HumanTypeclassInstanceMetadata {
    HumanTypeclassInstanceMetadata {
        name: name_from_dto(&instance.name, file_id),
        class: instance
            .class
            .as_ref()
            .map(|class| name_from_dto(class, file_id)),
        priority: instance.priority,
        decl_interface_hash: instance.decl_interface_hash.map(PackageHash::into_bytes),
        span: span_from_dto(instance.span, file_id),
    }
}

fn validate_dto_catalog(
    interface: &TargetedAuthoringHumanSourceInterface,
    direct_imports: &[ResolvedModuleImportIdentity],
) -> Result<(), HumanInterfaceCacheAdapterError> {
    let mut catalog = BTreeSet::new();
    for (index, declaration) in interface.declarations.iter().enumerate() {
        let name = canonical_name(&declaration.name, &format!("declarations[{index}].name"))?;
        if !catalog.insert(name) {
            return Err(HumanInterfaceCacheAdapterError::invalid(
                "duplicate_declaration",
                format!("declarations[{index}].name"),
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
            return Err(HumanInterfaceCacheAdapterError::invalid(
                "definition_reducibility_kind_mismatch",
                format!("declarations[{index}].definition_reducibility"),
            ));
        }
    }
    for (index, generated) in interface.generated_declarations.iter().enumerate() {
        require_catalog_target(
            &generated.parent,
            &catalog,
            direct_imports,
            &format!("generated_declarations[{index}].parent"),
        )?;
        let name = canonical_name(
            &generated.name,
            &format!("generated_declarations[{index}].name"),
        )?;
        if !catalog.insert(name) {
            return Err(HumanInterfaceCacheAdapterError::invalid(
                "duplicate_generated_declaration",
                format!("generated_declarations[{index}].name"),
            ));
        }
    }
    for (index, notation) in interface.notations.iter().enumerate() {
        require_catalog_target(
            &notation.target,
            &catalog,
            direct_imports,
            &format!("notations[{index}].target"),
        )?;
    }
    for (class_index, class) in interface.typeclass_classes.iter().enumerate() {
        require_catalog_target(
            &class.name,
            &catalog,
            direct_imports,
            &format!("typeclass_classes[{class_index}].name"),
        )?;
        require_catalog_target(
            &class.constructor,
            &catalog,
            direct_imports,
            &format!("typeclass_classes[{class_index}].constructor"),
        )?;
        for (field_index, field) in class.fields.iter().enumerate() {
            canonical_name(
                &field.name,
                &format!("typeclass_classes[{class_index}].fields[{field_index}].name"),
            )?;
            require_catalog_target(
                &field.projection,
                &catalog,
                direct_imports,
                &format!("typeclass_classes[{class_index}].fields[{field_index}].projection"),
            )?;
        }
    }
    for (index, instance) in interface.typeclass_instances.iter().enumerate() {
        require_catalog_target(
            &instance.name,
            &catalog,
            direct_imports,
            &format!("typeclass_instances[{index}].name"),
        )?;
        if let Some(class) = &instance.class {
            require_catalog_target(
                class,
                &catalog,
                direct_imports,
                &format!("typeclass_instances[{index}].class"),
            )?;
        }
    }
    Ok(())
}

fn canonical_name(
    name: &TargetedAuthoringHumanName,
    path: &str,
) -> Result<Name, HumanInterfaceCacheAdapterError> {
    let name = Name(name.parts.clone());
    if name.is_canonical() {
        Ok(name)
    } else {
        Err(HumanInterfaceCacheAdapterError::invalid(
            "invalid_declaration_name",
            path,
        ))
    }
}

fn require_catalog_target(
    target: &TargetedAuthoringHumanName,
    catalog: &BTreeSet<Name>,
    direct_imports: &[ResolvedModuleImportIdentity],
    path: &str,
) -> Result<(), HumanInterfaceCacheAdapterError> {
    let target = canonical_name(target, path)?;
    let imported = direct_imports.iter().any(|import| {
        target.0.len() > import.module.0.len() && target.0.starts_with(import.module.0.as_slice())
    });
    if catalog.contains(&target) || imported {
        Ok(())
    } else {
        Err(HumanInterfaceCacheAdapterError::invalid(
            "interface_catalog_reference_missing",
            path,
        ))
    }
}

fn validate_dto_interface_hashes(
    interface: &TargetedAuthoringHumanSourceInterface,
    context: &HumanInterfaceCacheAdapterContext<'_, '_>,
) -> Result<(), HumanInterfaceCacheAdapterError> {
    let mut represented_exports = BTreeSet::new();
    for (index, declaration) in interface.declarations.iter().enumerate() {
        represented_exports.insert(validate_interface_hash(
            &declaration.name,
            declaration.decl_interface_hash,
            context,
            &format!("declarations[{index}].decl_interface_hash"),
        )?);
    }
    for (index, generated) in interface.generated_declarations.iter().enumerate() {
        represented_exports.insert(validate_interface_hash(
            &generated.name,
            generated.decl_interface_hash,
            context,
            &format!("generated_declarations[{index}].decl_interface_hash"),
        )?);
    }
    for (class_index, class) in interface.typeclass_classes.iter().enumerate() {
        validate_interface_hash(
            &class.name,
            class.decl_interface_hash,
            context,
            &format!("typeclass_classes[{class_index}].decl_interface_hash"),
        )?;
        for (field_index, field) in class.fields.iter().enumerate() {
            validate_interface_hash(
                &field.projection,
                field.decl_interface_hash,
                context,
                &format!(
                    "typeclass_classes[{class_index}].fields[{field_index}].decl_interface_hash"
                ),
            )?;
        }
    }
    for (index, instance) in interface.typeclass_instances.iter().enumerate() {
        validate_interface_hash(
            &instance.name,
            instance.decl_interface_hash,
            context,
            &format!("typeclass_instances[{index}].decl_interface_hash"),
        )?;
    }
    if let Some(missing) = context
        .authoring_import
        .exports()
        .iter()
        .find(|export| !represented_exports.contains(&export.name))
    {
        return Err(HumanInterfaceCacheAdapterError::invalid(
            "interface_catalog_incomplete",
            missing.name.as_dotted(),
        ));
    }
    Ok(())
}

fn validate_interface_hash(
    name: &TargetedAuthoringHumanName,
    actual: Option<PackageHash>,
    context: &HumanInterfaceCacheAdapterContext<'_, '_>,
    path: &str,
) -> Result<Name, HumanInterfaceCacheAdapterError> {
    let name = canonical_name(name, path)?;
    let hashes = context.authoring_import.declaration_interface_hashes();
    let mut prefixed = context.authoring_import.module().0.clone();
    prefixed.extend(name.0.clone());
    let prefixed = Name(prefixed);
    let matched_name = if hashes.contains_key(&name)
        || context
            .authoring_import
            .exports()
            .iter()
            .any(|export| export.name == name)
    {
        name
    } else {
        prefixed
    };
    let expected = hashes.get(&matched_name).or_else(|| {
        context
            .authoring_import
            .exports()
            .iter()
            .find(|export| export.name == matched_name)
            .map(|export| &export.decl_interface_hash)
    });
    let Some(expected) = expected else {
        return Err(HumanInterfaceCacheAdapterError::invalid(
            "interface_hash_target_missing",
            path,
        ));
    };
    let Some(actual) = actual else {
        return Err(HumanInterfaceCacheAdapterError::unsupported(
            "interface_hash_unrepresentable",
            path,
        ));
    };
    if actual.as_bytes() != expected {
        return Err(HumanInterfaceCacheAdapterError::invalid(
            "interface_hash_mismatch",
            path,
        ));
    }
    Ok(matched_name)
}

#[cfg(test)]
mod tests {
    use npa_cert::{encode_module_cert, AxiomPolicy, ModuleCert, VerifiedModule};
    use npa_frontend::{
        compile_human_source_to_certificate_output_with_source_interfaces_and_axiom_policy,
        compile_human_source_to_observed_certificate_output_with_available_import_refs_and_axiom_policy,
        elaborate_human_module_with_authoring_imports, parse_human_module_with_source_interfaces,
        resolve_human_module_with_authoring_imports_and_source_interfaces, HumanCompileOptions,
    };
    use npa_package::{
        refresh_targeted_authoring_support_context_entry, targeted_authoring_module_identity,
        PackageCacheNamespaceDigest, PackageModuleIdentity,
        TargetedAuthoringAcceptedCertificateIdentity, TargetedAuthoringCertificateImportIdentity,
        TargetedAuthoringSupportKeyInput, TargetedAuthoringToolchainIdentity,
        PACKAGE_TARGETED_AUTHORING_LIVE_CLOSURE_CLAIM, PACKAGE_TARGETED_AUTHORING_POLICY,
        PACKAGE_TARGETED_AUTHORING_SUPPORT_CONTEXT_SCHEMA,
        PACKAGE_TARGETED_AUTHORING_SUPPORT_TRUST_BOUNDARY,
    };

    use super::*;

    const SOURCE: &str = "\
axiom A : Type
axiom a : A
def polymorphic_id.{u} {T : Sort u} (x : T) : T := x
def choose (x y : A) : A := x
infixl:65 \" ++ \" => choose
inductive Choice : Type where
| pick : Choice
class Boxed (T : Type) where
  value : T
instance boxed_a : Boxed A where
  value := a";

    fn hash(value: u8) -> PackageHash {
        PackageHash::new([value; 32])
    }

    #[test]
    fn package_build_cache_security_publication_predicate_is_closed() {
        for origin in [
            TargetedAuthoringPublicationOrigin::TargetedReadThroughSupport,
            TargetedAuthoringPublicationOrigin::TargetedLocalHitSupport,
            TargetedAuthoringPublicationOrigin::FullReadThroughRetainedModule,
        ] {
            assert!(origin.is_allowed());
        }
        for origin in [
            TargetedAuthoringPublicationOrigin::ExplicitTarget,
            TargetedAuthoringPublicationOrigin::PostTargetSupport,
            TargetedAuthoringPublicationOrigin::FullReadThroughUnretainedModule,
        ] {
            assert!(!origin.is_allowed());
            assert_eq!(
                validate_targeted_authoring_publication_gate(
                    origin,
                    false,
                    TargetedAuthoringModuleAcceptance::checked_certificate_complete(),
                    HUMAN_SOURCE_PRODUCER_PROFILE,
                ),
                Err("writer_origin_ineligible")
            );
        }

        let checked = TargetedAuthoringModuleAcceptance::checked_certificate_complete();
        assert!(checked.is_complete());
        assert_eq!(
            validate_targeted_authoring_publication_gate(
                TargetedAuthoringPublicationOrigin::TargetedLocalHitSupport,
                true,
                checked,
                HUMAN_SOURCE_PRODUCER_PROFILE,
            ),
            Err("closure_used_cached_context")
        );
        for profile in [
            STD_PACKAGE_PRODUCER_PROFILE,
            LEGACY_STD_PACKAGE_PRODUCER_PROFILE,
            "unsupported-profile",
        ] {
            assert_eq!(
                validate_targeted_authoring_publication_gate(
                    TargetedAuthoringPublicationOrigin::TargetedReadThroughSupport,
                    false,
                    checked,
                    profile,
                ),
                Err("unsupported_producer_profile")
            );
        }
        for requirement in [
            TargetedAuthoringModuleAcceptance::SOURCE_PIN,
            TargetedAuthoringModuleAcceptance::CERTIFICATE_PIN,
            TargetedAuthoringModuleAcceptance::AXIOM_POLICY,
            TargetedAuthoringModuleAcceptance::LIVE_VERIFICATION,
            TargetedAuthoringModuleAcceptance::MODULE_AND_IMPORT_TABLE,
            TargetedAuthoringModuleAcceptance::INTERFACE_DRIFT,
            TargetedAuthoringModuleAcceptance::INTERFACE_RECONSTRUCTION,
        ] {
            let incomplete = TargetedAuthoringModuleAcceptance {
                completed: checked.completed & !requirement,
                ..checked
            };
            assert!(!incomplete.is_complete());
            assert_eq!(
                validate_targeted_authoring_publication_gate(
                    TargetedAuthoringPublicationOrigin::TargetedReadThroughSupport,
                    false,
                    incomplete,
                    HUMAN_SOURCE_PRODUCER_PROFILE,
                ),
                Err("module_acceptance_incomplete")
            );
        }

        let full = TargetedAuthoringModuleAcceptance::full_source_complete();
        assert!(full.is_complete());
        for requirement in [
            TargetedAuthoringModuleAcceptance::SOURCE_PIN,
            TargetedAuthoringModuleAcceptance::CERTIFICATE_PIN,
            TargetedAuthoringModuleAcceptance::AXIOM_POLICY,
            TargetedAuthoringModuleAcceptance::LIVE_VERIFICATION,
            TargetedAuthoringModuleAcceptance::MODULE_AND_IMPORT_TABLE,
            TargetedAuthoringModuleAcceptance::INTERFACE_DRIFT,
            TargetedAuthoringModuleAcceptance::INTERFACE_RECONSTRUCTION,
            TargetedAuthoringModuleAcceptance::OBSERVABLE_IMPORTS,
            TargetedAuthoringModuleAcceptance::GENERATED_MANIFEST_HASHES,
            TargetedAuthoringModuleAcceptance::CHECKED_IN_CERTIFICATE_BYTES,
        ] {
            let incomplete = TargetedAuthoringModuleAcceptance {
                completed: full.completed & !requirement,
                ..full
            };
            assert!(!incomplete.is_complete());
            assert_eq!(
                validate_targeted_authoring_publication_gate(
                    TargetedAuthoringPublicationOrigin::FullReadThroughRetainedModule,
                    false,
                    incomplete,
                    HUMAN_SOURCE_PRODUCER_PROFILE,
                ),
                Err("module_acceptance_incomplete")
            );
        }
    }

    #[test]
    fn package_build_cache_security_current_snapshot_survives_source_and_certificate_replacement() {
        let root = std::env::temp_dir().join(format!(
            "npa-targeted-authoring-snapshot-security-{}",
            std::process::id()
        ));
        if root.exists() {
            std::fs::remove_dir_all(&root).unwrap();
        }
        std::fs::create_dir_all(&root).unwrap();
        let source_path = root.join("source.npa");
        let certificate_path = root.join("certificate.npcert");
        std::fs::write(&source_path, b"original source").unwrap();
        std::fs::write(&certificate_path, b"original certificate").unwrap();
        let snapshot = TargetedAuthoringCurrentSnapshot::new(
            std::fs::read_to_string(&source_path).unwrap(),
            std::fs::read(&certificate_path).unwrap(),
        );

        let replacement_source = root.join("replacement-source.npa");
        let replacement_certificate = root.join("replacement-certificate.npcert");
        std::fs::write(&replacement_source, b"replacement source").unwrap();
        std::fs::write(&replacement_certificate, b"replacement certificate").unwrap();
        std::fs::remove_file(&source_path).unwrap();
        std::fs::remove_file(&certificate_path).unwrap();
        std::fs::rename(replacement_source, &source_path).unwrap();
        std::fs::rename(replacement_certificate, &certificate_path).unwrap();

        let (source, certificate_bytes) = snapshot.into_parts();
        assert_eq!(source, "original source");
        assert_eq!(certificate_bytes, b"original certificate");
        assert_eq!(
            std::fs::read_to_string(source_path).unwrap(),
            "replacement source"
        );
        assert_eq!(
            std::fs::read(certificate_path).unwrap(),
            b"replacement certificate"
        );
        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn targeted_authoring_diagnostics_hide_publication_collision_details_without_detailed_mode() {
        let mut summary_planner = TargetedAuthoringSupportPublicationPlanner::new(
            None,
            None,
            Vec::new(),
            &AxiomPolicy::normal(),
            false,
        );
        summary_planner.record_publish_outcome(
            0,
            TargetedAuthoringSupportContextPublishOutcome::Conflict(
                TargetedAuthoringSupportContextWriterValidation::Stale,
            ),
        );
        assert!(summary_planner.take_diagnostics().is_empty());
    }

    #[test]
    fn package_build_cache_security_detailed_diagnostics_stop_at_the_fixed_limit() {
        let mut planner = TargetedAuthoringSupportPublicationPlanner::new(
            None,
            None,
            Vec::new(),
            &AxiomPolicy::normal(),
            true,
        );
        for module_index in 0..=TARGETED_AUTHORING_CACHE_LIMITS_V1.detailed_diagnostics {
            planner.record_publish_outcome(
                module_index,
                TargetedAuthoringSupportContextPublishOutcome::Invalid,
            );
        }

        let diagnostics = planner.take_diagnostics();
        assert_eq!(
            diagnostics.len(),
            TARGETED_AUTHORING_CACHE_LIMITS_V1.detailed_diagnostics
        );
        assert_eq!(
            diagnostics.last().unwrap().path.as_deref(),
            Some(
                format!(
                    "modules[{}]",
                    TARGETED_AUTHORING_CACHE_LIMITS_V1.detailed_diagnostics - 1
                )
                .as_str()
            )
        );
    }

    #[test]
    fn targeted_authoring_publication_outcomes_count_only_destination_winner() {
        let mut planner = TargetedAuthoringSupportPublicationPlanner::new(
            None,
            None,
            Vec::new(),
            &AxiomPolicy::normal(),
            true,
        );
        planner.record_publish_outcome(
            0,
            TargetedAuthoringSupportContextPublishOutcome::ExistingEqual,
        );
        planner.record_publish_outcome(
            1,
            TargetedAuthoringSupportContextPublishOutcome::Conflict(
                TargetedAuthoringSupportContextWriterValidation::Stale,
            ),
        );
        assert_eq!(planner.entries_written(), 0);
        assert_eq!(planner.take_diagnostics().len(), 1);

        planner.record_publish_outcome(2, TargetedAuthoringSupportContextPublishOutcome::Published);
        assert_eq!(planner.entries_written(), 1);
    }

    fn planner_input(
        topological_order: &[usize],
        local_dependencies: &[&[usize]],
        producer_profiles: &[&str],
        selected_targets: &[usize],
        selected_support: &[usize],
        external_order: &[usize],
        external_module_count: usize,
    ) -> TargetedAuthoringPlannerInput {
        TargetedAuthoringPlannerInput {
            combined_topological_order: topological_order.to_vec(),
            local_dependencies: local_dependencies
                .iter()
                .enumerate()
                .map(|(index, dependencies)| (index, dependencies.to_vec()))
                .collect(),
            producer_profiles: producer_profiles
                .iter()
                .enumerate()
                .map(|(index, profile)| {
                    (
                        index,
                        TargetedAuthoringProducerProfile::classify(Some(profile)),
                    )
                })
                .collect(),
            selected_targets: selected_targets.iter().copied().collect(),
            selected_support: selected_support.iter().copied().collect(),
            external_order: external_order.to_vec(),
            local_module_count: local_dependencies.len(),
            external_module_count,
        }
    }

    fn simple_authoring_execution_plan() -> TargetedAuthoringExecutionPlan {
        build_targeted_authoring_execution_plan(planner_input(
            &[0, 1],
            &[&[], &[0]],
            &[HUMAN_SOURCE_PRODUCER_PROFILE, HUMAN_SOURCE_PRODUCER_PROFILE],
            &[1],
            &[0],
            &[],
            0,
        ))
        .unwrap()
    }

    #[test]
    fn current_and_legacy_std_profiles_share_the_core_builder_classification() {
        for profile in [
            STD_PACKAGE_PRODUCER_PROFILE,
            LEGACY_STD_PACKAGE_PRODUCER_PROFILE,
        ] {
            assert_eq!(
                TargetedAuthoringProducerProfile::classify(Some(profile)),
                TargetedAuthoringProducerProfile::StdCoreBuilder
            );
        }
    }

    #[test]
    fn targeted_authoring_diagnostics_local_only_result_state_validates_once_at_projection() {
        let selection = CommandDiagnostic::info(DiagnosticKind::Build, "package_build_selection");
        let result = run_targeted_authoring_local_hit(
            "package build-certs",
            ".".to_owned(),
            selection,
            TargetedAuthoringCheckPlan::new(1, 1, 0),
            false,
            false,
            || Ok(simple_authoring_execution_plan()),
            |_, run| {
                run.record_live_support_visit(0);
                run.record_lookup_miss(0, TargetedAuthoringLookupMiss::Missing);
                run.record_live_support_completion(0).unwrap();
                run.record_target_attempt(1, false).unwrap();
                run.record_target_completion();
                TargetedAuthoringExecutionOutcome::completed(None)
            },
        )
        .into_parts()
        .0;

        assert_eq!(
            result.exit_code(),
            crate::diagnostic::CommandExitCode::Success
        );
        assert_eq!(result.diagnostics.len(), 3);
        assert_eq!(
            result.diagnostics[1].reason_code,
            "targeted_authoring_cache_summary"
        );
        assert_eq!(
            result.diagnostics[2].reason_code,
            TARGETED_AUTHORING_LOCAL_ONLY_REASON
        );
        assert_eq!(
            result.diagnostics[2].actual_value.as_deref(),
            Some(
                "trusted=false;build_evidence=false;proof_evidence=false;locally_accelerated=false"
            )
        );

        let invalid = run_targeted_authoring_local_hit(
            "package build-certs",
            ".".to_owned(),
            CommandDiagnostic::info(DiagnosticKind::Build, "package_build_selection"),
            TargetedAuthoringCheckPlan::new(1, 1, 0),
            false,
            false,
            || Ok(simple_authoring_execution_plan()),
            |_, run| {
                run.record_target_attempt(1, false).unwrap();
                TargetedAuthoringExecutionOutcome::completed(None)
            },
        )
        .into_parts()
        .0;
        assert_eq!(
            invalid.exit_code(),
            crate::diagnostic::CommandExitCode::UsageOrInternal
        );
        assert_eq!(
            invalid.diagnostics.last().unwrap().reason_code,
            "targeted_authoring_result_invalid"
        );
        assert_eq!(
            invalid
                .diagnostics
                .iter()
                .filter(|diagnostic| {
                    diagnostic.reason_code == TARGETED_AUTHORING_LOCAL_ONLY_REASON
                })
                .count(),
            1
        );
    }

    #[test]
    fn targeted_authoring_summary_completed_equations_and_early_stop_are_honest() {
        let completed = TargetedAuthoringCheckSummary {
            plan: TargetedAuthoringCheckPlan {
                selected_targets: 1,
                selected_support: 3,
                selected_external: 2,
                forced_live_support: 1,
                forced_live_targets: 1,
                count_overflowed: false,
            },
            run: TargetedAuthoringCheckRunState {
                visited_support: 3,
                visited_targets: 1,
                visited_external: 2,
                completed_support: 3,
                completed_targets: 1,
                completed_external: 2,
                target_attempts: 1,
                target_fresh_builds: 1,
                targets_forced_live: 1,
                context_hits: 1,
                context_bypassed_hits: 1,
                context_misses: 0,
                context_ineligible: 1,
                live_support_checks: 2,
                avoided_kernel_checks: 1,
                avoided_source_interface_resolutions: 1,
                ..TargetedAuthoringCheckRunState::default()
            },
            completed: true,
        };
        assert_eq!(
            completed.validate(TargetedAuthoringProvenance {
                locally_accelerated: true,
                ..TargetedAuthoringProvenance::LOCAL_ONLY
            }),
            Ok(())
        );

        let early_stop = TargetedAuthoringCheckSummary {
            plan: completed.plan,
            run: TargetedAuthoringCheckRunState {
                visited_support: 1,
                ..TargetedAuthoringCheckRunState::default()
            },
            completed: false,
        };
        assert_eq!(
            early_stop.validate(TargetedAuthoringProvenance::LOCAL_ONLY),
            Ok(())
        );
        assert_eq!(
            early_stop
                .diagnostic(TargetedAuthoringProvenance::LOCAL_ONLY)
                .actual_value
                .as_deref(),
            Some(
                "mode=local-hit;complete=false;support_selected=3;targets_selected=1;external_selected=2;forced_live_support=1;targets_forced_live=0;visited_support=1;visited_targets=0;visited_external=0;context_hits=0;context_bypassed_hits=0;context_misses=0;context_stale=0;context_schema_misses=0;context_invalid=0;context_ineligible=0;live_prerequisite_checks=0;avoided_kernel_checks=0;avoided_source_interface_resolutions=0;target_fresh_builds=0;entries_written=0;bytes_loaded=0;bytes_written=0;trusted=false;build_evidence=false;proof_evidence=false"
            )
        );

        let fabricated_completion = TargetedAuthoringCheckSummary {
            completed: true,
            ..early_stop
        };
        assert_eq!(
            fabricated_completion.validate(TargetedAuthoringProvenance::LOCAL_ONLY),
            Err("completed_visit_count_inconsistent")
        );
    }

    #[test]
    fn targeted_authoring_summary_completed_equations_hold_for_small_outcome_partitions() {
        for selected_support in 0_u64..=5 {
            for context_hits in 0..=selected_support {
                for context_bypassed_hits in 0..=selected_support - context_hits {
                    for context_misses in
                        0..=selected_support - context_hits - context_bypassed_hits
                    {
                        let context_ineligible = selected_support
                            - context_hits
                            - context_bypassed_hits
                            - context_misses;
                        let live_support_checks =
                            context_bypassed_hits + context_misses + context_ineligible;
                        let summary = TargetedAuthoringCheckSummary {
                            plan: TargetedAuthoringCheckPlan {
                                selected_targets: 0,
                                selected_support,
                                selected_external: 0,
                                forced_live_support: 0,
                                forced_live_targets: 0,
                                count_overflowed: false,
                            },
                            run: TargetedAuthoringCheckRunState {
                                visited_support: selected_support,
                                completed_support: selected_support,
                                context_hits,
                                context_bypassed_hits,
                                context_misses,
                                context_ineligible,
                                live_support_checks,
                                avoided_kernel_checks: context_hits,
                                avoided_source_interface_resolutions: context_hits,
                                ..TargetedAuthoringCheckRunState::default()
                            },
                            completed: true,
                        };
                        let provenance = TargetedAuthoringProvenance {
                            locally_accelerated: context_hits > 0,
                            ..TargetedAuthoringProvenance::LOCAL_ONLY
                        };
                        assert_eq!(summary.validate(provenance), Ok(()));

                        let invalid = TargetedAuthoringCheckSummary {
                            run: TargetedAuthoringCheckRunState {
                                live_support_checks: live_support_checks.saturating_add(1),
                                ..summary.run
                            },
                            ..summary
                        };
                        assert!(invalid.validate(provenance).is_err());
                    }
                }
            }
        }
    }

    #[test]
    fn targeted_authoring_diagnostics_are_bounded_private_and_stable() {
        let summary = TargetedAuthoringCheckSummary {
            plan: TargetedAuthoringCheckPlan::new(1, 1, 0),
            run: TargetedAuthoringCheckRunState {
                visited_support: 1,
                context_misses: 1,
                context_invalid: 1,
                ..TargetedAuthoringCheckRunState::default()
            },
            completed: false,
        }
        .diagnostic(TargetedAuthoringProvenance::LOCAL_ONLY);
        let value = summary.actual_value.as_deref().unwrap();
        assert!(value.starts_with("mode=local-hit;complete=false;support_selected=1"));
        for forbidden in [
            "/Users/",
            "source=",
            "proof=",
            "certificate_bytes",
            "cache_key=",
        ] {
            assert!(
                !value.contains(forbidden),
                "leaked forbidden detail: {forbidden}"
            );
        }

        let collision = CommandDiagnostic::info(
            DiagnosticKind::GeneratedArtifact,
            "targeted_authoring_cache_entry_invalid",
        )
        .with_path("modules[0]")
        .with_field("targeted_authoring_cache")
        .with_actual_value("operation=publication_collision");
        assert_eq!(
            collision.actual_value.as_deref(),
            Some("operation=publication_collision")
        );
        assert!(
            collision.actual_value.as_deref().unwrap().len()
                <= TARGETED_AUTHORING_CACHE_LIMITS_V1.diagnostic_value_bytes
        );
    }

    #[test]
    fn targeted_authoring_summary_measurements_keep_mode_specific_labels_separate() {
        let mut local_recorder =
            PerformanceMeasurementRecorder::new(npa_api::PerformanceMeasurementMode::Summary);
        TargetedAuthoringMeasurementSnapshot {
            support_selected: 4,
            targets_forced_live: 1,
            context_hits: 2,
            context_bypassed_hits: 1,
            context_misses: 1,
            live_prerequisite_checks: 2,
            avoided_kernel_checks: 2,
            avoided_source_interface_resolutions: 2,
            target_fresh_builds: 1,
            tool_identity_attempted: true,
            tool_identity_bytes: 17,
            tool_identity_elapsed_ns: 19,
            current_byte_validation_elapsed_ns: 23,
            reconstruction_elapsed_ns: 29,
            live_support_elapsed_ns: 31,
            source_interface_resolution_elapsed_ns: 7,
            fresh_target_elapsed_ns: 37,
            bytes_loaded: 41,
            bytes_written: 43,
            cache_lookup_ms: 5,
            local_hit_outcomes: true,
            ..TargetedAuthoringMeasurementSnapshot::default()
        }
        .record(&mut local_recorder);
        let local = local_recorder.report().unwrap();
        let local_labels = local
            .counters
            .iter()
            .map(|counter| counter.label)
            .collect::<BTreeSet<_>>();
        assert!(local_labels.contains(&PerformanceMeasurementLabel::CacheContextHits));
        assert!(local_labels.contains(&PerformanceMeasurementLabel::CacheToolIdentityBytes));
        assert!(
            local_labels.contains(&PerformanceMeasurementLabel::CacheCurrentByteValidationElapsed)
        );

        let mut read_through_recorder =
            PerformanceMeasurementRecorder::new(npa_api::PerformanceMeasurementMode::Summary);
        let read_through =
            TargetedAuthoringMeasurementSnapshot::read_through(4, 4, 1, 31, 7, 37, 41, 43);
        assert_eq!(read_through.cache_lookup_ms(), 0);
        read_through.record(&mut read_through_recorder);
        let read_through_labels = read_through_recorder
            .report()
            .unwrap()
            .counters
            .iter()
            .map(|counter| counter.label)
            .collect::<BTreeSet<_>>();
        assert!(read_through_labels.contains(&PerformanceMeasurementLabel::CacheSupportSelected));
        assert!(
            read_through_labels.contains(&PerformanceMeasurementLabel::CacheLivePrerequisiteChecks)
        );
        assert!(!read_through_labels.contains(&PerformanceMeasurementLabel::CacheContextHits));
        assert!(!read_through_labels
            .contains(&PerformanceMeasurementLabel::CacheCurrentByteValidationElapsed));
        assert!(!read_through_labels.contains(&PerformanceMeasurementLabel::CacheTargetsForcedLive));

        let mut off = TargetedAuthoringCheckRun::new(TargetedAuthoringCheckPlan::new(0, 0, 0));
        assert_eq!(off.time_current_byte_validation(|| 11), 11);
        assert_eq!(
            off.state.durations,
            TargetedAuthoringDurationTotals::default()
        );
    }

    #[test]
    fn targeted_authoring_differential_plan_partitions_chain_diamond_branch_and_multiple_targets() {
        struct Case {
            topological_order: &'static [usize],
            dependencies: &'static [&'static [usize]],
            targets: &'static [usize],
            support: &'static [usize],
            expected_pre: &'static [usize],
            expected_targets: &'static [usize],
            expected_uses: &'static [(usize, u64)],
        }
        let cases = [
            Case {
                topological_order: &[0, 1, 2],
                dependencies: &[&[], &[0], &[1]],
                targets: &[2],
                support: &[0, 1],
                expected_pre: &[0, 1],
                expected_targets: &[2],
                expected_uses: &[(0, 2), (1, 1)],
            },
            Case {
                topological_order: &[0, 1, 2, 3],
                dependencies: &[&[], &[0], &[0], &[1, 2]],
                targets: &[3],
                support: &[0, 1, 2],
                expected_pre: &[0, 1, 2],
                expected_targets: &[3],
                expected_uses: &[(0, 3), (1, 1), (2, 1)],
            },
            Case {
                topological_order: &[0, 1, 2, 3],
                dependencies: &[&[], &[0], &[1], &[0]],
                targets: &[2, 3],
                support: &[0, 1],
                expected_pre: &[0, 1],
                expected_targets: &[2, 3],
                expected_uses: &[(0, 3), (1, 1)],
            },
        ];

        for case in cases {
            let profiles = vec![HUMAN_SOURCE_PRODUCER_PROFILE; case.dependencies.len()];
            let plan = build_targeted_authoring_execution_plan(planner_input(
                case.topological_order,
                case.dependencies,
                &profiles,
                case.targets,
                case.support,
                &[2, 0, 1],
                3,
            ))
            .unwrap();

            assert_eq!(plan.combined_local_order, case.topological_order);
            assert_eq!(plan.pre_target_support, case.expected_pre);
            assert_eq!(plan.explicit_targets, case.expected_targets);
            assert!(plan.post_target_support.is_empty());
            assert_eq!(plan.external_order, [2, 0, 1]);
            assert_eq!(
                plan.remaining_local_uses,
                case.expected_uses.iter().copied().collect()
            );
            assert!(plan.force_live_local.is_empty());
            assert_eq!(plan.eligible_support_lookup, case.expected_pre);
            assert!(plan.requests_support_store());
        }
    }

    #[test]
    fn targeted_authoring_differential_forced_live_closure_distinguishes_post_legacy_and_profiles()
    {
        let post_and_legacy = build_targeted_authoring_execution_plan(planner_input(
            &[0, 5, 1, 2, 3, 4],
            &[&[], &[0], &[1], &[2], &[5], &[]],
            &[
                HUMAN_SOURCE_PRODUCER_PROFILE,
                HUMAN_SOURCE_PRODUCER_PROFILE,
                HUMAN_SOURCE_PRODUCER_PROFILE,
                HUMAN_SOURCE_PRODUCER_PROFILE,
                LEGACY_STD_PACKAGE_PRODUCER_PROFILE,
                HUMAN_SOURCE_PRODUCER_PROFILE,
            ],
            &[1, 3, 4],
            &[0, 2, 5],
            &[],
            0,
        ))
        .unwrap();
        assert_eq!(post_and_legacy.pre_target_support, [0, 5]);
        assert_eq!(post_and_legacy.post_target_support, [2]);
        assert_eq!(post_and_legacy.forced_live_support, [0, 2, 5].into());
        assert_eq!(post_and_legacy.forced_live_targets, [1, 4].into());
        assert!(post_and_legacy.eligible_support_lookup.is_empty());
        assert_eq!(
            post_and_legacy.initial_roles[&0].forced_live_reason(),
            Some(TargetedAuthoringForcedLiveReason::PostTargetSupportRequiresLiveOrder)
        );
        assert_eq!(
            post_and_legacy.initial_roles[&0]
                .forced_live_reason()
                .unwrap()
                .as_str(),
            "post_target_support_requires_live_order"
        );
        assert_eq!(
            post_and_legacy.initial_roles[&5].forced_live_reason(),
            Some(TargetedAuthoringForcedLiveReason::CoreBuilderConsumerRequiresLive)
        );
        assert_eq!(
            post_and_legacy.initial_roles[&5]
                .forced_live_reason()
                .unwrap()
                .as_str(),
            "core_builder_consumer_requires_live"
        );
        assert_eq!(
            post_and_legacy.initial_roles[&4].forced_live_reason(),
            Some(TargetedAuthoringForcedLiveReason::ProducerProfile)
        );
        assert_eq!(
            post_and_legacy.initial_roles[&4]
                .forced_live_reason()
                .unwrap()
                .as_str(),
            "producer_profile"
        );

        let predecessor_target = build_targeted_authoring_execution_plan(planner_input(
            &[0, 1, 2],
            &[&[], &[0], &[1]],
            &[
                HUMAN_SOURCE_PRODUCER_PROFILE,
                HUMAN_SOURCE_PRODUCER_PROFILE,
                LEGACY_STD_PACKAGE_PRODUCER_PROFILE,
            ],
            &[1, 2],
            &[0],
            &[],
            0,
        ))
        .unwrap();
        assert_eq!(predecessor_target.forced_live_support, [0].into());
        assert_eq!(predecessor_target.forced_live_targets, [1, 2].into());
        assert_eq!(
            predecessor_target.initial_roles[&1].forced_live_reason(),
            Some(TargetedAuthoringForcedLiveReason::CoreBuilderConsumerRequiresLive)
        );

        let mixed_profile = build_targeted_authoring_execution_plan(planner_input(
            &[0, 1, 2],
            &[&[], &[0], &[1]],
            &[
                HUMAN_SOURCE_PRODUCER_PROFILE,
                "unsupported-fixture-profile",
                HUMAN_SOURCE_PRODUCER_PROFILE,
            ],
            &[2],
            &[0, 1],
            &[],
            0,
        ))
        .unwrap();
        assert_eq!(mixed_profile.forced_live_support, [0, 1].into());
        assert_eq!(
            mixed_profile.initial_roles[&1].forced_live_reason(),
            Some(TargetedAuthoringForcedLiveReason::ProducerProfile)
        );
        assert!(!mixed_profile.requests_support_store());
    }

    #[test]
    fn targeted_authoring_differential_plan_empty_external_and_forced_cases_skip_support_store() {
        let empty = build_targeted_authoring_execution_plan(planner_input(
            &[],
            &[],
            &[],
            &[],
            &[],
            &[2, 0, 1],
            3,
        ))
        .unwrap();
        assert!(empty.combined_local_order.is_empty());
        assert_eq!(empty.external_order, [2, 0, 1]);
        assert!(!empty.requests_support_store());

        let no_local_support = build_targeted_authoring_execution_plan(planner_input(
            &[0],
            &[&[]],
            &[HUMAN_SOURCE_PRODUCER_PROFILE],
            &[0],
            &[],
            &[1, 0],
            2,
        ))
        .unwrap();
        assert_eq!(no_local_support.explicit_targets, [0]);
        assert!(no_local_support.remaining_local_uses.is_empty());
        assert!(!no_local_support.requests_support_store());

        let entirely_forced = build_targeted_authoring_execution_plan(planner_input(
            &[0, 1],
            &[&[], &[0]],
            &[HUMAN_SOURCE_PRODUCER_PROFILE, "unsupported-fixture-profile"],
            &[1],
            &[0],
            &[],
            0,
        ))
        .unwrap();
        assert_eq!(entirely_forced.forced_live_support, [0].into());
        assert_eq!(entirely_forced.forced_live_targets, [1].into());
        assert!(!entirely_forced.requests_support_store());
    }

    #[test]
    fn targeted_authoring_plan_rejects_graph_inconsistency_before_execution() {
        let error = build_targeted_authoring_execution_plan(planner_input(
            &[0, 1],
            &[&[], &[2]],
            &[HUMAN_SOURCE_PRODUCER_PROFILE, HUMAN_SOURCE_PRODUCER_PROFILE],
            &[1],
            &[0],
            &[],
            0,
        ))
        .unwrap_err();
        assert_eq!(error.reason_code, "targeted_authoring_plan_invalid");
        assert_eq!(error.field.as_deref(), Some("plan"));
        assert_eq!(
            error.actual_value.as_deref(),
            Some("local_dependency_inconsistent")
        );
    }

    #[test]
    fn targeted_authoring_plan_bounds_local_and_external_identities_together() {
        let limit = TARGETED_AUTHORING_CACHE_LIMITS_V1.closure_modules;
        let error = build_targeted_authoring_execution_plan(TargetedAuthoringPlannerInput {
            combined_topological_order: (0..limit).collect(),
            local_dependencies: (0..limit).map(|index| (index, Vec::new())).collect(),
            producer_profiles: (0..limit)
                .map(|index| (index, TargetedAuthoringProducerProfile::HumanSurface))
                .collect(),
            selected_targets: (0..limit).collect(),
            selected_support: BTreeSet::new(),
            external_order: vec![0],
            local_module_count: limit,
            external_module_count: 1,
        })
        .unwrap_err();

        assert_eq!(error.reason_code, "targeted_authoring_plan_invalid");
        assert_eq!(
            error.actual_value.as_deref(),
            Some("selected_identity_out_of_bounds")
        );
    }

    #[test]
    fn targeted_authoring_import_context_wraps_live_origin_without_reverse_projection() {
        let (_, verified, _) = compile_fixture(FileId(900));
        let session = TargetedAuthoringBuildSession::new();
        let context = session.register_live_support(&verified);

        assert!(!context.closure_used_cached_context());
        let import = context.authoring_import().unwrap();
        assert_eq!(import.module(), &Name::from_dotted("Fixture.Adapter"));
    }

    fn compile_fixture(
        file_id: FileId,
    ) -> (ModuleCert, VerifiedModule, HumanImportedSourceInterface) {
        let module = Name::from_dotted("Fixture.Adapter");
        let output =
            compile_human_source_to_certificate_output_with_source_interfaces_and_axiom_policy(
                file_id,
                module.clone(),
                SOURCE,
                &[],
                &[],
                &HumanCompileOptions::default(),
                &AxiomPolicy::normal(),
            )
            .expect("fixture should compile");
        let interface = HumanImportedSourceInterface {
            module,
            export_hash: output.certificate.hashes().export_hash,
            certificate_hash: Some(output.certificate.hashes().certificate_hash),
            source_interface: output.source_interface,
        };
        (output.certificate, output.verified_module, interface)
    }

    fn support_entry(
        certificate: &ModuleCert,
        dto: TargetedAuthoringHumanImportedSourceInterface,
        direct_imports: Vec<ResolvedModuleImportIdentity>,
        profile: TargetedAuthoringInterfaceProfile,
    ) -> TargetedAuthoringSupportContextEntry {
        let certificate_bytes = encode_module_cert(certificate).unwrap();
        let namespace = PackageCacheNamespaceDigest::parse(&"1".repeat(64)).unwrap();
        let key_input = TargetedAuthoringSupportKeyInput {
            toolchain: TargetedAuthoringToolchainIdentity {
                executable_hash: hash(1),
                cli_authoring_abi: "npa.cli.targeted_authoring_abi.v1".to_owned(),
                frontend_authoring_abi: "npa.frontend.human_authoring_interface_abi.v2".to_owned(),
                producer_authoring_abi: "npa.cert.local_authoring_producer_abi.v1".to_owned(),
                kernel_authoring_abi: "npa.kernel.local_authoring_context_abi.v1".to_owned(),
            },
            package: dto.source.package.clone(),
            version: dto.source.version.clone(),
            core_spec: "npa.core.v0.1".to_owned(),
            kernel_profile: "npa.kernel.v0.1".to_owned(),
            certificate_format: "npa.certificate.canonical.v0.1".to_owned(),
            checker_profile: "npa.checker.reference.v0.1".to_owned(),
            producer_profile: dto.producer_profile.clone(),
            semantic_compiler_options: vec!["frontend=human".to_owned()],
            axiom_policy_hash: hash(2),
            module: dto.module.clone(),
            module_identity: targeted_authoring_module_identity(&PackageModuleIdentity {
                package: dto.source.package.clone(),
                version: dto.source.version.clone(),
                module: dto.module.clone(),
            }),
            current_source_hash: dto.source.source_hash,
            expected_source_hash: dto.source.source_hash,
            current_certificate_file_hash: package_file_hash(&certificate_bytes),
            expected_certificate_file_hash: package_file_hash(&certificate_bytes),
            expected_export_hash: dto.export_hash,
            expected_axiom_report_hash: PackageHash::from(certificate.hashes().axiom_report_hash),
            expected_certificate_hash: dto.certificate_hash,
            actual_export_hash: dto.export_hash,
            actual_axiom_report_hash: PackageHash::from(certificate.hashes().axiom_report_hash),
            actual_certificate_hash: dto.certificate_hash,
            certificate_imports: certificate
                .imports()
                .iter()
                .map(|import| TargetedAuthoringCertificateImportIdentity {
                    module: import.module.clone(),
                    export_hash: PackageHash::from(import.export_hash),
                    certificate_hash: import.certificate_hash.map(PackageHash::from),
                })
                .collect(),
            dependency_closure_commitment: hash(3),
            manifest_human_imports: direct_imports,
            source_interface_schema: PACKAGE_TARGETED_AUTHORING_HUMAN_INTERFACE_SCHEMA.to_owned(),
            source_interface_reconstruction_version: "npa.cli.human_interface_adapter.v1"
                .to_owned(),
        };
        refresh_targeted_authoring_support_context_entry(&TargetedAuthoringSupportContextEntry {
            schema: PACKAGE_TARGETED_AUTHORING_SUPPORT_CONTEXT_SCHEMA.to_owned(),
            cache_key: String::new(),
            namespace,
            closure_commitment: key_input.dependency_closure_commitment,
            producer_profile: key_input.producer_profile.clone(),
            interface_profile: profile,
            authoring_policy: PACKAGE_TARGETED_AUTHORING_POLICY.to_owned(),
            accepted_certificate: TargetedAuthoringAcceptedCertificateIdentity {
                module: dto.module.clone(),
                certificate_file_hash: key_input.current_certificate_file_hash,
                export_hash: dto.export_hash,
                axiom_report_hash: key_input.actual_axiom_report_hash,
                certificate_hash: dto.certificate_hash,
            },
            source_interface: dto,
            key_input,
            integrity_digest: hash(0),
            trusted: false,
            build_evidence: false,
            proof_evidence: false,
            live_closure_eligibility: PACKAGE_TARGETED_AUTHORING_LIVE_CLOSURE_CLAIM.to_owned(),
            trust_boundary: PACKAGE_TARGETED_AUTHORING_SUPPORT_TRUST_BOUNDARY.to_owned(),
        })
        .expect("fixture entry should validate")
    }

    fn pending_cached_fixture(module_index: usize) -> PendingCachedTargetedSupportContext {
        let (certificate, verified, interface) = compile_fixture(FileId(module_index as u32));
        let certificate_bytes = encode_module_cert(&certificate).unwrap();
        let package = PackageId::new("fixture-package");
        let version = PackageVersion::new("0.1.0");
        let authoring = HumanAuthoringImport::from_verified_module(&verified);
        let adapter = HumanInterfaceCacheAdapterContext::new(
            &package,
            &version,
            HUMAN_SOURCE_PRODUCER_PROFILE,
            &[],
            module_index,
            SOURCE,
            &authoring,
        );
        let dto = human_interface_to_cache_dto(&interface, &adapter).unwrap();
        let policy = AxiomPolicy::normal();
        let mut entry = support_entry(
            &certificate,
            dto,
            Vec::new(),
            TargetedAuthoringInterfaceProfile::HumanSource,
        );
        entry.key_input.axiom_policy_hash = PackageHash::from(policy.policy_hash());
        entry.key_input.certificate_format = certificate.header().format.clone();
        entry.key_input.core_spec = certificate.header().core_spec.clone();
        entry = refresh_targeted_authoring_support_context_entry(&entry).unwrap();
        let snapshot = TargetedAuthoringCurrentSnapshot::new(SOURCE.to_owned(), certificate_bytes);
        let retained_bytes = snapshot.loaded_bytes().unwrap();
        let (pending, source_interface) = reconstruct_pending_cached_support(
            &entry,
            &snapshot,
            module_index,
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &policy,
        )
        .unwrap();
        PendingCachedTargetedSupportContext {
            pending,
            source_interface,
            snapshot,
            retained_bytes,
        }
    }

    #[test]
    fn targeted_authoring_differential_miss_promotion_bypasses_leaf_hit_before_consumer_live_load()
    {
        let execution_plan = build_targeted_authoring_execution_plan(planner_input(
            &[0, 1, 2],
            &[&[], &[0], &[1]],
            &[
                HUMAN_SOURCE_PRODUCER_PROFILE,
                HUMAN_SOURCE_PRODUCER_PROFILE,
                HUMAN_SOURCE_PRODUCER_PROFILE,
            ],
            &[2],
            &[0, 1],
            &[],
            0,
        ))
        .unwrap();
        let mut run = TargetedAuthoringCheckRun::new_with_measurements(
            TargetedAuthoringCheckPlan::new(1, 2, 0),
            false,
            true,
        );
        run.adopt_execution_plan(&execution_plan).unwrap();
        let pending = pending_cached_fixture(0);
        run.retained_context_bytes = pending.retained_bytes;
        run.pending_context_indices_by_module
            .insert(pending.pending.module().clone(), 0);
        run.pending_contexts.insert(0, pending);
        run.record_live_support_visit(0);
        run.record_live_support_visit(1);
        run.lookup_misses
            .insert(1, TargetedAuthoringLookupMiss::Missing);
        run.state.context_misses = 1;
        run.retained_snapshots.insert(
            1,
            TargetedAuthoringCurrentSnapshot::new("consumer".to_owned(), vec![1]),
        );

        let promoted = run.resolve_reached_pre_target_support(1).unwrap();

        assert_eq!(promoted, vec![0, 1]);
        assert!(run.pending_contexts.is_empty());
        assert_eq!(run.state.context_bypassed_hits, 1);
        assert_eq!(run.state.context_hits, 0);
        assert_eq!(run.state.context_misses, 1);
        assert_eq!(run.retained_context_bytes, 0);
        assert!(run.retained_snapshots.contains_key(&0));
        assert!(run.retained_snapshots.contains_key(&1));
        assert_eq!(
            run.cache_diagnostics
                .iter()
                .filter(|diagnostic| {
                    diagnostic.reason_code == "targeted_authoring_cache_hit_bypassed"
                })
                .count(),
            1
        );
        run.take_retained_snapshot(0).unwrap();
        run.record_live_support_completion(0).unwrap();
        let stopped = run.finish(false, None);
        assert_eq!(stopped.summary.run.completed_support, 1);
        assert_eq!(stopped.summary.run.live_support_checks, 1);
        assert!(!stopped.summary.completed);
        assert!(stopped
            .summary
            .validate(TargetedAuthoringProvenance::LOCAL_ONLY)
            .is_ok());
    }

    #[test]
    fn targeted_authoring_differential_miss_promotion_preserves_uncovered_shared_diamond_hit() {
        let execution_plan = build_targeted_authoring_execution_plan(planner_input(
            &[0, 1, 2, 3],
            &[&[], &[0], &[0], &[1, 2]],
            &[
                HUMAN_SOURCE_PRODUCER_PROFILE,
                HUMAN_SOURCE_PRODUCER_PROFILE,
                HUMAN_SOURCE_PRODUCER_PROFILE,
                HUMAN_SOURCE_PRODUCER_PROFILE,
            ],
            &[3],
            &[0, 1, 2],
            &[],
            0,
        ))
        .unwrap();
        let mut run = TargetedAuthoringCheckRun::new(TargetedAuthoringCheckPlan::new(1, 3, 0));
        run.adopt_execution_plan(&execution_plan).unwrap();
        for module_index in [0, 1] {
            let pending = pending_cached_fixture(module_index);
            run.retained_context_bytes += pending.retained_bytes;
            run.pending_contexts.insert(module_index, pending);
            run.record_live_support_visit(module_index);
        }
        run.record_live_support_visit(2);
        run.lookup_misses
            .insert(2, TargetedAuthoringLookupMiss::Invalid);
        run.state.context_misses = 1;
        run.state.context_invalid = 1;
        run.retained_snapshots.insert(
            2,
            TargetedAuthoringCurrentSnapshot::new("right".to_owned(), vec![2]),
        );

        let promoted = run.resolve_reached_pre_target_support(2).unwrap();

        assert_eq!(promoted, vec![0, 2]);
        assert!(!run.pending_contexts.contains_key(&0));
        assert!(run.pending_contexts.contains_key(&1));
        assert_eq!(run.state.context_bypassed_hits, 1);
        assert_eq!(run.state.context_misses, 1);
    }

    #[test]
    fn targeted_authoring_miss_promotion_reconstructs_consumer_without_adopting_pending_leaf() {
        let options = HumanCompileOptions::default();
        let policy = AxiomPolicy::normal();
        let package = PackageId::new("fixture-package");
        let version = PackageVersion::new("0.1.0");
        let base_source = "axiom A : Type";
        let base =
            compile_human_source_to_certificate_output_with_source_interfaces_and_axiom_policy(
                FileId(0),
                Name::from_dotted("Pending.Base"),
                base_source,
                &[],
                &[],
                &options,
                &policy,
            )
            .unwrap();
        let base_interface = HumanImportedSourceInterface {
            module: base.certificate.header().module.clone(),
            export_hash: base.certificate.hashes().export_hash,
            certificate_hash: Some(base.certificate.hashes().certificate_hash),
            source_interface: base.source_interface.clone(),
        };
        let base_authoring = HumanAuthoringImport::from_verified_module(&base.verified_module);
        let base_adapter = HumanInterfaceCacheAdapterContext::new(
            &package,
            &version,
            HUMAN_SOURCE_PRODUCER_PROFILE,
            &[],
            0,
            base_source,
            &base_authoring,
        );
        let base_dto = human_interface_to_cache_dto(&base_interface, &base_adapter).unwrap();
        let mut base_entry = support_entry(
            &base.certificate,
            base_dto,
            Vec::new(),
            TargetedAuthoringInterfaceProfile::HumanSource,
        );
        base_entry.key_input.axiom_policy_hash = PackageHash::from(policy.policy_hash());
        base_entry.key_input.certificate_format = base.certificate.header().format.clone();
        base_entry.key_input.core_spec = base.certificate.header().core_spec.clone();
        base_entry = refresh_targeted_authoring_support_context_entry(&base_entry).unwrap();
        let base_snapshot = TargetedAuthoringCurrentSnapshot::new(
            base_source.to_owned(),
            encode_module_cert(&base.certificate).unwrap(),
        );
        let (base_pending, base_cached_interface) = reconstruct_pending_cached_support(
            &base_entry,
            &base_snapshot,
            0,
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &policy,
        )
        .unwrap();
        let retained_bytes = base_snapshot.loaded_bytes().unwrap();
        let pending_contexts = BTreeMap::from([(
            0,
            PendingCachedTargetedSupportContext {
                pending: base_pending,
                source_interface: base_cached_interface,
                snapshot: base_snapshot,
                retained_bytes,
            },
        )]);
        let pending_indices = BTreeMap::from([(Name::from_dotted("Pending.Base"), 0)]);

        let mid_source = "import Pending.Base\ndef B : Type := A";
        let mid =
            compile_human_source_to_certificate_output_with_source_interfaces_and_axiom_policy(
                FileId(1),
                Name::from_dotted("Pending.Mid"),
                mid_source,
                std::slice::from_ref(&base.verified_module),
                std::slice::from_ref(&base_interface),
                &options,
                &policy,
            )
            .unwrap();
        let mid_interface = HumanImportedSourceInterface {
            module: mid.certificate.header().module.clone(),
            export_hash: mid.certificate.hashes().export_hash,
            certificate_hash: Some(mid.certificate.hashes().certificate_hash),
            source_interface: mid.source_interface.clone(),
        };
        let direct_import = ResolvedModuleImportIdentity {
            module: base.certificate.header().module.clone(),
            export_hash: PackageHash::from(base.certificate.hashes().export_hash),
            certificate_hash: PackageHash::from(base.certificate.hashes().certificate_hash),
        };
        let mid_authoring = HumanAuthoringImport::from_verified_module(&mid.verified_module);
        let mid_adapter = HumanInterfaceCacheAdapterContext::new(
            &package,
            &version,
            HUMAN_SOURCE_PRODUCER_PROFILE,
            std::slice::from_ref(&direct_import),
            1,
            mid_source,
            &mid_authoring,
        );
        let mid_dto = human_interface_to_cache_dto(&mid_interface, &mid_adapter).unwrap();
        let mut mid_entry = support_entry(
            &mid.certificate,
            mid_dto,
            vec![direct_import],
            TargetedAuthoringInterfaceProfile::HumanSource,
        );
        mid_entry.key_input.axiom_policy_hash = PackageHash::from(policy.policy_hash());
        mid_entry.key_input.certificate_format = mid.certificate.header().format.clone();
        mid_entry.key_input.core_spec = mid.certificate.header().core_spec.clone();
        mid_entry = refresh_targeted_authoring_support_context_entry(&mid_entry).unwrap();
        let mid_snapshot = TargetedAuthoringCurrentSnapshot::new(
            mid_source.to_owned(),
            encode_module_cert(&mid.certificate).unwrap(),
        );

        let (mid_pending, _) = reconstruct_pending_cached_support(
            &mid_entry,
            &mid_snapshot,
            1,
            &BTreeMap::new(),
            &pending_contexts,
            &pending_indices,
            &policy,
        )
        .expect("a consumer should validate against an unadopted pending prerequisite");

        assert_eq!(mid_pending.module(), &Name::from_dotted("Pending.Mid"));
        assert_eq!(pending_contexts.len(), 1);
    }

    #[test]
    fn targeted_authoring_context_lifetimes_share_live_owner_and_release_combined_views() {
        let (_, verified, _) = compile_fixture(FileId(930));
        let verified = Arc::new(verified);
        let session = TargetedAuthoringBuildSession::new();
        let context = session.register_shared_live_support(Arc::clone(&verified));
        assert_eq!(Arc::strong_count(&verified), 2);
        assert!(!context.closure_used_cached_context());
        drop(context);
        assert_eq!(Arc::strong_count(&verified), 1);

        let execution_plan = build_targeted_authoring_execution_plan(planner_input(
            &[0, 1, 2, 3],
            &[&[], &[0], &[0, 1], &[0, 1]],
            &[
                HUMAN_SOURCE_PRODUCER_PROFILE,
                HUMAN_SOURCE_PRODUCER_PROFILE,
                HUMAN_SOURCE_PRODUCER_PROFILE,
                HUMAN_SOURCE_PRODUCER_PROFILE,
            ],
            &[1, 2, 3],
            &[0],
            &[],
            0,
        ))
        .unwrap();
        let mut ledger =
            TargetedAuthoringProducerLifetimeLedger::from_execution_plan(&execution_plan);
        assert!(ledger
            .register(
                0,
                TargetedAuthoringProducerViews::LIVE_SUPPORT_OR_FORCED_TARGET,
            )
            .unwrap());
        assert!(ledger
            .register(
                1,
                TargetedAuthoringProducerViews::LIVE_SUPPORT_OR_FORCED_TARGET,
            )
            .unwrap());

        assert!(ledger.consume_consumer(1).unwrap().is_empty());
        assert!(ledger.consume_consumer(2).unwrap().is_empty());
        assert_eq!(
            ledger.retained(0),
            Some(TargetedAuthoringProducerLifetime {
                remaining_uses: 1,
                views: TargetedAuthoringProducerViews::LIVE_SUPPORT_OR_FORCED_TARGET,
            })
        );
        assert_eq!(
            ledger.retained(1),
            Some(TargetedAuthoringProducerLifetime {
                remaining_uses: 1,
                views: TargetedAuthoringProducerViews::LIVE_SUPPORT_OR_FORCED_TARGET,
            })
        );
        assert_eq!(ledger.consume_consumer(3).unwrap(), vec![0, 1]);
        assert!(ledger.retained.is_empty());

        let execution_plan = simple_authoring_execution_plan();
        let mut run = TargetedAuthoringCheckRun::new(TargetedAuthoringCheckPlan::new(1, 1, 0));
        run.adopt_execution_plan(&execution_plan).unwrap();
        let pending = pending_cached_fixture(0);
        run.retained_context_bytes = pending.retained_bytes;
        run.pending_context_indices_by_module
            .insert(pending.pending.module().clone(), 0);
        run.pending_contexts.insert(0, pending);
        run.record_live_support_visit(0);
        let adopted = run.adopt_remaining_cached_support(&session).unwrap();
        assert_eq!(adopted.len(), 1);
        assert_eq!(adopted[0].module_index(), 0);
        assert!(adopted[0].context().closure_used_cached_context());
        assert_eq!(
            adopted[0].source_interface().module,
            Name::from_dotted("Fixture.Adapter")
        );
        assert_eq!(run.state.context_hits, 1);
        assert_eq!(run.state.avoided_kernel_checks, 1);
        assert_eq!(run.state.avoided_source_interface_resolutions, 1);
        assert_eq!(run.state.completed_support, 1);
        assert!(run.provenance.locally_accelerated);
        assert_eq!(run.retained_context_bytes, 0);
        drop(adopted);
    }

    #[test]
    fn targeted_authoring_differential_multi_target_attempts_are_unique_ordered_and_role_checked() {
        let execution_plan = build_targeted_authoring_execution_plan(planner_input(
            &[0, 1, 2],
            &[&[], &[0], &[0]],
            &[
                HUMAN_SOURCE_PRODUCER_PROFILE,
                HUMAN_SOURCE_PRODUCER_PROFILE,
                "unsupported-fixture-profile",
            ],
            &[0, 1, 2],
            &[],
            &[],
            0,
        ))
        .unwrap();
        let mut run = TargetedAuthoringCheckRun::new(TargetedAuthoringCheckPlan::new(3, 0, 0));
        run.adopt_execution_plan(&execution_plan).unwrap();

        run.record_target_attempt(0, true).unwrap();
        assert_eq!(
            run.record_target_attempt(0, true)
                .unwrap_err()
                .actual_value
                .as_deref(),
            Some("target_attempt_repeated")
        );
        run.record_target_completion();
        run.register_target_lifetime(0, true).unwrap();
        run.record_target_attempt(1, false).unwrap();
        run.record_target_completion();
        run.register_target_lifetime(1, false).unwrap();
        run.consume_local_consumer(1).unwrap();
        run.record_target_attempt(2, true).unwrap();
        run.record_target_completion();
        run.register_target_lifetime(2, true).unwrap();
        run.consume_local_consumer(2).unwrap();

        assert_eq!(run.target_attempt_order, vec![0, 1, 2]);
        assert_eq!(run.state.target_fresh_builds, 3);
        assert_eq!(run.state.targets_forced_live, 2);
        let completed = run.finish(true, None);
        assert!(completed
            .summary
            .validate(TargetedAuthoringProvenance::LOCAL_ONLY)
            .is_ok());
    }

    #[test]
    fn targeted_authoring_differential_miss_promotion_late_ineligibility_keeps_single_miss_bucket()
    {
        let execution_plan = simple_authoring_execution_plan();
        let mut run = TargetedAuthoringCheckRun::new(TargetedAuthoringCheckPlan::new(1, 1, 0));
        run.adopt_execution_plan(&execution_plan).unwrap();
        run.record_live_support_visit(0);
        run.record_lookup_miss(0, TargetedAuthoringLookupMiss::Missing);
        run.record_late_support_ineligibility(0, "interface_unrepresentable");
        run.record_late_support_ineligibility(0, "interface_unrepresentable");

        assert_eq!(run.state.context_misses, 1);
        assert_eq!(run.state.context_ineligible, 0);
        assert!(run.publication_suppressed.contains(&0));
        assert_eq!(
            run.cache_diagnostics
                .iter()
                .filter(|diagnostic| {
                    diagnostic.reason_code == "targeted_authoring_module_ineligible"
                })
                .count(),
            1
        );
    }

    #[test]
    fn package_build_cache_security_exact_hit_identity_drift_and_pending_classification() {
        let module_index = 77;
        let (certificate, verified, interface) = compile_fixture(FileId(module_index));
        let certificate_bytes = encode_module_cert(&certificate).unwrap();
        let package = PackageId::new("fixture-package");
        let version = PackageVersion::new("0.1.0");
        let authoring = HumanAuthoringImport::from_verified_module(&verified);
        let adapter = HumanInterfaceCacheAdapterContext::new(
            &package,
            &version,
            HUMAN_SOURCE_PRODUCER_PROFILE,
            &[],
            module_index as usize,
            SOURCE,
            &authoring,
        );
        let dto = human_interface_to_cache_dto(&interface, &adapter).unwrap();
        let policy = AxiomPolicy::normal();
        let mut entry = support_entry(
            &certificate,
            dto,
            Vec::new(),
            TargetedAuthoringInterfaceProfile::HumanSource,
        );
        entry.key_input.axiom_policy_hash = PackageHash::from(policy.policy_hash());
        entry.key_input.certificate_format = certificate.header().format.clone();
        entry.key_input.core_spec = certificate.header().core_spec.clone();
        entry = refresh_targeted_authoring_support_context_entry(&entry).unwrap();
        let snapshot =
            TargetedAuthoringCurrentSnapshot::new(SOURCE.to_owned(), certificate_bytes.clone());

        let source_drift =
            TargetedAuthoringCurrentSnapshot::new(format!("{SOURCE}\n"), certificate_bytes.clone());
        assert!(reconstruct_pending_cached_support(
            &entry,
            &source_drift,
            module_index as usize,
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &policy,
        )
        .is_err());

        let certificate_drift = TargetedAuthoringCurrentSnapshot::new(
            SOURCE.to_owned(),
            [certificate_bytes.as_slice(), b"drift"].concat(),
        );
        assert!(reconstruct_pending_cached_support(
            &entry,
            &certificate_drift,
            module_index as usize,
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &policy,
        )
        .is_err());

        let (pending, source_interface) = reconstruct_pending_cached_support(
            &entry,
            &snapshot,
            module_index as usize,
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &policy,
        )
        .expect("the exact current entry should remain pending");
        let execution_plan = simple_authoring_execution_plan();
        let mut run = TargetedAuthoringCheckRun::new(TargetedAuthoringCheckPlan::new(1, 1, 0));
        run.adopt_execution_plan(&execution_plan).unwrap();
        run.record_live_support_visit(0);
        run.pending_contexts.insert(
            0,
            PendingCachedTargetedSupportContext {
                pending,
                source_interface,
                snapshot,
                retained_bytes: SOURCE.len() + certificate_bytes.len(),
            },
        );

        assert_eq!(run.pending_contexts.len(), 1);
        assert_eq!(run.state.context_hits, 0);
        assert_eq!(run.state.context_misses, 0);
        assert_eq!(run.state.context_bypassed_hits, 0);
        let incomplete = run.finish(false, None);
        assert!(!incomplete.summary.completed);
        assert!(incomplete
            .summary
            .validate(TargetedAuthoringProvenance::LOCAL_ONLY)
            .is_ok());
    }

    #[test]
    fn targeted_authoring_lookup_unavailable_classifies_only_reached_partial_graph() {
        let execution_plan = build_targeted_authoring_execution_plan(planner_input(
            &[0, 1, 2],
            &[&[], &[0], &[1]],
            &[
                HUMAN_SOURCE_PRODUCER_PROFILE,
                HUMAN_SOURCE_PRODUCER_PROFILE,
                HUMAN_SOURCE_PRODUCER_PROFILE,
            ],
            &[2],
            &[0, 1],
            &[],
            0,
        ))
        .unwrap();
        let mut partial = TargetedAuthoringCheckRun::new(TargetedAuthoringCheckPlan::new(1, 2, 0));
        partial.adopt_execution_plan(&execution_plan).unwrap();
        partial.record_live_support_visit(0);
        assert!(partial.should_capture_pre_target_snapshot(0));
        partial.record_lookup_miss(0, TargetedAuthoringLookupMiss::Unavailable);
        assert_eq!(partial.state.context_misses, 1);
        assert_eq!(partial.lookup_misses.len(), 1);
        let partial = partial.finish(false, None);
        assert!(!partial.summary.completed);
        assert!(partial
            .summary
            .validate(TargetedAuthoringProvenance::LOCAL_ONLY)
            .is_ok());

        let mut completed =
            TargetedAuthoringCheckRun::new(TargetedAuthoringCheckPlan::new(1, 2, 0));
        completed.adopt_execution_plan(&execution_plan).unwrap();
        for module_index in [0, 1] {
            completed.record_live_support_visit(module_index);
            assert!(completed.should_capture_pre_target_snapshot(module_index));
            completed.record_lookup_miss(module_index, TargetedAuthoringLookupMiss::Unavailable);
            completed
                .record_live_support_completion(module_index)
                .unwrap();
        }
        completed.record_target_attempt(2, false).unwrap();
        completed.record_target_completion();
        assert_eq!(completed.state.context_misses, 2);
        assert_eq!(completed.lookup_misses.len(), 2);
        let completed = completed.finish(true, None);
        assert!(completed.summary.completed);
        assert!(completed
            .summary
            .validate(TargetedAuthoringProvenance::LOCAL_ONLY)
            .is_ok());
    }

    fn assert_compilation_observation_parity(
        authoring: &HumanCompilationObservations,
        ordinary: &HumanCompilationObservations,
    ) {
        assert_eq!(authoring.attempted, ordinary.attempted);
        assert_eq!(authoring.omitted, ordinary.omitted);
        assert_eq!(authoring.overflowed, ordinary.overflowed);
        assert_eq!(authoring.declarations.len(), ordinary.declarations.len());
        for (authoring, ordinary) in authoring.declarations.iter().zip(&ordinary.declarations) {
            assert_eq!(authoring.declaration_index, ordinary.declaration_index);
            assert_eq!(authoring.declaration, ordinary.declaration);
            assert_eq!(authoring.term_nodes, ordinary.term_nodes);
            assert_eq!(authoring.kernel, ordinary.kernel);
        }
    }

    fn human_interface_spans(interface: &HumanImportedSourceInterface) -> Vec<Span> {
        let source = &interface.source_interface;
        let mut spans = Vec::new();
        for declaration in &source.declarations {
            spans.push(declaration.name.span);
            spans.extend(declaration.universe_params.iter().map(|value| value.span));
            for binder in &declaration.binders {
                spans.extend(binder.name.iter().map(|value| value.span));
                spans.push(binder.span);
            }
            spans.push(declaration.span);
        }
        for notation in &source.notations {
            spans.push(notation.target.span);
            spans.push(notation.span);
        }
        for generated in &source.generated_declarations {
            spans.push(generated.parent.span);
            spans.push(generated.name.span);
            spans.push(generated.span);
        }
        for class in &source.typeclass_classes {
            spans.push(class.name.span);
            spans.push(class.constructor.span);
            for field in &class.fields {
                spans.push(field.name.span);
                spans.push(field.projection.span);
                spans.push(field.span);
            }
            spans.push(class.span);
        }
        for instance in &source.typeclass_instances {
            spans.push(instance.name.span);
            spans.extend(instance.class.iter().map(|value| value.span));
            spans.push(instance.span);
        }
        spans
    }

    #[test]
    fn targeted_authoring_differential_human_compile_matches_live_bytes_interface_observations_and_origins(
    ) {
        let (_, verified, imported_interface) = compile_fixture(FileId(7));
        let file_id = FileId(21);
        let module = Name::from_dotted("Fixture.Target");
        let source = "import Fixture.Adapter\naxiom input : A\ndef target : A := input ++ input";
        let options = HumanCompileOptions::default();
        let policy = AxiomPolicy::normal();
        let ordinary =
            compile_human_source_to_observed_certificate_output_with_available_import_refs_and_axiom_policy(
                file_id,
                module.clone(),
                source,
                &[&verified],
                &[&verified],
                std::slice::from_ref(&imported_interface),
                &options,
                &policy,
                None,
                true,
            )
            .expect("ordinary Human compilation should succeed");

        let session = TargetedAuthoringBuildSession::new();
        let authoring_import = session.register_verified_module(&verified).unwrap();
        let authoring = session
            .compile_human_target(
                file_id,
                module,
                source,
                std::slice::from_ref(&authoring_import),
                std::slice::from_ref(&authoring_import),
                std::slice::from_ref(&imported_interface),
                &options,
                &policy,
                None,
                true,
            )
            .expect("authoring-only Human compilation should succeed");

        assert_eq!(
            authoring.certificate_bytes(),
            encode_module_cert(&ordinary.output.certificate).unwrap()
        );
        assert_eq!(
            authoring.source_interface(),
            &ordinary.output.source_interface
        );
        assert_compilation_observation_parity(
            authoring.compilation_observations(),
            &ordinary.observations,
        );
        assert_eq!(authoring.authoring_observations().import_contexts(), 1);
        assert!(!authoring
            .authoring_observations()
            .closure_used_cached_context());
        assert!(authoring
            .source_interface()
            .declarations
            .iter()
            .all(|declaration| declaration.span.file_id == file_id));
        assert!(!authoring.is_proof_evidence());
        assert!(!authoring.is_publication_eligible());
        assert!(!authoring.fresh_context().is_proof_evidence());
        assert!(!authoring.fresh_context().is_publication_eligible());
    }

    #[test]
    fn targeted_authoring_differential_human_compile_transitive_preferred_imports_match_live() {
        let options = HumanCompileOptions::default();
        let policy = AxiomPolicy::normal();
        let base =
            compile_human_source_to_certificate_output_with_source_interfaces_and_axiom_policy(
                FileId(22),
                Name::from_dotted("Preferred.Base"),
                "axiom A : Type",
                &[],
                &[],
                &options,
                &policy,
            )
            .unwrap();
        let base_interface = HumanImportedSourceInterface {
            module: base.certificate.header().module.clone(),
            export_hash: base.certificate.hashes().export_hash,
            certificate_hash: Some(base.certificate.hashes().certificate_hash),
            source_interface: base.source_interface.clone(),
        };
        let mid =
            compile_human_source_to_certificate_output_with_source_interfaces_and_axiom_policy(
                FileId(23),
                Name::from_dotted("Preferred.Mid"),
                "import Preferred.Base\ndef B : Type := A",
                std::slice::from_ref(&base.verified_module),
                std::slice::from_ref(&base_interface),
                &options,
                &policy,
            )
            .unwrap();
        let mid_interface = HumanImportedSourceInterface {
            module: mid.certificate.header().module.clone(),
            export_hash: mid.certificate.hashes().export_hash,
            certificate_hash: Some(mid.certificate.hashes().certificate_hash),
            source_interface: mid.source_interface.clone(),
        };
        let source = "import Preferred.Mid\ndef use : Type := B";
        let available_live = [&base.verified_module, &mid.verified_module];
        let ordinary =
            compile_human_source_to_observed_certificate_output_with_available_import_refs_and_axiom_policy(
                FileId(24),
                Name::from_dotted("Preferred.Consumer"),
                source,
                &[&mid.verified_module],
                &available_live,
                std::slice::from_ref(&mid_interface),
                &options,
                &policy,
                None,
                false,
            )
            .unwrap();

        let session = TargetedAuthoringBuildSession::new();
        let mid_authoring = session
            .register_verified_module(&mid.verified_module)
            .unwrap();
        let base_authoring = session
            .register_verified_module(&base.verified_module)
            .unwrap();
        let available_authoring = [base_authoring, mid_authoring.clone()];
        let authoring = session
            .compile_human_target(
                FileId(24),
                Name::from_dotted("Preferred.Consumer"),
                source,
                std::slice::from_ref(&mid_authoring),
                &available_authoring,
                std::slice::from_ref(&mid_interface),
                &options,
                &policy,
                None,
                false,
            )
            .unwrap();

        assert_eq!(
            authoring.certificate_bytes(),
            encode_module_cert(&ordinary.output.certificate).unwrap()
        );
        assert_eq!(
            ordinary
                .output
                .certificate
                .imports()
                .iter()
                .map(|import| import.module.as_dotted())
                .collect::<Vec<_>>(),
            ["Preferred.Base", "Preferred.Mid"]
        );
        assert_eq!(authoring.authoring_observations().import_contexts(), 2);
    }

    #[test]
    fn targeted_authoring_differential_human_compile_failure_diagnostics_match_live() {
        let options = HumanCompileOptions::default();
        let normal = AxiomPolicy::normal();
        let cases = [
            ("parse", "def"),
            ("resolution", "import Missing\naxiom P : Prop"),
            ("elaboration", "def bad (A x : Type) : A := x"),
        ];
        for (name, source) in cases {
            let file_id = FileId(30);
            let module = Name::from_dotted("Fixture.Failure");
            let ordinary =
                compile_human_source_to_observed_certificate_output_with_available_import_refs_and_axiom_policy(
                    file_id,
                    module.clone(),
                    source,
                    &[],
                    &[],
                    &[],
                    &options,
                    &normal,
                    None,
                    true,
                )
                .expect_err("ordinary fixture should fail");
            let session = TargetedAuthoringBuildSession::new();
            let authoring = session
                .compile_human_target(
                    file_id,
                    module,
                    source,
                    &[],
                    &[],
                    &[],
                    &options,
                    &normal,
                    None,
                    true,
                )
                .expect_err("authoring fixture should fail");
            assert_eq!(authoring, ordinary, "{name} diagnostic drifted");
        }

        let source = "axiom P : Prop";
        let file_id = FileId(31);
        let module = Name::from_dotted("Fixture.PolicyFailure");
        let high_trust = AxiomPolicy::high_trust();
        let ordinary =
            compile_human_source_to_observed_certificate_output_with_available_import_refs_and_axiom_policy(
                file_id,
                module.clone(),
                source,
                &[],
                &[],
                &[],
                &options,
                &high_trust,
                None,
                true,
            )
            .expect_err("ordinary high-trust check should reject the axiom");
        let session = TargetedAuthoringBuildSession::new();
        let authoring = session
            .compile_human_target(
                file_id,
                module,
                source,
                &[],
                &[],
                &[],
                &options,
                &high_trust,
                None,
                true,
            )
            .expect_err("authoring high-trust check should reject the axiom");
        assert_eq!(authoring, ordinary);
    }

    #[test]
    fn human_authoring_compile_fresh_context_is_command_local_and_reusable() {
        let options = HumanCompileOptions::default();
        let policy = AxiomPolicy::normal();
        let owner = TargetedAuthoringBuildSession::new();
        let base = owner
            .compile_human_target(
                FileId(40),
                Name::from_dotted("Fresh.Base"),
                "axiom A : Type",
                &[],
                &[],
                &[],
                &options,
                &policy,
                None,
                false,
            )
            .unwrap();
        let base_interface = base.imported_source_interface();
        let base_import = base.fresh_context().authoring_import().unwrap();
        let consumer = owner
            .compile_human_target(
                FileId(41),
                Name::from_dotted("Fresh.Consumer"),
                "import Fresh.Base\ndef use : Type := A",
                std::slice::from_ref(&base_import),
                std::slice::from_ref(&base_import),
                std::slice::from_ref(&base_interface),
                &options,
                &policy,
                None,
                false,
            )
            .expect("the owner session may consume its fresh target context");
        assert_eq!(consumer.authoring_observations().import_contexts(), 1);
        assert!(!consumer.fresh_context().closure_used_cached_context());

        let other = TargetedAuthoringBuildSession::new();
        let error = other
            .compile_human_target(
                FileId(42),
                Name::from_dotted("Fresh.OtherConsumer"),
                "import Fresh.Base\ndef use : Type := A",
                std::slice::from_ref(&base_import),
                std::slice::from_ref(&base_import),
                std::slice::from_ref(&base_interface),
                &options,
                &policy,
                None,
                false,
            )
            .expect_err("another session must reject the retained fresh context");
        assert!(error.message.contains("ImportNotVerifiedInSession"));
    }

    #[test]
    fn human_authoring_compile_propagates_cached_closure_without_publication_capability() {
        let (certificate, _, imported_interface) = compile_fixture(FileId(50));
        let certificate_bytes = encode_module_cert(&certificate).unwrap();
        let policy = AxiomPolicy::normal();
        let session = LocalAuthoringVerifierSession::new();
        let pending = session
            .reconstruct_pending_context(
                &certificate_bytes,
                &npa_cert::LocalAuthoringReconstructionIdentity::new(
                    package_file_hash(&certificate_bytes).into_bytes(),
                    certificate.header().format.clone(),
                    certificate.header().core_spec.clone(),
                    certificate.header().module.clone(),
                    certificate.imports().to_vec(),
                    certificate.hashes().export_hash,
                    certificate.hashes().axiom_report_hash,
                    certificate.hashes().certificate_hash,
                    policy.policy_hash(),
                ),
                &npa_cert::LocalAuthoringInterfaceIdentity::new(
                    certificate.header().module.clone(),
                    certificate.hashes().export_hash,
                    certificate.hashes().certificate_hash,
                ),
                &[],
                &policy,
            )
            .unwrap();
        let cached_context = session.adopt_pending_context(pending);
        let cached_import =
            HumanAuthoringImport::from_local_authoring_context(&cached_context).unwrap();
        let output =
            compile_human_source_to_authoring_certificate_output_with_available_imports_and_axiom_policy(
                &session,
                FileId(51),
                Name::from_dotted("Fixture.CachedConsumer"),
                "import Fixture.Adapter\ndef use : Type := A",
                std::slice::from_ref(&cached_import),
                std::slice::from_ref(&cached_import),
                std::slice::from_ref(&imported_interface),
                &HumanCompileOptions::default(),
                &policy,
                None,
                false,
            )
            .unwrap();
        assert!(output.closure_used_cached_context());
        assert!(output
            .authoring_observations()
            .closure_used_cached_context());
        assert!(!output.is_proof_evidence());
        assert!(!output.is_publication_eligible());
        assert!(!output.fresh_context().is_proof_evidence());
        assert!(!output.fresh_context().is_publication_eligible());

        let wrapped = TargetedAuthoringModuleBuild::from_frontend(output);
        assert!(wrapped.fresh_context().closure_used_cached_context());
        assert!(!wrapped.is_publication_eligible());
    }

    #[test]
    fn targeted_authoring_differential_human_interface_cache_adapter_field_parity_origins_and_unsupported_fallback(
    ) {
        let file_id = FileId(7);
        let (certificate, verified, interface) = compile_fixture(file_id);
        let authoring = HumanAuthoringImport::from_verified_module(&verified);
        let package = PackageId::new("fixture-package");
        let version = PackageVersion::new("0.1.0");
        let context = HumanInterfaceCacheAdapterContext::new(
            &package,
            &version,
            HUMAN_SOURCE_PRODUCER_PROFILE,
            &[],
            7,
            SOURCE,
            &authoring,
        );
        let dto = human_interface_to_cache_dto(&interface, &context).unwrap();

        assert_eq!(
            dto.source_interface.module,
            interface.source_interface.module
        );
        assert_eq!(
            dto.source_interface.declarations.len(),
            interface.source_interface.declarations.len()
        );
        assert_eq!(
            dto.source_interface.notations.len(),
            interface.source_interface.notations.len()
        );
        assert!(!dto.source_interface.generated_declarations.is_empty());
        assert!(!dto.source_interface.typeclass_classes.is_empty());
        assert!(!dto.source_interface.typeclass_instances.is_empty());
        assert!(dto.source_interface.declarations.iter().all(|declaration| {
            declaration.span.origin == TargetedAuthoringSpanOrigin::CurrentModule
                && declaration.decl_interface_hash.is_some()
        }));
        assert!(dto
            .source_interface
            .declarations
            .iter()
            .any(|declaration| !declaration.universe_params.is_empty()
                && declaration.binders.iter().any(
                    |binder| binder.binder_info == TargetedAuthoringHumanBinderInfo::Implicit
                )));
        let notation = &dto.source_interface.notations[0];
        assert_eq!(notation.kind, TargetedAuthoringHumanNotationKind::Infixl);
        assert_eq!(
            notation.associativity,
            TargetedAuthoringHumanNotationAssociativity::Left
        );
        assert_eq!(notation.precedence, 65);
        assert_eq!(notation.token, "++");
        assert!(notation.namespace.is_empty());

        let entry = support_entry(
            &certificate,
            dto,
            Vec::new(),
            TargetedAuthoringInterfaceProfile::HumanSource,
        );
        assert_eq!(
            cache_entry_to_human_interface(&entry, &context).unwrap(),
            interface
        );
        let reordered_context = HumanInterfaceCacheAdapterContext::new(
            &package,
            &version,
            HUMAN_SOURCE_PRODUCER_PROFILE,
            &[],
            17,
            SOURCE,
            &authoring,
        );
        let reordered = cache_entry_to_human_interface(&entry, &reordered_context).unwrap();
        let reordered_spans = human_interface_spans(&reordered);
        assert!(!reordered_spans.is_empty());
        assert!(reordered_spans
            .iter()
            .all(|span| span.file_id == FileId(17)));
        assert!(reordered_spans
            .iter()
            .any(|span| span.start.0 != 0 || span.end.0 != 0));

        let fallback = crate::package_build::fallback_imported_source_interface(&verified);
        let fallback_context = HumanInterfaceCacheAdapterContext::new(
            &package,
            &version,
            LEGACY_STD_PACKAGE_PRODUCER_PROFILE,
            &[],
            usize::MAX,
            SOURCE,
            &authoring,
        );
        let fallback_dto = human_interface_to_cache_dto(&fallback, &fallback_context).unwrap();
        assert!(fallback_dto
            .source_interface
            .declarations
            .iter()
            .all(|declaration| declaration.span.origin
                == TargetedAuthoringSpanOrigin::SyntheticFallback
                && declaration.span.start == 0
                && declaration.span.end == 0));
        let fallback_entry = support_entry(
            &certificate,
            fallback_dto,
            Vec::new(),
            TargetedAuthoringInterfaceProfile::SyntheticCertificateFallback,
        );
        assert_eq!(
            cache_entry_to_human_interface(&fallback_entry, &fallback_context).unwrap(),
            fallback
        );
        let reordered_fallback_context = HumanInterfaceCacheAdapterContext::new(
            &package,
            &version,
            LEGACY_STD_PACKAGE_PRODUCER_PROFILE,
            &[],
            23,
            SOURCE,
            &authoring,
        );
        let reordered_fallback =
            cache_entry_to_human_interface(&fallback_entry, &reordered_fallback_context).unwrap();
        let fallback_spans = human_interface_spans(&reordered_fallback);
        assert!(!fallback_spans.is_empty());
        assert!(fallback_spans
            .iter()
            .all(|span| { span.file_id == FileId(0) && span.start.0 == 0 && span.end.0 == 0 }));

        let mut missing_hash = interface.clone();
        missing_hash.certificate_hash = None;
        let error = human_interface_to_cache_dto(&missing_hash, &context).unwrap_err();
        assert_eq!(
            error.kind(),
            HumanInterfaceCacheAdapterErrorKind::Unsupported
        );
        assert_eq!(error.reason_code(), "certificate_hash_unrepresentable");

        let unknown_profile_context = HumanInterfaceCacheAdapterContext::new(
            &package,
            &version,
            "future-human-producer",
            &[],
            7,
            SOURCE,
            &authoring,
        );
        let error = human_interface_to_cache_dto(&interface, &unknown_profile_context).unwrap_err();
        assert_eq!(
            error.kind(),
            HumanInterfaceCacheAdapterErrorKind::Unsupported
        );
        assert_eq!(error.reason_code(), "unsupported_producer_profile");

        let mut incompatible_span = interface.clone();
        incompatible_span.source_interface.declarations[0]
            .span
            .file_id = FileId(0);
        let error = human_interface_to_cache_dto(&incompatible_span, &context).unwrap_err();
        assert_eq!(
            error.kind(),
            HumanInterfaceCacheAdapterErrorKind::Unsupported
        );
        assert_eq!(error.reason_code(), "span_origin_unrepresentable");

        if usize::BITS > u32::BITS {
            let error = checked_current_module_file_id(u32::MAX as usize + 1).unwrap_err();
            assert_eq!(error.reason_code(), "module_index_out_of_range");
        }
    }

    #[test]
    fn targeted_authoring_differential_human_interface_cache_adapter_reordered_import_map_is_not_normalized(
    ) {
        let file_id = FileId(2);
        let (_certificate, verified, interface) = compile_fixture(file_id);
        let authoring = HumanAuthoringImport::from_verified_module(&verified);
        let package = PackageId::new("fixture-package");
        let version = PackageVersion::new("0.1.0");
        let first = ResolvedModuleImportIdentity {
            module: Name::from_dotted("Fixture.Zed"),
            export_hash: hash(11),
            certificate_hash: hash(12),
        };
        let second = ResolvedModuleImportIdentity {
            module: Name::from_dotted("Fixture.Alpha"),
            export_hash: hash(13),
            certificate_hash: hash(14),
        };
        let direct_imports = [first.clone(), second.clone()];
        let context = HumanInterfaceCacheAdapterContext::new(
            &package,
            &version,
            HUMAN_SOURCE_PRODUCER_PROFILE,
            &direct_imports,
            2,
            SOURCE,
            &authoring,
        );
        let dto = human_interface_to_cache_dto(&interface, &context).unwrap();
        assert_eq!(dto.direct_imports, [first, second]);
    }

    #[test]
    fn targeted_authoring_differential_human_interface_enum_and_namespace_matrix_round_trips() {
        let file_id = FileId(19);
        let (certificate, verified, interface) = compile_fixture(file_id);
        let authoring = HumanAuthoringImport::from_verified_module(&verified);
        let package = PackageId::new("fixture-package");
        let version = PackageVersion::new("0.1.0");
        let context = HumanInterfaceCacheAdapterContext::new(
            &package,
            &version,
            HUMAN_SOURCE_PRODUCER_PROFILE,
            &[],
            19,
            SOURCE,
            &authoring,
        );
        let round_trip = |candidate: &HumanImportedSourceInterface| {
            let dto = human_interface_to_cache_dto(candidate, &context).unwrap();
            let entry = support_entry(
                &certificate,
                dto,
                Vec::new(),
                TargetedAuthoringInterfaceProfile::HumanSource,
            );
            cache_entry_to_human_interface(&entry, &context).unwrap()
        };

        for kind in [
            HumanSourceDeclarationKind::Def,
            HumanSourceDeclarationKind::Theorem,
            HumanSourceDeclarationKind::Axiom,
            HumanSourceDeclarationKind::Inductive,
            HumanSourceDeclarationKind::Class,
            HumanSourceDeclarationKind::ClassField,
            HumanSourceDeclarationKind::Instance,
        ] {
            let mut candidate = interface.clone();
            candidate.source_interface.declarations[0].kind = kind;
            assert_eq!(round_trip(&candidate), candidate, "{kind:?}");
        }
        let mut imported = interface.clone();
        imported.source_interface.declarations[0].kind = HumanSourceDeclarationKind::Imported;
        let error = human_interface_to_cache_dto(&imported, &context).unwrap_err();
        assert_eq!(error.reason_code(), "interface_profile_unrepresentable");
        let definition_index = interface
            .source_interface
            .declarations
            .iter()
            .position(|declaration| declaration.kind == HumanSourceDeclarationKind::Def)
            .expect("fixture definition");
        for reducibility in [
            None,
            Some(DefinitionReducibility::Reducible),
            Some(DefinitionReducibility::Opaque),
        ] {
            let mut candidate = interface.clone();
            candidate.source_interface.declarations[definition_index].definition_reducibility =
                reducibility;
            assert_eq!(round_trip(&candidate), candidate, "{reducibility:?}");
        }
        for (kind, associativity) in [
            (
                HumanNotationKind::Notation,
                HumanNotationAssociativity::NonAssoc,
            ),
            (
                HumanNotationKind::Prefix,
                HumanNotationAssociativity::NonAssoc,
            ),
            (
                HumanNotationKind::Postfix,
                HumanNotationAssociativity::NonAssoc,
            ),
            (
                HumanNotationKind::Infix,
                HumanNotationAssociativity::NonAssoc,
            ),
            (HumanNotationKind::Infixl, HumanNotationAssociativity::Left),
            (HumanNotationKind::Infixr, HumanNotationAssociativity::Right),
        ] {
            let mut candidate = interface.clone();
            candidate.source_interface.notations[0].kind = kind;
            candidate.source_interface.notations[0].associativity = associativity;
            candidate.source_interface.notations[0].namespace =
                vec!["Fixture".to_owned(), "Nested".to_owned()];
            assert_eq!(round_trip(&candidate), candidate, "{kind:?}");
        }
    }

    #[test]
    fn package_build_cache_security_interface_adapter_rejects_malformed_reference_and_origin() {
        let file_id = FileId(3);
        let (certificate, verified, interface) = compile_fixture(file_id);
        let authoring = HumanAuthoringImport::from_verified_module(&verified);
        let package = PackageId::new("fixture-package");
        let version = PackageVersion::new("0.1.0");
        let context = HumanInterfaceCacheAdapterContext::new(
            &package,
            &version,
            HUMAN_SOURCE_PRODUCER_PROFILE,
            &[],
            3,
            SOURCE,
            &authoring,
        );
        let dto = human_interface_to_cache_dto(&interface, &context).unwrap();
        let mut entry = support_entry(
            &certificate,
            dto,
            Vec::new(),
            TargetedAuthoringInterfaceProfile::HumanSource,
        );
        entry.source_interface.source_interface.notations[0]
            .target
            .parts = vec!["Missing".to_owned(), "target".to_owned()];
        let error = cache_entry_to_human_interface(&entry, &context).unwrap_err();
        assert_eq!(error.kind(), HumanInterfaceCacheAdapterErrorKind::Invalid);
        assert_eq!(error.reason_code(), "support_context_entry_invalid");

        let dto = human_interface_to_cache_dto(&interface, &context).unwrap();
        let mut entry = support_entry(
            &certificate,
            dto,
            Vec::new(),
            TargetedAuthoringInterfaceProfile::HumanSource,
        );
        entry.source_interface.source_interface.declarations[0]
            .span
            .origin = TargetedAuthoringSpanOrigin::SyntheticFallback;
        let error = cache_entry_to_human_interface(&entry, &context).unwrap_err();
        assert_eq!(error.kind(), HumanInterfaceCacheAdapterErrorKind::Invalid);

        let dto = human_interface_to_cache_dto(&interface, &context).unwrap();
        let mut entry = support_entry(
            &certificate,
            dto,
            Vec::new(),
            TargetedAuthoringInterfaceProfile::HumanSource,
        );
        entry
            .source_interface
            .source_interface
            .declarations
            .retain(|declaration| declaration.name.parts != ["a"]);
        let entry = refresh_targeted_authoring_support_context_entry(&entry).unwrap();
        let error = cache_entry_to_human_interface(&entry, &context).unwrap_err();
        assert_eq!(error.reason_code(), "interface_catalog_incomplete");
    }

    #[test]
    fn targeted_authoring_differential_human_interface_cache_round_trip_resolves_and_elaborates_like_live(
    ) {
        let file_id = FileId(5);
        let (certificate, verified, live_interface) = compile_fixture(file_id);
        let authoring = HumanAuthoringImport::from_verified_module(&verified);
        let package = PackageId::new("fixture-package");
        let version = PackageVersion::new("0.1.0");
        let context = HumanInterfaceCacheAdapterContext::new(
            &package,
            &version,
            HUMAN_SOURCE_PRODUCER_PROFILE,
            &[],
            5,
            SOURCE,
            &authoring,
        );
        let dto = human_interface_to_cache_dto(&live_interface, &context).unwrap();
        let entry = support_entry(
            &certificate,
            dto,
            Vec::new(),
            TargetedAuthoringInterfaceProfile::HumanSource,
        );
        let reconstructed = cache_entry_to_human_interface(&entry, &context).unwrap();
        assert_eq!(reconstructed, live_interface);

        let consumer_source = "import Fixture.Adapter\naxiom a : A\ndef use : A := a ++ a";
        let live_parsed = parse_human_module_with_source_interfaces(
            FileId(9),
            consumer_source,
            std::slice::from_ref(&live_interface),
        )
        .unwrap();
        let reconstructed_parsed = parse_human_module_with_source_interfaces(
            FileId(9),
            consumer_source,
            std::slice::from_ref(&reconstructed),
        )
        .unwrap();
        assert_eq!(live_parsed, reconstructed_parsed);

        let options = HumanCompileOptions::default();
        let live_resolved = resolve_human_module_with_authoring_imports_and_source_interfaces(
            Name::from_dotted("Fixture.Consumer"),
            live_parsed,
            std::slice::from_ref(&authoring),
            std::slice::from_ref(&live_interface),
            &options,
        )
        .unwrap();
        let reconstructed_resolved =
            resolve_human_module_with_authoring_imports_and_source_interfaces(
                Name::from_dotted("Fixture.Consumer"),
                reconstructed_parsed,
                std::slice::from_ref(&authoring),
                std::slice::from_ref(&reconstructed),
                &options,
            )
            .unwrap();
        assert_eq!(live_resolved, reconstructed_resolved);

        let live_core = elaborate_human_module_with_authoring_imports(
            Name::from_dotted("Fixture.Consumer"),
            live_resolved,
            std::slice::from_ref(&authoring),
            &options,
        )
        .unwrap();
        let reconstructed_core = elaborate_human_module_with_authoring_imports(
            Name::from_dotted("Fixture.Consumer"),
            reconstructed_resolved,
            std::slice::from_ref(&authoring),
            &options,
        )
        .unwrap();
        assert_eq!(live_core, reconstructed_core);
    }
}

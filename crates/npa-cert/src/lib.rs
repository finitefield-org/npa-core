//! Canonical certificate construction, hashing, encoding, and verification.
//!
//! This crate treats parser, elaborator, tactics, and automation output as untrusted. Its public
//! API accepts already elaborated kernel declarations, emits deterministic canonical certificates,
//! and verifies only canonical certificate bytes against the small Rust kernel.
//!
//! Validation-stage capabilities are deliberately private and cannot be supplied by callers:
//!
//! ```compile_fail
//! let _ = npa_cert::ValidatedLevelReferences(());
//! ```
//!
//! ```compile_fail
//! let _ = npa_cert::ValidatedTermReferences(());
//! ```
//!
//! ```compile_fail
//! let _ = std::mem::size_of::<npa_cert::ValidatedCertificateTables>();
//! ```
//!
//! Canonical-byte equality evidence and built-certificate encodings also have no public
//! construction or conversion path:
//!
//! ```compile_fail
//! let built: npa_cert::BuiltCertificateHashEncoding = unreachable!();
//! let _: npa_cert::CanonicalCertificateEncoding<'_> = built.into();
//! ```
//!
//! ```compile_fail
//! let built: npa_cert::BuiltCertificateHashEncoding = unreachable!();
//! let _: npa_cert::CanonicalCertificateHashInput<'_> = built.into();
//! ```

#![deny(missing_docs)]

mod binary;
mod canonical;
mod declaration_closure;
mod hash;
mod inductive;
mod kernel;
#[cfg(test)]
mod legacy_owned_oracle;
mod local_authoring;
mod local_transparency;
mod logical_charge;
mod producer;
mod rebind;
#[cfg(test)]
mod shared_payload_contract_tests;
mod structural;
mod theorem_premise_analysis;
mod types;
mod verify;

/// Semantic ABI of locally reconstructed certificate-authoring producer state.
pub const LOCAL_AUTHORING_PRODUCER_ABI: &str = "npa.cert.local_authoring_producer_abi.v2";

pub use declaration_closure::*;
pub use inductive::{
    classify_inductive_artifact_profile_v1, generate_inductive_artifacts_v1,
    generate_mutual_inductive_artifacts_v1, inductive_generated_artifact_hashes_v1,
    InductiveArtifactProfileCheckV1, InductiveGeneratedArtifactHashesV1,
    UnsupportedMvpRecursorProfileV1,
};
pub use kernel::{
    benchmark_term_materialization_admission_v1, benchmark_term_materialization_plan_v1,
    builtin_decl_interface_hash, verified_module_to_kernel_decls,
    TermMaterializationBenchmarkResultV1, TERM_MATERIALIZATION_BUDGET_POLICY_V1,
    TERM_MATERIALIZATION_CHARGED_BYTE_LIMIT,
};
pub use local_authoring::*;
pub use local_transparency::dependency_selective_fingerprint_canonical_bytes;
pub use logical_charge::{
    PACKAGE_SHARED_ARC_METADATA_BYTES_V1, PACKAGE_SHARED_CACHE_ENTRY_LIMIT_V1,
    PACKAGE_SHARED_CACHE_ENTRY_OVERHEAD_BYTES_V1, PACKAGE_SHARED_CACHE_RETAINED_BYTE_LIMIT_V1,
    PACKAGE_SHARED_PAYLOAD_CHARGE_METADATA_BYTES_V1,
};
pub use producer::*;
pub use rebind::*;
pub use structural::{
    CertificateStructuralAudit, CertificateStructuralImportAudit, MAX_CERTIFICATE_BYTES,
    MAX_CERTIFICATE_EXPANDED_NODES, MAX_CLOSURE_EXPANDED_NODES, MAX_CLOSURE_MODULES,
    MAX_DECLARATIONS, MAX_EXPORTS, MAX_IMPORTS, MAX_LEVEL_TABLE_NODES, MAX_NAME_TABLE_ENTRIES,
    MAX_NESTED_VECTOR_ENTRIES, MAX_ROOT_EXPANDED_NODES, MAX_STRUCTURAL_DEPTH, MAX_TERM_TABLE_NODES,
};
pub use theorem_premise_analysis::*;
pub use types::*;

pub(crate) use binary::*;
pub(crate) use canonical::*;
pub(crate) use hash::*;
pub(crate) use kernel::{
    add_current_module_decl_to_env, add_decl_to_env, add_referenced_builtins_to_env,
    builtin_is_axiom, cert_decl_to_kernel_decl_with_terms,
    certificate_import_export_entry_to_kernel_decl,
    certificate_import_export_entry_to_kernel_decl_with_terms,
    certificate_import_referenced_builtin_names, certificate_import_to_kernel_decls,
    collect_decl_payload_term_roots, core_features_from_builtins, decl_payload_term_root_count,
    expr_from_term, level_from_node, name_to_string, reserved_core_primitive_name,
    source_decl_index_for_export_entry, universe_names, ImportedMaterializationAdmission,
    KernelExprMaterialization, KernelTermConversion, MaterializationAttempt, MaterializationStop,
    SelectedTermMaterializationPlan, TermMaterializationBudgetV1,
    TERM_PLANNER_NAME_COMPONENT_CHARGE_BYTES_V1, TERM_PLANNER_RECORD_CHARGE_BYTES_V1,
};
pub(crate) use local_transparency::{
    complete_local_transparency_dependencies, local_transparency_dependencies,
    validate_local_implementation_closure, validate_local_implementation_entries,
    LocalTransparencyBudget,
};
pub(crate) use structural::*;
pub(crate) use verify::*;

pub(crate) const FORMAT: &str = "NPA-CERT-0.4.0";
pub(crate) const CORE_SPEC: &str = "NPA-Core-0.4.0";
pub(crate) const DECL_CERT_DOMAIN: &[u8] = b"NPA-DECL-CERT-0.4.0";
pub(crate) const MODULE_EXPORT_DOMAIN: &[u8] = b"NPA-MODULE-EXPORT-0.2.0";
pub(crate) const MODULE_CERT_DOMAIN: &[u8] = b"NPA-MODULE-CERT-0.4.0";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(non_camel_case_types)]
pub(crate) enum CertificateFormatVersion {
    V0_4_0,
}

impl CertificateFormatVersion {
    pub(crate) fn encodes_export_universe_constraints(self) -> bool {
        true
    }

    pub(crate) fn encodes_tagged_dependencies(self) -> bool {
        true
    }

    pub(crate) fn declaration_certificate_domain(self) -> &'static [u8] {
        DECL_CERT_DOMAIN
    }

    pub(crate) fn module_certificate_domain(self) -> &'static [u8] {
        MODULE_CERT_DOMAIN
    }
}

pub(crate) fn certificate_format_version(header: &CertHeader) -> Result<CertificateFormatVersion> {
    if header.format == FORMAT && header.core_spec == CORE_SPEC {
        Ok(CertificateFormatVersion::V0_4_0)
    } else {
        Err(CertError::UnsupportedFormat {
            format: header.format.clone(),
            core_spec: header.core_spec.clone(),
        })
    }
}

/// Build a canonical module certificate from already elaborated core declarations.
///
/// `imports` must be `VerifiedModule` values returned by this crate's verifier. The resulting
/// certificate contains only trusted canonical payload: source maps, diagnostics, tactic traces,
/// and AI traces are not encoded or hashed.
pub fn build_module_cert(module: CoreModule, imports: &[VerifiedModule]) -> Result<ModuleCert> {
    build_module_cert_observed(module, imports, None)
}

/// Build a canonical module certificate and optionally observe its immutable payload allocation.
///
/// Errors and canonical bytes are identical to [`build_module_cert`]. The meter is updated only
/// after the complete certificate build succeeds.
pub fn build_module_cert_observed(
    module: CoreModule,
    imports: &[VerifiedModule],
    observation: Option<&mut CertificatePayloadObservation>,
) -> Result<ModuleCert> {
    canonical::build_module_cert_observed_impl(module, imports, observation)
}

/// Build a canonical module certificate from already elaborated core declarations and borrowed
/// verified imports.
///
/// This has the same trust requirements as `build_module_cert` but lets callers avoid cloning
/// large verified import closures when they already hold stable references.
pub fn build_module_cert_from_import_refs(
    module: CoreModule,
    imports: &[&VerifiedModule],
) -> Result<ModuleCert> {
    build_module_cert_from_import_refs_observed(module, imports, None)
}

/// Build from borrowed verified imports and optionally observe the frozen payload.
pub fn build_module_cert_from_import_refs_observed(
    module: CoreModule,
    imports: &[&VerifiedModule],
    observation: Option<&mut CertificatePayloadObservation>,
) -> Result<ModuleCert> {
    canonical::build_module_cert_from_import_refs_observed_impl(module, imports, observation)
}

/// Build a canonical module certificate with explicit providers for referenced imported names.
///
/// This has the same trust requirements as `build_module_cert_from_import_refs`. The preferred
/// provider map lets frontends preserve source-resolution identity when the broader certificate
/// import closure contains another module that exports the same public name.
pub fn build_module_cert_from_import_refs_with_preferred_imports(
    module: CoreModule,
    imports: &[&VerifiedModule],
    preferred_imports: &std::collections::BTreeMap<Name, ImportEntry>,
) -> Result<ModuleCert> {
    build_module_cert_from_import_refs_with_preferred_imports_observed(
        module,
        imports,
        preferred_imports,
        None,
    )
}

/// Build with preferred imported-name providers and optionally observe the frozen payload.
pub fn build_module_cert_from_import_refs_with_preferred_imports_observed(
    module: CoreModule,
    imports: &[&VerifiedModule],
    preferred_imports: &std::collections::BTreeMap<Name, ImportEntry>,
    observation: Option<&mut CertificatePayloadObservation>,
) -> Result<ModuleCert> {
    canonical::build_module_cert_from_import_refs_with_preferred_imports_observed_impl(
        module,
        imports,
        preferred_imports,
        observation,
    )
}

/// Encode a module certificate as the canonical `.npcert` binary representation.
///
/// The returned bytes are the exact bytes used by certificate verification and module hashing.
pub fn encode_module_cert(cert: &ModuleCert) -> Result<Vec<u8>> {
    binary::encode_module_cert_full_for_header(cert)
}

/// Decode a `.npcert` byte sequence into a syntactic certificate value.
///
/// This function does not trust or register the result. Use `verify_module_cert` to check
/// canonical encoding, hashes, imports, axiom policy, and kernel validity.
pub fn decode_module_cert(bytes: &[u8]) -> Result<ModuleCert> {
    decode_module_cert_observed(bytes, None)
}

/// Decode a certificate and optionally observe the immutable payload allocation.
///
/// This has the same validation and error order as [`decode_module_cert`]. The
/// optional meter is updated only after a complete decode succeeds.
pub fn decode_module_cert_observed(
    bytes: &[u8],
    observation: Option<&mut CertificatePayloadObservation>,
) -> Result<ModuleCert> {
    ensure_certificate_byte_limit(bytes)?;
    let mut decoder = binary::Decoder::new(bytes);
    let (parts, _) = decoder.module_cert_parts_with_import_offsets()?;
    if !decoder.is_done() {
        return Err(CertError::DecodeError);
    }
    Ok(ModuleCert::from_parts_observed(parts, observation))
}

/// Decode and validate only the exact certificate format/core header pair and module name.
///
/// This does not validate the remaining certificate payload. Callers may use it to construct
/// version-separated cache identities before performing full source-free verification.
pub fn decode_module_cert_header(bytes: &[u8]) -> Result<CertHeader> {
    ensure_certificate_byte_limit(bytes)?;
    binary::decode_module_cert_header(bytes)
}

/// Decode a certificate and return the byte offset of each import entry.
///
/// Offsets are ordered exactly like [`ModuleCert::imports`] and point to the
/// first byte of the corresponding encoded import. This is useful for callers
/// that must preserve precise import-resolution diagnostics.
pub fn decode_module_cert_with_import_offsets(bytes: &[u8]) -> Result<(ModuleCert, Vec<usize>)> {
    decode_module_cert_with_import_offsets_observed(bytes, None)
}

/// Decode a certificate with import offsets and optionally observe its immutable payload.
///
/// The existing decoder's bytes, offsets, error ordering, and limits are unchanged. The meter is
/// updated only after the complete certificate and all offsets have been decoded successfully.
pub fn decode_module_cert_with_import_offsets_observed(
    bytes: &[u8],
    observation: Option<&mut CertificatePayloadObservation>,
) -> Result<(ModuleCert, Vec<usize>)> {
    ensure_certificate_byte_limit(bytes)?;
    let mut decoder = binary::Decoder::new(bytes);
    let (parts, import_offsets) = decoder.module_cert_parts_with_import_offsets()?;
    if !decoder.is_done() {
        return Err(CertError::DecodeError);
    }
    Ok((
        ModuleCert::from_parts_observed(parts, observation),
        import_offsets,
    ))
}

/// Decode structural certificate data and report fixed-profile measurements.
///
/// This entry point performs bounded decoding and structural preflight only.
/// It does not verify canonical encoding, hashes, imports, axioms, or proofs,
/// and its result is never proof evidence.
pub fn audit_certificate_structural_limits(bytes: &[u8]) -> Result<CertificateStructuralAudit> {
    ensure_certificate_byte_limit(bytes)?;
    let mut decoder = binary::Decoder::new_for_structural_audit(bytes);
    let certificate = decoder.module_cert()?;
    if !decoder.is_done() {
        return Err(CertError::DecodeError);
    }
    structural_audit(
        &certificate,
        bytes.len(),
        decoder.audit_core_feature_count(),
    )
}

/// Validate fixed structural limits and canonical DAG reference order on an already decoded
/// certificate value.
///
/// This is a non-verifying admission check for consumers that receive a syntactic [`ModuleCert`]
/// capability rather than encoded bytes. It rejects oversized tables, invalid or cyclic table
/// references, excessive structural depth, and excessive semantic-root expansion. It does not
/// validate hashes, imports, axioms, or kernel semantics and is never proof evidence.
pub fn validate_decoded_module_cert_structural_limits(cert: &ModuleCert) -> Result<()> {
    structural_preflight(cert).map(|_| ())
}

/// Decode a canonical certificate and verify its stored structural hashes.
///
/// This checks canonical encoding, table structure, declaration and module
/// hashes, declaration order, and generated inductive artifacts. It does not
/// resolve imports, apply an axiom policy, type check declarations, or register
/// the result as verified proof evidence.
pub fn verify_module_cert_hashes(bytes: &[u8]) -> Result<ModuleCert> {
    verify::verify_module_cert_hashes_impl(bytes)
}

/// Verify a canonical module certificate and register the verified module in `session`.
///
/// Verification performs decode, canonical byte round-trip, hash recomputation, import resolution,
/// high-trust policy checks, axiom report recomputation, and Rust kernel checking over decoded
/// core declarations.
pub fn verify_module_cert(
    bytes: &[u8],
    session: &mut VerifierSession,
    policy: &AxiomPolicy,
) -> Result<VerifiedModule> {
    verify::verify_module_cert_impl(bytes, session, policy)
}

/// Verify a canonical module certificate against borrowed verified imports without registering
/// the result in a session.
///
/// This performs the same decode, canonical byte round-trip, hash recomputation, import
/// resolution, axiom policy enforcement, and kernel checking as `verify_module_cert`. It is for
/// one-shot verification paths that do not need a persistent `VerifierSession`.
pub fn verify_module_cert_with_import_refs(
    bytes: &[u8],
    imports: &[&VerifiedModule],
    policy: &AxiomPolicy,
) -> Result<VerifiedModule> {
    verify::verify_module_cert_with_import_refs_impl(bytes, imports, policy)
}

/// Verify a canonical module certificate with explicit out-of-band kernel
/// execution options.
///
/// Memo selection is not serialized and does not alter certificate, module,
/// import, or policy identities. [`npa_kernel::KernelExecutionOptions::default`]
/// retains the behavior of [`verify_module_cert_with_import_refs`].
pub fn verify_module_cert_with_import_refs_and_kernel_options(
    bytes: &[u8],
    imports: &[&VerifiedModule],
    policy: &AxiomPolicy,
    kernel_options: npa_kernel::KernelExecutionOptions,
) -> Result<VerifiedModule> {
    verify_module_cert_with_import_refs_and_kernel_options_and_observations(
        bytes,
        imports,
        policy,
        kernel_options,
        CertificateVerificationObservationSinks::new(),
    )
}

/// Verify canonical certificate bytes with explicit kernel options and
/// additive operation-local observation sinks.
pub fn verify_module_cert_with_import_refs_and_kernel_options_and_observations(
    bytes: &[u8],
    imports: &[&VerifiedModule],
    policy: &AxiomPolicy,
    kernel_options: npa_kernel::KernelExecutionOptions,
    observations: CertificateVerificationObservationSinks<'_>,
) -> Result<VerifiedModule> {
    verify::verify_module_cert_with_import_refs_and_options_and_observations_impl(
        bytes,
        imports,
        policy,
        kernel_options,
        observations,
    )
}

/// Verify a canonical module certificate with explicit kernel options while
/// aggregating deterministic work and memo/probe counters from the real
/// declaration-verification path.
pub fn verify_module_cert_with_import_refs_and_kernel_options_and_work_counters(
    bytes: &[u8],
    imports: &[&VerifiedModule],
    policy: &AxiomPolicy,
    kernel_options: npa_kernel::KernelExecutionOptions,
    work_counters: &mut npa_kernel::KernelWorkCounters,
) -> Result<VerifiedModule> {
    verify_module_cert_with_import_refs_and_kernel_options_and_observations(
        bytes,
        imports,
        policy,
        kernel_options,
        CertificateVerificationObservationSinks::new().with_kernel(work_counters),
    )
}

/// Verify an already decoded module certificate against borrowed verified imports.
///
/// This performs the same canonical byte round-trip, hash recomputation, import
/// resolution, axiom policy enforcement, and kernel checking as
/// `verify_module_cert_with_import_refs`. It is for build paths that just
/// produced a `ModuleCert` and need to avoid decoding the freshly encoded bytes
/// back into a second certificate value.
pub fn verify_decoded_module_cert_with_import_refs(
    cert: &ModuleCert,
    bytes: &[u8],
    imports: &[&VerifiedModule],
    policy: &AxiomPolicy,
) -> Result<VerifiedModule> {
    verify::verify_decoded_module_cert_with_import_refs_impl(cert, bytes, imports, policy)
}

/// Verify an already decoded certificate with explicit out-of-band kernel
/// execution options.
///
/// This preserves the canonical byte comparison and all policy checks of
/// [`verify_decoded_module_cert_with_import_refs`]. Memo state is created and
/// dropped independently for each kernel declaration operation.
pub fn verify_decoded_module_cert_with_import_refs_and_kernel_options(
    cert: &ModuleCert,
    bytes: &[u8],
    imports: &[&VerifiedModule],
    policy: &AxiomPolicy,
    kernel_options: npa_kernel::KernelExecutionOptions,
) -> Result<VerifiedModule> {
    verify_decoded_module_cert_with_import_refs_and_kernel_options_and_observations(
        cert,
        bytes,
        imports,
        policy,
        kernel_options,
        CertificateVerificationObservationSinks::new(),
    )
}

/// Verify an already decoded certificate with explicit kernel options and
/// additive operation-local observation sinks.
pub fn verify_decoded_module_cert_with_import_refs_and_kernel_options_and_observations(
    cert: &ModuleCert,
    bytes: &[u8],
    imports: &[&VerifiedModule],
    policy: &AxiomPolicy,
    kernel_options: npa_kernel::KernelExecutionOptions,
    observations: CertificateVerificationObservationSinks<'_>,
) -> Result<VerifiedModule> {
    verify::verify_decoded_module_cert_with_import_refs_and_options_and_observations_impl(
        cert,
        bytes,
        imports,
        policy,
        kernel_options,
        observations,
    )
}

/// Verify a retained decoded certificate against borrowed imports.
///
/// This is the opaque-capability counterpart of
/// [`verify_decoded_module_cert_with_import_refs`]. It does not expose the
/// decoded certificate to the caller and preserves the same canonical-byte,
/// import, policy, and kernel checks.
pub fn verify_retained_decoded_module_cert_with_import_refs(
    cert: &RetainedDecodedModuleCert,
    bytes: &[u8],
    imports: &[&VerifiedModule],
    policy: &AxiomPolicy,
) -> Result<VerifiedModule> {
    verify_decoded_module_cert_with_import_refs(cert.module(), bytes, imports, policy)
}

/// Verify a retained decoded certificate with explicit kernel options.
pub fn verify_retained_decoded_module_cert_with_import_refs_and_kernel_options(
    cert: &RetainedDecodedModuleCert,
    bytes: &[u8],
    imports: &[&VerifiedModule],
    policy: &AxiomPolicy,
    kernel_options: npa_kernel::KernelExecutionOptions,
) -> Result<VerifiedModule> {
    verify_retained_decoded_module_cert_with_import_refs_and_kernel_options_and_observations(
        cert,
        bytes,
        imports,
        policy,
        kernel_options,
        CertificateVerificationObservationSinks::new(),
    )
}

/// Verify a retained decoded certificate with explicit options and additive
/// operation-local observation sinks.
pub fn verify_retained_decoded_module_cert_with_import_refs_and_kernel_options_and_observations(
    cert: &RetainedDecodedModuleCert,
    bytes: &[u8],
    imports: &[&VerifiedModule],
    policy: &AxiomPolicy,
    kernel_options: npa_kernel::KernelExecutionOptions,
    observations: CertificateVerificationObservationSinks<'_>,
) -> Result<VerifiedModule> {
    verify_decoded_module_cert_with_import_refs_and_kernel_options_and_observations(
        cert.module(),
        bytes,
        imports,
        policy,
        kernel_options,
        observations,
    )
}

/// Verify a freshly built module certificate against borrowed verified imports.
///
/// This is for callers that just obtained a `ModuleCert` from this crate's canonical
/// certificate builder and will encode the returned certificate afterward. Persisted
/// source-free bytes must still use `verify_module_cert` or
/// `verify_module_cert_with_import_refs`, which decode and compare canonical bytes.
pub fn verify_built_module_cert_with_import_refs(
    cert: &ModuleCert,
    imports: &[&VerifiedModule],
    policy: &AxiomPolicy,
) -> Result<VerifiedModule> {
    verify::verify_built_module_cert_with_import_refs_impl(cert, imports, policy)
}

/// Verify a freshly built certificate with explicit out-of-band kernel
/// execution options.
///
/// Persisted bytes must continue to use a byte-verifying entry point. The
/// options select only operation-local execution behavior and never enter the
/// certificate identity.
pub fn verify_built_module_cert_with_import_refs_and_kernel_options(
    cert: &ModuleCert,
    imports: &[&VerifiedModule],
    policy: &AxiomPolicy,
    kernel_options: npa_kernel::KernelExecutionOptions,
) -> Result<VerifiedModule> {
    verify_built_module_cert_with_import_refs_and_kernel_options_and_observations(
        cert,
        imports,
        policy,
        kernel_options,
        CertificateVerificationObservationSinks::new(),
    )
}

/// Verify a freshly built certificate with explicit kernel options and
/// additive operation-local observation sinks.
///
/// Built input is already frozen, so merely verifying it never records a new
/// payload allocation. Kernel and term observations describe only the live
/// verification work performed by this call.
pub fn verify_built_module_cert_with_import_refs_and_kernel_options_and_observations(
    cert: &ModuleCert,
    imports: &[&VerifiedModule],
    policy: &AxiomPolicy,
    kernel_options: npa_kernel::KernelExecutionOptions,
    observations: CertificateVerificationObservationSinks<'_>,
) -> Result<VerifiedModule> {
    verify::verify_built_module_cert_with_import_refs_and_options_and_observations_impl(
        cert,
        imports,
        policy,
        kernel_options,
        observations,
    )
}

/// Verify an already decoded module certificate against its canonical byte source.
///
/// This helper is for process-local decode caches. It still compares the
/// canonical encoding of `cert` against `bytes`, recomputes hashes, resolves
/// imports, enforces policy, and runs the Rust kernel checker before registering
/// the module in `session`.
pub fn verify_decoded_module_cert(
    cert: &ModuleCert,
    bytes: &[u8],
    session: &mut VerifierSession,
    policy: &AxiomPolicy,
) -> Result<VerifiedModule> {
    verify_decoded_module_cert_with_observations(
        cert,
        bytes,
        session,
        policy,
        CertificateVerificationObservationSinks::new(),
    )
}

/// Verify and register an already decoded certificate while collecting
/// additive operation-local observations.
pub fn verify_decoded_module_cert_with_observations(
    cert: &ModuleCert,
    bytes: &[u8],
    session: &mut VerifierSession,
    policy: &AxiomPolicy,
    observations: CertificateVerificationObservationSinks<'_>,
) -> Result<VerifiedModule> {
    verify::verify_decoded_module_cert_with_observations_impl(
        cert,
        bytes,
        session,
        policy,
        observations,
    )
}

/// Verify and register a retained decoded certificate without exposing its
/// underlying syntax value.
pub fn verify_retained_decoded_module_cert(
    cert: &RetainedDecodedModuleCert,
    bytes: &[u8],
    session: &mut VerifierSession,
    policy: &AxiomPolicy,
) -> Result<VerifiedModule> {
    verify_retained_decoded_module_cert_with_observations(
        cert,
        bytes,
        session,
        policy,
        CertificateVerificationObservationSinks::new(),
    )
}

/// Verify and register a retained decoded certificate while collecting
/// additive operation-local observations.
pub fn verify_retained_decoded_module_cert_with_observations(
    cert: &RetainedDecodedModuleCert,
    bytes: &[u8],
    session: &mut VerifierSession,
    policy: &AxiomPolicy,
    observations: CertificateVerificationObservationSinks<'_>,
) -> Result<VerifiedModule> {
    verify_decoded_module_cert_with_observations(
        cert.module(),
        bytes,
        session,
        policy,
        observations,
    )
}

/// Return the canonical structural hash for a term table entry in a module certificate.
///
/// The hash is computed from the term structure and referenced level hashes, not from the table
/// index itself.
pub fn term_hash(cert: &ModuleCert, term: TermId) -> Result<Hash> {
    hash::term_hash_impl(cert, term)
}

/// Return canonical bytes for a raw kernel expression.
///
/// This is the kernel core expression view used by higher-level machine APIs before a term is
/// embedded in a certificate module and resolved to certificate `GlobalRef`s.
pub fn core_expr_canonical_bytes(expr: &npa_kernel::Expr) -> Vec<u8> {
    hash::core_expr_canonical_bytes_impl(expr)
}

/// Return the canonical structural hash for a raw kernel expression.
///
/// This hash is computed from [`core_expr_canonical_bytes`] and ignores display-only binder names.
pub fn core_expr_hash(expr: &npa_kernel::Expr) -> Hash {
    hash::core_expr_hash_impl(expr)
}

/// Return canonical bytes for a declaration universe context.
///
/// The input must use sorted, unique universe parameters and normalized constraint levels. The
/// bytes are independent of certificate table indexes and reject unresolved/meta-like universe
/// encodings because the kernel level grammar has no meta constructor.
pub fn universe_constraints_canonical_bytes(
    universe_params: &[String],
    constraints: &[npa_kernel::UniverseConstraint],
) -> Result<Vec<u8>> {
    hash::universe_constraints_canonical_bytes_impl(universe_params, constraints)
}

/// Return the deterministic structural hash for a declaration universe context.
pub fn universe_constraints_hash(
    universe_params: &[String],
    constraints: &[npa_kernel::UniverseConstraint],
) -> Result<Hash> {
    hash::universe_constraints_hash_impl(universe_params, constraints)
}

#[cfg(test)]
mod validation_reuse_allocation_meter {
    use std::alloc::{GlobalAlloc, Layout, System};
    use std::cell::Cell;

    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
    pub(crate) struct Snapshot {
        pub(crate) allocation_events: u64,
        pub(crate) allocated_bytes: u64,
    }

    #[derive(Clone, Copy)]
    struct State {
        active: bool,
        snapshot: Snapshot,
    }

    thread_local! {
        static STATE: Cell<State> = const { Cell::new(State {
            active: false,
            snapshot: Snapshot {
                allocation_events: 0,
                allocated_bytes: 0,
            },
        }) };
    }

    pub(crate) struct TrackingSystem;

    #[global_allocator]
    static ALLOCATOR: TrackingSystem = TrackingSystem;

    fn record(requested_bytes: usize) {
        let _ = STATE.try_with(|state| {
            let mut current = state.get();
            if current.active {
                current.snapshot.allocation_events =
                    current.snapshot.allocation_events.saturating_add(1);
                current.snapshot.allocated_bytes = current
                    .snapshot
                    .allocated_bytes
                    .saturating_add(u64::try_from(requested_bytes).unwrap_or(u64::MAX));
                state.set(current);
            }
        });
    }

    unsafe impl GlobalAlloc for TrackingSystem {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            let pointer = unsafe { System.alloc(layout) };
            if !pointer.is_null() {
                record(layout.size());
            }
            pointer
        }

        unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
            let pointer = unsafe { System.alloc_zeroed(layout) };
            if !pointer.is_null() {
                record(layout.size());
            }
            pointer
        }

        unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
            let new_pointer = unsafe { System.realloc(pointer, layout, new_size) };
            if !new_pointer.is_null() {
                record(new_size);
            }
            new_pointer
        }

        unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
            unsafe { System.dealloc(pointer, layout) }
        }
    }

    pub(crate) fn reset_and_start() {
        STATE.with(|state| {
            state.set(State {
                active: true,
                snapshot: Snapshot::default(),
            });
        });
    }

    pub(crate) fn stop() -> Snapshot {
        STATE.with(|state| {
            let mut current = state.get();
            current.active = false;
            state.set(current);
            current.snapshot
        })
    }

    #[cfg(test)]
    pub(crate) fn set_for_saturation_test(snapshot: Snapshot) {
        STATE.with(|state| {
            state.set(State {
                active: true,
                snapshot,
            });
        });
    }
}

#[cfg(test)]
mod tests;

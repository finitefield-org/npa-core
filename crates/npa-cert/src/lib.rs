//! Canonical certificate construction, hashing, encoding, and verification.
//!
//! This crate treats parser, elaborator, tactics, and automation output as untrusted. Its public
//! API accepts already elaborated kernel declarations, emits deterministic canonical certificates,
//! and verifies only canonical certificate bytes against the small Rust kernel.

#![deny(missing_docs)]

mod binary;
mod canonical;
mod hash;
mod inductive;
mod kernel;
mod producer;
mod types;
mod verify;

pub use inductive::{
    classify_inductive_artifact_profile_v1, generate_inductive_artifacts_v1,
    generate_mutual_inductive_artifacts_v1, inductive_generated_artifact_hashes_v1,
    InductiveArtifactProfileCheckV1, InductiveGeneratedArtifactHashesV1,
    UnsupportedMvpRecursorProfileV1,
};
pub use kernel::{builtin_decl_interface_hash, verified_module_to_kernel_decls};
pub use producer::*;
pub use types::*;

pub(crate) use binary::*;
pub(crate) use canonical::*;
pub(crate) use hash::*;
pub(crate) use kernel::{
    add_decl_to_env, add_referenced_builtins_to_env, builtin_is_axiom, cert_decl_to_kernel_decl,
    core_features_from_builtins, expr_from_term, level_from_node, name_to_string,
    reserved_core_primitive_name, source_decl_index_for_export_entry, universe_names,
    verified_module_export_entry_to_kernel_decl, verified_module_referenced_builtin_names,
};
pub(crate) use verify::*;

pub(crate) const FORMAT: &str = "NPA-CERT-0.2.0";
pub(crate) const CORE_SPEC: &str = "NPA-Core-0.2.0";
pub(crate) const PREVIOUS_FORMAT: &str = "NPA-CERT-0.1.2";
pub(crate) const PREVIOUS_CORE_SPEC: &str = "NPA-Core-0.1.2";
pub(crate) const LEGACY_FORMAT: &str = "NPA-CERT-0.1";
pub(crate) const LEGACY_CORE_SPEC: &str = "NPA-Core-0.1";
pub(crate) const MODULE_EXPORT_DOMAIN: &[u8] = b"NPA-MODULE-EXPORT-0.2.0";
pub(crate) const MODULE_CERT_DOMAIN: &[u8] = b"NPA-MODULE-CERT-0.2.0";
pub(crate) const PREVIOUS_MODULE_EXPORT_DOMAIN: &[u8] = b"NPA-MODULE-EXPORT-0.1.2";
pub(crate) const PREVIOUS_MODULE_CERT_DOMAIN: &[u8] = b"NPA-MODULE-CERT-0.1.2";
pub(crate) const LEGACY_MODULE_EXPORT_DOMAIN: &[u8] = b"NPA-MODULE-EXPORT-0.1";
pub(crate) const LEGACY_MODULE_CERT_DOMAIN: &[u8] = b"NPA-MODULE-CERT-0.1";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CertificateFormatVersion {
    Current,
    Previous,
    Legacy,
}

impl CertificateFormatVersion {
    pub(crate) fn encodes_export_universe_constraints(self) -> bool {
        self != Self::Legacy
    }
}

pub(crate) fn certificate_format_version(header: &CertHeader) -> Result<CertificateFormatVersion> {
    if header.format == FORMAT && header.core_spec == CORE_SPEC {
        Ok(CertificateFormatVersion::Current)
    } else if header.format == PREVIOUS_FORMAT && header.core_spec == PREVIOUS_CORE_SPEC {
        Ok(CertificateFormatVersion::Previous)
    } else if header.format == LEGACY_FORMAT && header.core_spec == LEGACY_CORE_SPEC {
        Ok(CertificateFormatVersion::Legacy)
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
    canonical::build_module_cert_impl(module, imports)
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
    canonical::build_module_cert_from_import_refs_impl(module, imports)
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
    let mut decoder = binary::Decoder::new(bytes);
    let cert = decoder.module_cert()?;
    if !decoder.is_done() {
        return Err(CertError::DecodeError);
    }
    Ok(cert)
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
    verify::verify_decoded_module_cert_impl(cert, bytes, session, policy)
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
mod tests;

use std::collections::{BTreeMap, BTreeSet};

use npa_kernel::{Ctx, Decl, Env, Error, Expr, Level};

use crate::{
    encode_axiom_refs_to, encode_name_to, encode_uvar_to, hash_with_domain, union_axioms, AxiomRef,
    CertError, CoreModule, DeclHashes, ExportEntry, Hash, ModuleCert, ModuleName,
    ProducerLimitKind, ProducerTokenHashField, VerifiedModule,
};

/// Sidecar-only producer classification for audit and diagnostics.
///
/// This profile is intentionally not accepted by certificate construction or verification APIs.
///
/// ```compile_fail
/// use npa_cert::{build_module_cert, ProducerProfile};
///
/// let _ = build_module_cert(ProducerProfile::AiCoreMvp, &[]);
/// ```
///
/// ```compile_fail
/// use npa_cert::{verify_module_cert, ProducerProfile, VerifierSession};
///
/// let mut session = VerifierSession::new();
/// let _ = verify_module_cert(&[], &mut session, &ProducerProfile::AiCoreMvp);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProducerProfile {
    /// Human-facing surface-language producer.
    HumanSurface,
    /// AI-facing MVP core declaration producer.
    AiCoreMvp,
}

/// Deterministic resource limits for producer candidate checking.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProducerLimits {
    /// Maximum declarations accepted in a candidate batch.
    pub max_declarations: u32,
    /// Maximum expression nodes accepted in a candidate declaration.
    pub max_expr_nodes: u32,
    /// Maximum level nodes accepted in a candidate declaration.
    pub max_level_nodes: u32,
    /// Maximum dotted-name components accepted in a candidate declaration.
    pub max_name_components: u32,
    /// Maximum reduction steps available to candidate checking.
    pub max_reduction_steps: u64,
    /// Maximum conversion steps available to candidate checking.
    pub max_conversion_steps: u64,
}

/// Return canonical bytes for a producer limit profile.
///
/// Fields are encoded in [`ProducerLimits`] declaration order, and each numeric field uses the
/// same minimal ULEB128 encoding as certificate canonical binary.
pub fn producer_limits_canonical_bytes(limits: &ProducerLimits) -> Vec<u8> {
    let mut out = Vec::new();
    encode_uvar_to(&mut out, u64::from(limits.max_declarations));
    encode_uvar_to(&mut out, u64::from(limits.max_expr_nodes));
    encode_uvar_to(&mut out, u64::from(limits.max_level_nodes));
    encode_uvar_to(&mut out, u64::from(limits.max_name_components));
    encode_uvar_to(&mut out, limits.max_reduction_steps);
    encode_uvar_to(&mut out, limits.max_conversion_steps);
    out
}

/// Return the canonical hash for a producer limit profile.
pub fn producer_limits_hash(limits: &ProducerLimits) -> Hash {
    hash_with_domain(
        b"NPA-PRODUCER-LIMITS-0.1",
        &producer_limits_canonical_bytes(limits),
    )
}

/// Return whether limit profile `a` is at least as strict as profile `b`.
///
/// A profile is stricter-or-equal only when every field is less than or equal to the corresponding
/// field in `b`.
pub fn stricter_or_equal(a: &ProducerLimits, b: &ProducerLimits) -> bool {
    a.max_declarations <= b.max_declarations
        && a.max_expr_nodes <= b.max_expr_nodes
        && a.max_level_nodes <= b.max_level_nodes
        && a.max_name_components <= b.max_name_components
        && a.max_reduction_steps <= b.max_reduction_steps
        && a.max_conversion_steps <= b.max_conversion_steps
}

/// Public-environment key for a producer direct import.
///
/// This key intentionally excludes the imported certificate hash. Two imports with the same module
/// and export hash expose the same downstream kernel environment even if their proof bodies, and
/// therefore full certificate hashes, differ.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ProducerImportEnvKey {
    /// Imported module name.
    pub module: ModuleName,
    /// Imported module export hash.
    pub export_hash: Hash,
}

/// Return the producer public-environment key for a verified import.
pub fn producer_import_env_key(import: &VerifiedModule) -> ProducerImportEnvKey {
    ProducerImportEnvKey {
        module: import.module().clone(),
        export_hash: import.export_hash(),
    }
}

/// Validate `batch.imports` order and return import environment keys in import-index order.
///
/// The accepted order is the same canonical order used by module certificate imports:
/// `(module, export_hash, Some(certificate_hash))`. The returned vector preserves the input order,
/// so later `GlobalRef::Imported(import_index, ...)` lookups continue to point at
/// `batch.imports[import_index]`.
pub fn validate_candidate_batch_imports(
    batch: &CandidateBatch<'_>,
) -> Result<Vec<ProducerImportEnvKey>, CertError> {
    canonical_import_env_keys(batch.imports)
}

/// Validate canonical direct-import order and return producer import keys in the same order.
pub fn canonical_import_env_keys(
    imports: &[VerifiedModule],
) -> Result<Vec<ProducerImportEnvKey>, CertError> {
    let mut seen = BTreeSet::new();
    let mut keys = Vec::with_capacity(imports.len());
    for import in imports {
        let key = producer_import_env_key(import);
        if !seen.insert(key.clone()) {
            return Err(CertError::DuplicateImportEnvKey {
                module: key.module,
                export_hash: key.export_hash,
            });
        }
        keys.push(key);
    }

    if !imports
        .windows(2)
        .all(|pair| verified_import_order_key(&pair[0]) < verified_import_order_key(&pair[1]))
    {
        return Err(CertError::NonCanonicalEncoding { object: "Imports" });
    }

    Ok(keys)
}

/// Export lookup view for one producer direct import.
///
/// Unlike [`ProducerImportEnvKey`], this view keeps the verified import's exported declarations and
/// name table so imported axiom dependencies can be recomputed from checked certificate data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProducerImportExportView {
    /// Imported module name.
    pub module: ModuleName,
    /// Imported module export hash.
    pub export_hash: Hash,
    /// Imported module name table used by export entries and axiom refs.
    pub name_table: Vec<ModuleName>,
    /// Imported module public export entries.
    pub exports: Vec<ExportEntry>,
}

/// Validate canonical direct-import order and return export lookup views in the same order.
pub fn canonical_import_export_views(
    imports: &[VerifiedModule],
) -> Result<Vec<ProducerImportExportView>, CertError> {
    canonical_import_env_keys(imports)?;
    Ok(imports
        .iter()
        .map(|import| ProducerImportExportView {
            module: import.module().clone(),
            export_hash: import.export_hash(),
            name_table: import.name_table().to_vec(),
            exports: import.export_block().to_vec(),
        })
        .collect())
}

/// Public checked declaration interface committed by the producer environment fingerprint.
///
/// Declaration identity is represented by `decl_interface_hash`; exact proof or opaque body
/// identity belongs to checked candidate token hashes and prior-chain fingerprints, not to the
/// producer public environment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProducerCheckedDeclInterface {
    /// Declaration interface hash.
    pub decl_interface_hash: Hash,
    /// Transitive axiom dependencies for this declaration.
    pub axiom_dependencies: Vec<AxiomRef>,
}

/// Canonical producer public environment fingerprint input.
///
/// `direct_imports` must already be in canonical import order. `checked_decls` order is meaningful
/// and follows accepted current-module declaration order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProducerEnvFingerprintBytes {
    /// Direct import public-environment keys in canonical import order.
    pub direct_imports: Vec<ProducerImportEnvKey>,
    /// Checked current-module declaration interfaces in accepted order.
    pub checked_decls: Vec<ProducerCheckedDeclInterface>,
}

/// One exact checked declaration token entry committed by the prior-chain fingerprint.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProducerPriorChainEntry {
    /// Declaration interface hash for public environment identity.
    pub decl_interface_hash: Hash,
    /// Declaration certificate hash for exact proof/body identity.
    pub decl_certificate_hash: Hash,
    /// Producer environment fingerprint before this declaration was accepted.
    pub pre_env_fingerprint: Hash,
    /// Producer environment fingerprint after this declaration was accepted.
    pub post_env_fingerprint: Hash,
}

/// Canonical producer prior-chain fingerprint input.
///
/// `checked_decls` order is the accepted current-module declaration token order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProducerPriorChainBytes {
    /// Exact checked declaration token entries in accepted order.
    pub checked_decls: Vec<ProducerPriorChainEntry>,
}

/// Producer lookup environment for dependency and axiom recomputation.
///
/// `import_exports` has the same order as `CandidateBatch.imports` and
/// [`canonical_import_env_keys`]. `checked_decls` has the accepted current-module declaration
/// order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProducerLookupEnv {
    /// Export views for direct imports in canonical import order.
    pub import_exports: Vec<ProducerImportExportView>,
    /// Checked current-module declaration interfaces in accepted order.
    pub checked_decls: Vec<ProducerCheckedDeclInterface>,
    pub(crate) checked_decl_names: Vec<ModuleName>,
    pub(crate) checked_generated_name_to_index: BTreeMap<ModuleName, usize>,
}

/// Build a producer lookup environment from canonical imports and checked declaration interfaces.
pub fn producer_lookup_env(
    imports: &[VerifiedModule],
    checked_decls: &[ProducerCheckedDeclInterface],
) -> Result<ProducerLookupEnv, CertError> {
    Ok(ProducerLookupEnv {
        import_exports: canonical_import_export_views(imports)?,
        checked_decls: checked_decls.to_vec(),
        checked_decl_names: vec![],
        checked_generated_name_to_index: BTreeMap::new(),
    })
}

/// Recompute the producer checked declaration interface from canonical lookup data.
pub fn producer_checked_decl_interface(
    decl: &Decl,
    lookup_env: &ProducerLookupEnv,
) -> Result<ProducerCheckedDeclInterface, CertError> {
    crate::canonical_producer_checked_decl_interface(decl, lookup_env)
}

/// Return canonical bytes for a producer public environment fingerprint input.
pub fn producer_env_fingerprint_canonical_bytes(env: &ProducerEnvFingerprintBytes) -> Vec<u8> {
    let mut out = Vec::new();
    encode_uvar_to(&mut out, env.direct_imports.len() as u64);
    for import in &env.direct_imports {
        encode_name_to(&mut out, &import.module);
        out.extend(import.export_hash);
    }
    encode_uvar_to(&mut out, env.checked_decls.len() as u64);
    for checked in &env.checked_decls {
        out.extend(checked.decl_interface_hash);
        let axioms = union_axioms(checked.axiom_dependencies.iter().cloned());
        encode_axiom_refs_to(&mut out, &axioms);
    }
    out
}

/// Return the canonical producer public environment fingerprint.
pub fn producer_env_fingerprint(env: &ProducerEnvFingerprintBytes) -> Hash {
    hash_with_domain(
        b"NPA-PRODUCER-ENV-0.1",
        &producer_env_fingerprint_canonical_bytes(env),
    )
}

/// Return canonical bytes for a producer prior-chain fingerprint input.
pub fn prior_chain_fingerprint_canonical_bytes(chain: &ProducerPriorChainBytes) -> Vec<u8> {
    let mut out = Vec::new();
    encode_uvar_to(&mut out, chain.checked_decls.len() as u64);
    for entry in &chain.checked_decls {
        out.extend(entry.decl_interface_hash);
        out.extend(entry.decl_certificate_hash);
        out.extend(entry.pre_env_fingerprint);
        out.extend(entry.post_env_fingerprint);
    }
    out
}

/// Return the canonical producer prior-chain fingerprint.
pub fn prior_chain_fingerprint(chain: &ProducerPriorChainBytes) -> Hash {
    hash_with_domain(
        b"NPA-PRODUCER-CHAIN-0.1",
        &prior_chain_fingerprint_canonical_bytes(chain),
    )
}

/// Recompute the initial producer public environment fingerprint from canonical imports.
pub fn initial_env_fingerprint(imports: &[VerifiedModule]) -> Result<Hash, CertError> {
    Ok(producer_env_fingerprint(&ProducerEnvFingerprintBytes {
        direct_imports: canonical_import_env_keys(imports)?,
        checked_decls: vec![],
    }))
}

/// Recompute the producer public environment fingerprint after accepting `decl`.
///
/// This intentionally rebuilds the complete fingerprint input from imports and checked declaration
/// interfaces instead of appending to a previous fingerprint value.
pub fn post_env_fingerprint(
    imports: &[VerifiedModule],
    checked_decls_before: &[ProducerCheckedDeclInterface],
    decl: &Decl,
) -> Result<Hash, CertError> {
    let direct_imports = canonical_import_env_keys(imports)?;
    let lookup_env = producer_lookup_env(imports, checked_decls_before)?;
    let mut checked_decls = checked_decls_before.to_vec();
    checked_decls.push(producer_checked_decl_interface(decl, &lookup_env)?);

    Ok(producer_env_fingerprint(&ProducerEnvFingerprintBytes {
        direct_imports,
        checked_decls,
    }))
}

/// Validate reusable current-module declaration tokens for a producer batch.
///
/// Invalid prior tokens are rejected at the batch boundary because later candidates would otherwise
/// be checked against a forged producer environment.
pub fn validate_prior_current_decls(
    batch: &CandidateBatch<'_>,
) -> Result<Vec<ProducerCheckedDeclInterface>, CertError> {
    Ok(validate_checked_decl_chain(
        batch.imports,
        batch.prior_current_decls,
        Some(&batch.limits),
    )?
    .checked_decls)
}

/// Build a canonical module certificate from an exact sequence of checked producer tokens.
///
/// This API revalidates the token chain against `imports`, recomputes producer environment
/// fingerprints, prior-chain fingerprints, limit-profile hashes, and private declaration hashes,
/// then constructs a `CoreModule` internally and calls [`crate::build_module_cert`]. It does not
/// perform any new `ProducerLimits` strictness comparison; that check is only for reusing prior
/// tokens inside [`check_core_decl_candidates`].
pub fn build_module_cert_from_checked_candidates(
    module_name: ModuleName,
    imports: &[VerifiedModule],
    checked_decls: &[CheckedDeclCandidate],
) -> Result<ModuleCert, CertError> {
    let chain = validate_checked_decl_chain(imports, checked_decls, None)?;
    crate::build_module_cert(
        CoreModule {
            name: module_name,
            declarations: chain.declarations,
        },
        imports,
    )
}

/// Precheck a single producer candidate against an existing kernel environment under limits.
///
/// This fast path does not emit `.npcert` bytes or create a verified module. It only performs
/// deterministic schema limit checks and a metered kernel precheck for source declarations that
/// the AI producer MVP is allowed to submit directly.
pub fn precheck_core_decl_candidate(
    env: &Env,
    candidate: &CoreDeclCandidate,
    limits: &ProducerLimits,
) -> Result<(), CertError> {
    ensure_candidate_schema_limits(&candidate.declaration, limits)?;
    let mut whnf_fuel = fuel_to_usize(
        limits.max_reduction_steps,
        ProducerLimitKind::MaxReductionSteps,
    )?;
    let mut conversion_fuel = fuel_to_usize(
        limits.max_conversion_steps,
        ProducerLimitKind::MaxConversionSteps,
    )?;
    precheck_decl_with_fuel(
        env,
        &candidate.declaration,
        &mut whnf_fuel,
        &mut conversion_fuel,
    )
}

/// Check a batch of core declaration candidates without producing certificate bytes.
///
/// Batch-level structural failures return `Err(CertError)`. Candidate-local failures are reported
/// as [`CandidateStatus::Rejected`] at the same input index.
pub fn check_core_decl_candidates(
    batch: CandidateBatch<'_>,
) -> Result<CandidateBatchResult, CertError> {
    ensure_candidate_batch_schema(&batch)?;
    let direct_imports = validate_candidate_batch_imports(&batch)?;
    let mut checked_decls = validate_prior_current_decls(&batch)?;
    let prior_decl_sources: Vec<_> = batch
        .prior_current_decls
        .iter()
        .map(|token| token.declaration.clone())
        .collect();
    let mut prior_chain_entries: Vec<_> = batch
        .prior_current_decls
        .iter()
        .map(|token| ProducerPriorChainEntry {
            decl_interface_hash: token.decl_interface_hash,
            decl_certificate_hash: token.decl_certificate_hash,
            pre_env_fingerprint: token.pre_env_fingerprint,
            post_env_fingerprint: token.post_env_fingerprint,
        })
        .collect();
    let mut current_env_fingerprint = producer_env_fingerprint(&ProducerEnvFingerprintBytes {
        direct_imports: direct_imports.clone(),
        checked_decls: checked_decls.clone(),
    });
    let mut env = producer_base_env(batch.imports)?;
    let mut added_prior_sources = Vec::with_capacity(batch.prior_current_decls.len());
    for token in batch.prior_current_decls {
        add_referenced_builtins_for_decl(
            &mut env,
            batch.imports,
            &added_prior_sources,
            &token.declaration,
        )?;
        crate::add_decl_to_env(&mut env, token.declaration.clone())?;
        added_prior_sources.push(token.declaration.clone());
    }
    let mut checked_decl_sources = prior_decl_sources;

    let mut statuses = Vec::with_capacity(batch.candidates.len());
    for candidate in &batch.candidates {
        match check_candidate_in_batch(
            CandidateCheckContext {
                env: &env,
                imports: batch.imports,
                direct_imports: &direct_imports,
                checked_decls: &checked_decls,
                checked_decl_sources: &checked_decl_sources,
                prior_chain_entries: &prior_chain_entries,
                pre_env_fingerprint: current_env_fingerprint,
                limits: &batch.limits,
            },
            candidate,
        ) {
            Ok(accepted) => {
                env = accepted.env;
                checked_decls.push(accepted.interface);
                checked_decl_sources.push(accepted.declaration);
                prior_chain_entries.push(accepted.prior_chain_entry);
                current_env_fingerprint = accepted.post_env_fingerprint;
                statuses.push(CandidateStatus::Accepted(accepted.token));
            }
            Err(err) => statuses.push(CandidateStatus::Rejected(err)),
        }
    }

    Ok(CandidateBatchResult { statuses })
}

/// Untrusted core declaration candidate submitted by a producer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoreDeclCandidate {
    /// Already elaborated kernel declaration proposed by the producer.
    pub declaration: Decl,
}

/// Batch of untrusted core declaration candidates checked against a current environment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CandidateBatch<'a> {
    /// Verified imports available to the candidate batch.
    pub imports: &'a [VerifiedModule],
    /// Previously checked current-module declarations available to later candidates.
    pub prior_current_decls: &'a [CheckedDeclCandidate],
    /// Candidate declarations to check, in input order.
    pub candidates: Vec<CoreDeclCandidate>,
    /// Deterministic resource limits applied to this batch.
    pub limits: ProducerLimits,
}

/// Opaque token for a candidate declaration accepted by producer checking.
///
/// The token has no public constructor and exposes no raw declaration getter. Later producer
/// milestones construct this token only after candidate checking has recomputed its private hashes
/// and fingerprints.
///
/// ```compile_fail
/// use npa_cert::{CandidateHashPreview, CheckedDeclCandidate, ProducerLimits};
/// use npa_kernel::{Decl, Expr, Level};
///
/// let declaration = Decl::Axiom {
///     name: "P".to_owned(),
///     universe_params: vec![],
///     ty: Expr::sort(Level::zero()),
/// };
/// let zero = [0_u8; 32];
/// let limits = ProducerLimits {
///     max_declarations: 1,
///     max_expr_nodes: 1,
///     max_level_nodes: 1,
///     max_name_components: 1,
///     max_reduction_steps: 1,
///     max_conversion_steps: 1,
/// };
///
/// let _token = CheckedDeclCandidate {
///     declaration,
///     preview_hashes: CandidateHashPreview {
///         type_hash: None,
///         body_hash: None,
///         decl_interface_hash: None,
///         decl_certificate_hash: None,
///     },
///     pre_env_fingerprint: zero,
///     post_env_fingerprint: zero,
///     prior_chain_fingerprint: zero,
///     limits,
///     limit_profile_hash: zero,
///     decl_interface_hash: zero,
///     decl_certificate_hash: zero,
/// };
/// ```
///
/// ```compile_fail
/// use npa_cert::CheckedDeclCandidate;
///
/// fn leak_raw_declaration(token: CheckedDeclCandidate) {
///     let _ = token.declaration;
/// }
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedDeclCandidate {
    declaration: Decl,
    preview_hashes: CandidateHashPreview,
    pre_env_fingerprint: Hash,
    post_env_fingerprint: Hash,
    prior_chain_fingerprint: Hash,
    limits: ProducerLimits,
    limit_profile_hash: Hash,
    decl_interface_hash: Hash,
    decl_certificate_hash: Hash,
}

impl CheckedDeclCandidate {
    /// Return non-authoritative preview hashes captured while checking this token.
    pub fn preview_hashes(&self) -> CandidateHashPreview {
        self.preview_hashes
    }

    /// Return the producer environment fingerprint before this declaration was accepted.
    pub fn pre_env_fingerprint(&self) -> Hash {
        self.pre_env_fingerprint
    }

    /// Return the producer environment fingerprint after this declaration was accepted.
    pub fn post_env_fingerprint(&self) -> Hash {
        self.post_env_fingerprint
    }

    /// Return the prior-chain fingerprint committed by this token.
    pub fn prior_chain_fingerprint(&self) -> Hash {
        self.prior_chain_fingerprint
    }

    /// Return the deterministic limits used when this token was created.
    pub fn limits(&self) -> ProducerLimits {
        self.limits
    }

    /// Return the diagnostic hash of the limits used when this token was created.
    pub fn limit_profile_hash(&self) -> Hash {
        self.limit_profile_hash
    }

    /// Return whether the stored limits match this token's diagnostic limit-profile hash.
    pub fn limit_profile_hash_matches(&self) -> bool {
        producer_limits_hash(&self.limits) == self.limit_profile_hash
    }

    /// Return whether this token's checked limits are reusable under `batch_limits`.
    pub fn limits_are_reusable_under(&self, batch_limits: &ProducerLimits) -> bool {
        stricter_or_equal(&self.limits, batch_limits)
    }

    /// Return the token's diagnostic declaration interface hash.
    pub fn decl_interface_hash(&self) -> Hash {
        self.decl_interface_hash
    }

    /// Return the token's diagnostic declaration certificate hash.
    pub fn decl_certificate_hash(&self) -> Hash {
        self.decl_certificate_hash
    }
}

/// Non-authoritative hash preview computed while checking a producer candidate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CandidateHashPreview {
    /// Preview of the declaration type hash, when available.
    pub type_hash: Option<Hash>,
    /// Preview of the declaration body or proof hash, when available.
    pub body_hash: Option<Hash>,
    /// Preview of the declaration interface hash, when available.
    pub decl_interface_hash: Option<Hash>,
    /// Preview of the declaration certificate hash, when available.
    pub decl_certificate_hash: Option<Hash>,
}

/// Per-candidate status returned by producer batch checking.
///
/// Accepted candidates are producer-side checked tokens, not verified modules.
///
/// ```compile_fail
/// use npa_cert::{CandidateStatus, VerifiedModule};
///
/// fn trust_accepted_candidate(status: CandidateStatus) -> VerifiedModule {
///     let CandidateStatus::Accepted(token) = status else {
///         panic!("candidate was rejected");
///     };
///     token
/// }
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
// Certificate producer specifies a by-value accepted token; do not box the public API boundary.
#[allow(clippy::large_enum_variant)]
pub enum CandidateStatus {
    /// Candidate passed producer precheck and became an opaque token.
    Accepted(CheckedDeclCandidate),
    /// Candidate was rejected with a deterministic certificate error.
    Rejected(CertError),
}

/// Result for a producer candidate batch.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CandidateBatchResult {
    /// One status per input candidate, in the same order.
    pub statuses: Vec<CandidateStatus>,
}

struct AcceptedCandidate {
    token: CheckedDeclCandidate,
    interface: ProducerCheckedDeclInterface,
    prior_chain_entry: ProducerPriorChainEntry,
    post_env_fingerprint: Hash,
    declaration: Decl,
    env: Env,
}

struct ResolvedCoreDeclCandidate {
    interface: ProducerCheckedDeclInterface,
    hashes: DeclHashes,
}

struct ValidatedTokenChain {
    checked_decls: Vec<ProducerCheckedDeclInterface>,
    declarations: Vec<Decl>,
}

struct CandidateCheckContext<'a> {
    env: &'a Env,
    imports: &'a [VerifiedModule],
    direct_imports: &'a [ProducerImportEnvKey],
    checked_decls: &'a [ProducerCheckedDeclInterface],
    checked_decl_sources: &'a [Decl],
    prior_chain_entries: &'a [ProducerPriorChainEntry],
    pre_env_fingerprint: Hash,
    limits: &'a ProducerLimits,
}

fn check_candidate_in_batch(
    context: CandidateCheckContext<'_>,
    candidate: &CoreDeclCandidate,
) -> Result<AcceptedCandidate, CertError> {
    let declaration = candidate.declaration.clone();
    ensure_no_unresolved_metavariable(&declaration)?;
    ensure_candidate_schema_limits(&declaration, context.limits)?;

    let resolved = resolve_core_decl_candidate(
        context.imports,
        context.checked_decls,
        context.checked_decl_sources,
        &declaration,
    )?;

    let mut candidate_env = context.env.clone();
    add_referenced_builtins_for_decl(
        &mut candidate_env,
        context.imports,
        context.checked_decl_sources,
        &declaration,
    )?;
    let mut whnf_fuel = fuel_to_usize(
        context.limits.max_reduction_steps,
        ProducerLimitKind::MaxReductionSteps,
    )?;
    let mut conversion_fuel = fuel_to_usize(
        context.limits.max_conversion_steps,
        ProducerLimitKind::MaxConversionSteps,
    )?;
    precheck_decl_with_fuel(
        &candidate_env,
        &declaration,
        &mut whnf_fuel,
        &mut conversion_fuel,
    )?;

    let mut next_env = candidate_env;
    crate::add_decl_to_env(&mut next_env, declaration.clone())?;

    let mut next_checked_decls = context.checked_decls.to_vec();
    next_checked_decls.push(resolved.interface.clone());
    let post_env_fingerprint = producer_env_fingerprint(&ProducerEnvFingerprintBytes {
        direct_imports: context.direct_imports.to_vec(),
        checked_decls: next_checked_decls,
    });
    let prior_chain_fingerprint = prior_chain_fingerprint(&ProducerPriorChainBytes {
        checked_decls: context.prior_chain_entries.to_vec(),
    });
    let limit_profile_hash = producer_limits_hash(context.limits);
    let token = CheckedDeclCandidate {
        declaration: declaration.clone(),
        preview_hashes: CandidateHashPreview {
            type_hash: None,
            body_hash: None,
            decl_interface_hash: Some(resolved.hashes.decl_interface_hash),
            decl_certificate_hash: Some(resolved.hashes.decl_certificate_hash),
        },
        pre_env_fingerprint: context.pre_env_fingerprint,
        post_env_fingerprint,
        prior_chain_fingerprint,
        limits: *context.limits,
        limit_profile_hash,
        decl_interface_hash: resolved.hashes.decl_interface_hash,
        decl_certificate_hash: resolved.hashes.decl_certificate_hash,
    };
    let prior_chain_entry = ProducerPriorChainEntry {
        decl_interface_hash: resolved.hashes.decl_interface_hash,
        decl_certificate_hash: resolved.hashes.decl_certificate_hash,
        pre_env_fingerprint: context.pre_env_fingerprint,
        post_env_fingerprint,
    };

    Ok(AcceptedCandidate {
        token,
        interface: resolved.interface,
        prior_chain_entry,
        post_env_fingerprint,
        declaration,
        env: next_env,
    })
}

fn resolve_core_decl_candidate(
    imports: &[VerifiedModule],
    checked_decls: &[ProducerCheckedDeclInterface],
    checked_decl_sources: &[Decl],
    declaration: &Decl,
) -> Result<ResolvedCoreDeclCandidate, CertError> {
    // This is the producer boundary where name-based kernel declarations become hash-bound
    // certificate references for dependency and private token hashes.
    let lookup_env = producer_lookup_env_for_sources(imports, checked_decls, checked_decl_sources)?;
    let (interface, hashes) =
        crate::canonical_producer_checked_decl_hashes(declaration, &lookup_env)?;
    Ok(ResolvedCoreDeclCandidate { interface, hashes })
}

fn validate_checked_decl_chain(
    imports: &[VerifiedModule],
    tokens: &[CheckedDeclCandidate],
    reusable_limits: Option<&ProducerLimits>,
) -> Result<ValidatedTokenChain, CertError> {
    let direct_imports = canonical_import_env_keys(imports)?;
    let mut checked_decls = Vec::with_capacity(tokens.len());
    let mut declarations = Vec::with_capacity(tokens.len());
    let mut prior_chain_entries = Vec::with_capacity(tokens.len());
    let mut expected_pre_env_fingerprint = producer_env_fingerprint(&ProducerEnvFingerprintBytes {
        direct_imports: direct_imports.clone(),
        checked_decls: vec![],
    });

    for (token_index, token) in tokens.iter().enumerate() {
        ensure_token_hash(
            token_index,
            ProducerTokenHashField::PreEnvFingerprint,
            expected_pre_env_fingerprint,
            token.pre_env_fingerprint,
        )?;

        let expected_prior_chain_fingerprint = prior_chain_fingerprint(&ProducerPriorChainBytes {
            checked_decls: prior_chain_entries.clone(),
        });
        ensure_token_hash(
            token_index,
            ProducerTokenHashField::PriorChainFingerprint,
            expected_prior_chain_fingerprint,
            token.prior_chain_fingerprint,
        )?;

        ensure_token_hash(
            token_index,
            ProducerTokenHashField::LimitProfileHash,
            producer_limits_hash(&token.limits),
            token.limit_profile_hash,
        )?;
        if reusable_limits.is_some_and(|limits| !token.limits_are_reusable_under(limits)) {
            return Err(CertError::ProducerTokenLimitTooLoose { token_index });
        }

        let resolved = resolve_core_decl_candidate(
            imports,
            &checked_decls,
            &declarations,
            &token.declaration,
        )?;

        ensure_token_hash(
            token_index,
            ProducerTokenHashField::DeclInterfaceHash,
            resolved.hashes.decl_interface_hash,
            token.decl_interface_hash,
        )?;
        ensure_token_hash(
            token_index,
            ProducerTokenHashField::DeclCertificateHash,
            resolved.hashes.decl_certificate_hash,
            token.decl_certificate_hash,
        )?;

        let mut next_checked_decls = checked_decls.clone();
        next_checked_decls.push(resolved.interface.clone());
        let expected_post_env_fingerprint =
            producer_env_fingerprint(&ProducerEnvFingerprintBytes {
                direct_imports: direct_imports.clone(),
                checked_decls: next_checked_decls,
            });
        ensure_token_hash(
            token_index,
            ProducerTokenHashField::PostEnvFingerprint,
            expected_post_env_fingerprint,
            token.post_env_fingerprint,
        )?;

        prior_chain_entries.push(ProducerPriorChainEntry {
            decl_interface_hash: resolved.hashes.decl_interface_hash,
            decl_certificate_hash: resolved.hashes.decl_certificate_hash,
            pre_env_fingerprint: expected_pre_env_fingerprint,
            post_env_fingerprint: expected_post_env_fingerprint,
        });
        checked_decls.push(resolved.interface);
        declarations.push(token.declaration.clone());
        expected_pre_env_fingerprint = expected_post_env_fingerprint;
    }

    Ok(ValidatedTokenChain {
        checked_decls,
        declarations,
    })
}

fn fuel_to_usize(value: u64, limit: ProducerLimitKind) -> Result<usize, CertError> {
    usize::try_from(value).map_err(|_| CertError::ProducerLimitExceeded { limit })
}

fn ensure_token_hash(
    token_index: usize,
    field: ProducerTokenHashField,
    expected: Hash,
    actual: Hash,
) -> Result<(), CertError> {
    if expected == actual {
        Ok(())
    } else {
        Err(CertError::ProducerTokenHashMismatch {
            token_index,
            field,
            expected,
            actual,
        })
    }
}

fn ensure_candidate_batch_schema(batch: &CandidateBatch<'_>) -> Result<(), CertError> {
    if batch.candidates.len() > batch.limits.max_declarations as usize {
        return Err(CertError::ProducerLimitExceeded {
            limit: ProducerLimitKind::MaxDeclarations,
        });
    }
    Ok(())
}

fn producer_base_env(imports: &[VerifiedModule]) -> Result<Env, CertError> {
    let mut env = Env::new();
    let imports: Vec<_> = imports.iter().collect();
    crate::add_imports_to_env(&mut env, &imports)?;
    Ok(env)
}

fn producer_lookup_env_for_sources(
    imports: &[VerifiedModule],
    checked_decls: &[ProducerCheckedDeclInterface],
    checked_decl_sources: &[Decl],
) -> Result<ProducerLookupEnv, CertError> {
    if checked_decls.len() != checked_decl_sources.len() {
        return Err(CertError::DecodeError);
    }
    let mut lookup_env = producer_lookup_env(imports, checked_decls)?;
    lookup_env.checked_decl_names = checked_decl_sources
        .iter()
        .map(|decl| crate::Name::from_dotted(decl.name()))
        .collect();
    lookup_env.checked_generated_name_to_index =
        checked_generated_name_to_index(checked_decl_sources);
    crate::ensure_unique_names(&checked_public_names(checked_decl_sources))?;
    Ok(lookup_env)
}

fn checked_generated_name_to_index(decls: &[Decl]) -> BTreeMap<ModuleName, usize> {
    let mut generated = BTreeMap::new();
    for (decl_index, decl) in decls.iter().enumerate() {
        match decl {
            Decl::Inductive { data, .. } => {
                for constructor in &data.constructors {
                    generated.insert(crate::Name::from_dotted(&constructor.name), decl_index);
                }
                if let Some(recursor) = &data.recursor {
                    generated.insert(crate::Name::from_dotted(&recursor.name), decl_index);
                }
            }
            Decl::MutualInductiveBlock { data, .. } => {
                for inductive in &data.inductives {
                    generated.insert(crate::Name::from_dotted(&inductive.name), decl_index);
                    for constructor in &inductive.constructors {
                        generated.insert(crate::Name::from_dotted(&constructor.name), decl_index);
                    }
                    if let Some(recursor) = &inductive.recursor {
                        generated.insert(crate::Name::from_dotted(&recursor.name), decl_index);
                    }
                }
            }
            _ => {}
        }
    }
    generated
}

fn checked_public_names(decls: &[Decl]) -> Vec<ModuleName> {
    let mut names = Vec::new();
    for decl in decls {
        names.push(crate::Name::from_dotted(decl.name()));
        match decl {
            Decl::Inductive { data, .. } => {
                for constructor in &data.constructors {
                    names.push(crate::Name::from_dotted(&constructor.name));
                }
                if let Some(recursor) = &data.recursor {
                    names.push(crate::Name::from_dotted(&recursor.name));
                }
            }
            Decl::MutualInductiveBlock { data, .. } => {
                for inductive in &data.inductives {
                    names.push(crate::Name::from_dotted(&inductive.name));
                    for constructor in &inductive.constructors {
                        names.push(crate::Name::from_dotted(&constructor.name));
                    }
                    if let Some(recursor) = &inductive.recursor {
                        names.push(crate::Name::from_dotted(&recursor.name));
                    }
                }
            }
            _ => {}
        }
    }
    names
}

fn add_referenced_builtins_for_decl(
    env: &mut Env,
    imports: &[VerifiedModule],
    checked_decl_sources: &[Decl],
    decl: &Decl,
) -> Result<(), CertError> {
    let mut names = BTreeSet::new();
    collect_const_names_from_decl(&mut names, decl);
    let import_exports = import_export_names(imports)?;
    let checked_public_names = checked_public_names(checked_decl_sources)
        .into_iter()
        .collect::<BTreeSet<_>>();
    names.retain(|name| {
        !import_exports.contains(name)
            && !checked_public_names.contains(name)
            && crate::builtin_decl_interface_hash(name).is_some()
    });
    crate::add_referenced_builtins_to_env(env, &names)
}

fn import_export_names(imports: &[VerifiedModule]) -> Result<BTreeSet<ModuleName>, CertError> {
    let mut names = BTreeSet::new();
    for import in imports {
        for entry in import.export_block() {
            names.insert(
                import
                    .name_table()
                    .get(entry.name)
                    .cloned()
                    .ok_or(CertError::DecodeError)?,
            );
        }
    }
    Ok(names)
}

fn ensure_no_unresolved_metavariable(decl: &Decl) -> Result<(), CertError> {
    if decl_contains_unresolved_metavariable(decl) {
        Err(CertError::UnresolvedMetavariable)
    } else {
        Ok(())
    }
}

fn decl_contains_unresolved_metavariable(decl: &Decl) -> bool {
    match decl {
        Decl::MutualInductiveBlock { data, .. } => data.inductives.iter().any(|inductive| {
            inductive
                .params
                .iter()
                .any(|binder| expr_contains_unresolved_metavariable(&binder.ty))
                || inductive
                    .indices
                    .iter()
                    .any(|binder| expr_contains_unresolved_metavariable(&binder.ty))
                || inductive
                    .constructors
                    .iter()
                    .any(|constructor| expr_contains_unresolved_metavariable(&constructor.ty))
                || inductive
                    .recursor
                    .iter()
                    .any(|recursor| expr_contains_unresolved_metavariable(&recursor.ty))
        }),
        _ => {
            expr_contains_unresolved_metavariable(decl.ty())
                || match decl {
                    Decl::Def { value, .. } | Decl::DefConstrained { value, .. } => {
                        expr_contains_unresolved_metavariable(value)
                    }
                    Decl::Theorem { proof, .. } | Decl::TheoremConstrained { proof, .. } => {
                        expr_contains_unresolved_metavariable(proof)
                    }
                    Decl::Inductive { data, .. } => {
                        data.params
                            .iter()
                            .any(|binder| expr_contains_unresolved_metavariable(&binder.ty))
                            || data
                                .indices
                                .iter()
                                .any(|binder| expr_contains_unresolved_metavariable(&binder.ty))
                            || data.constructors.iter().any(|constructor| {
                                expr_contains_unresolved_metavariable(&constructor.ty)
                            })
                            || data
                                .recursor
                                .iter()
                                .any(|recursor| expr_contains_unresolved_metavariable(&recursor.ty))
                    }
                    Decl::Axiom { .. }
                    | Decl::AxiomConstrained { .. }
                    | Decl::Constructor { .. }
                    | Decl::Recursor { .. }
                    | Decl::MutualInductiveBlock { .. } => false,
                }
        }
    }
}

fn expr_contains_unresolved_metavariable(expr: &Expr) -> bool {
    match expr {
        Expr::Sort(level) => level_contains_unresolved_metavariable(level),
        Expr::BVar(_) | Expr::Const { .. } => false,
        Expr::App(fun, arg) => {
            expr_contains_unresolved_metavariable(fun) || expr_contains_unresolved_metavariable(arg)
        }
        Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
            expr_contains_unresolved_metavariable(ty) || expr_contains_unresolved_metavariable(body)
        }
        Expr::Let {
            ty, value, body, ..
        } => {
            expr_contains_unresolved_metavariable(ty)
                || expr_contains_unresolved_metavariable(value)
                || expr_contains_unresolved_metavariable(body)
        }
    }
}

fn level_contains_unresolved_metavariable(level: &Level) -> bool {
    match level {
        Level::Zero | Level::Param(_) => false,
        Level::Succ(level) => level_contains_unresolved_metavariable(level),
        Level::Max(lhs, rhs) | Level::IMax(lhs, rhs) => {
            level_contains_unresolved_metavariable(lhs)
                || level_contains_unresolved_metavariable(rhs)
        }
    }
}

fn collect_const_names_from_decl(names: &mut BTreeSet<ModuleName>, decl: &Decl) {
    if !matches!(decl, Decl::MutualInductiveBlock { .. }) {
        collect_const_names_from_expr(names, decl.ty());
    }
    match decl {
        Decl::Def { value, .. } | Decl::DefConstrained { value, .. } => {
            collect_const_names_from_expr(names, value)
        }
        Decl::Theorem { proof, .. } | Decl::TheoremConstrained { proof, .. } => {
            collect_const_names_from_expr(names, proof)
        }
        Decl::Inductive { data, .. } => {
            for param in &data.params {
                collect_const_names_from_expr(names, &param.ty);
            }
            for index in &data.indices {
                collect_const_names_from_expr(names, &index.ty);
            }
            for constructor in &data.constructors {
                collect_const_names_from_expr(names, &constructor.ty);
            }
            if let Some(recursor) = &data.recursor {
                collect_const_names_from_expr(names, &recursor.ty);
            }
        }
        Decl::MutualInductiveBlock { data, .. } => {
            for inductive in &data.inductives {
                for param in &inductive.params {
                    collect_const_names_from_expr(names, &param.ty);
                }
                for index in &inductive.indices {
                    collect_const_names_from_expr(names, &index.ty);
                }
                for constructor in &inductive.constructors {
                    collect_const_names_from_expr(names, &constructor.ty);
                }
                if let Some(recursor) = &inductive.recursor {
                    collect_const_names_from_expr(names, &recursor.ty);
                }
            }
        }
        Decl::Axiom { .. }
        | Decl::AxiomConstrained { .. }
        | Decl::Constructor { .. }
        | Decl::Recursor { .. } => {}
    }
}

fn collect_const_names_from_expr(names: &mut BTreeSet<ModuleName>, expr: &Expr) {
    match expr {
        Expr::Sort(_) | Expr::BVar(_) => {}
        Expr::Const { name, .. } => {
            names.insert(crate::Name::from_dotted(name));
        }
        Expr::App(fun, arg) => {
            collect_const_names_from_expr(names, fun);
            collect_const_names_from_expr(names, arg);
        }
        Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
            collect_const_names_from_expr(names, ty);
            collect_const_names_from_expr(names, body);
        }
        Expr::Let {
            ty, value, body, ..
        } => {
            collect_const_names_from_expr(names, ty);
            collect_const_names_from_expr(names, value);
            collect_const_names_from_expr(names, body);
        }
    }
}

fn verified_import_order_key(import: &VerifiedModule) -> (ModuleName, Hash, Option<Hash>) {
    (
        import.module().clone(),
        import.export_hash(),
        Some(import.certificate_hash()),
    )
}

fn ensure_candidate_schema_limits(decl: &Decl, limits: &ProducerLimits) -> Result<(), CertError> {
    if limits.max_declarations == 0 {
        return Err(CertError::ProducerLimitExceeded {
            limit: ProducerLimitKind::MaxDeclarations,
        });
    }

    let expr_nodes = decl_expr_node_count(decl);
    if expr_nodes > limits.max_expr_nodes as u64 {
        return Err(CertError::ProducerLimitExceeded {
            limit: ProducerLimitKind::MaxExprNodes,
        });
    }

    let level_nodes = decl_level_node_count(decl);
    if level_nodes > limits.max_level_nodes as u64 {
        return Err(CertError::ProducerLimitExceeded {
            limit: ProducerLimitKind::MaxLevelNodes,
        });
    }

    if decl_max_name_components(decl) > limits.max_name_components as u64 {
        return Err(CertError::ProducerLimitExceeded {
            limit: ProducerLimitKind::MaxNameComponents,
        });
    }

    Ok(())
}

fn precheck_decl_with_fuel(
    env: &Env,
    decl: &Decl,
    whnf_fuel: &mut usize,
    conversion_fuel: &mut usize,
) -> Result<(), CertError> {
    match decl {
        Decl::Axiom {
            name,
            universe_params,
            ty,
        }
        | Decl::AxiomConstrained {
            name,
            universe_params,
            ty,
            ..
        } => {
            ensure_fresh(env, name)?;
            let delta = validate_universe_params(universe_params)?;
            npa_kernel::level::ensure_universe_constraints_wf(&delta, decl.universe_constraints())
                .map_err(CertError::Kernel)?;
            expect_sort_with_fuel(env, &delta, ty, whnf_fuel, conversion_fuel)
        }
        Decl::Def {
            name,
            universe_params,
            ty,
            value,
            ..
        }
        | Decl::DefConstrained {
            name,
            universe_params,
            ty,
            value,
            ..
        } => {
            ensure_fresh(env, name)?;
            let delta = validate_universe_params(universe_params)?;
            npa_kernel::level::ensure_universe_constraints_wf(&delta, decl.universe_constraints())
                .map_err(CertError::Kernel)?;
            expect_sort_with_fuel(env, &delta, ty, whnf_fuel, conversion_fuel)?;
            env.check_with_fuel_metered(
                &Ctx::new(),
                &delta,
                value,
                ty,
                whnf_fuel,
                conversion_fuel,
            )?;
            Ok(())
        }
        Decl::Theorem {
            name,
            universe_params,
            ty,
            proof,
        }
        | Decl::TheoremConstrained {
            name,
            universe_params,
            ty,
            proof,
            ..
        } => {
            ensure_fresh(env, name)?;
            let delta = validate_universe_params(universe_params)?;
            npa_kernel::level::ensure_universe_constraints_wf(&delta, decl.universe_constraints())
                .map_err(CertError::Kernel)?;
            expect_sort_with_fuel(env, &delta, ty, whnf_fuel, conversion_fuel)?;
            env.check_with_fuel_metered(
                &Ctx::new(),
                &delta,
                proof,
                ty,
                whnf_fuel,
                conversion_fuel,
            )?;
            Ok(())
        }
        Decl::Inductive { name, .. } => Err(CertError::Kernel(Error::InvalidInductive(format!(
            "{name} inductive candidate precheck is not part of the certificate AI MVP"
        )))),
        Decl::MutualInductiveBlock { name, .. } => {
            Err(CertError::Kernel(Error::InvalidInductive(format!(
                "{name} mutual inductive candidate precheck is not part of the certificate AI MVP"
            ))))
        }
        Decl::Constructor { .. } | Decl::Recursor { .. } => Err(CertError::UnknownDependency {
            name: crate::Name::from_dotted(decl.name()),
        }),
    }
}

fn ensure_fresh(env: &Env, name: &str) -> Result<(), CertError> {
    if env.decl(name).is_some() {
        Err(CertError::Kernel(Error::DuplicateDecl(name.to_owned())))
    } else {
        Ok(())
    }
}

fn validate_universe_params(params: &[String]) -> Result<Vec<String>, CertError> {
    npa_kernel::level::validate_universe_params(params).map_err(CertError::Kernel)
}

fn expect_sort_with_fuel(
    env: &Env,
    delta: &[String],
    term: &Expr,
    whnf_fuel: &mut usize,
    conversion_fuel: &mut usize,
) -> Result<(), CertError> {
    let ty = env.infer_with_fuel_metered(&Ctx::new(), delta, term, whnf_fuel, conversion_fuel)?;
    match env.whnf_with_fuel_metered(&Ctx::new(), delta, &ty, whnf_fuel)? {
        Expr::Sort(_) => Ok(()),
        actual => Err(CertError::Kernel(Error::ExpectedSort { actual })),
    }
}

fn decl_expr_node_count(decl: &Decl) -> u64 {
    match decl {
        Decl::Axiom { ty, .. } | Decl::AxiomConstrained { ty, .. } => expr_node_count(ty),
        Decl::Def { ty, value, .. } | Decl::DefConstrained { ty, value, .. } => {
            expr_node_count(ty) + expr_node_count(value)
        }
        Decl::Theorem { ty, proof, .. } | Decl::TheoremConstrained { ty, proof, .. } => {
            expr_node_count(ty) + expr_node_count(proof)
        }
        Decl::Inductive { ty, data, .. } => {
            expr_node_count(ty)
                + data
                    .params
                    .iter()
                    .map(|binder| expr_node_count(&binder.ty))
                    .sum::<u64>()
                + data
                    .indices
                    .iter()
                    .map(|binder| expr_node_count(&binder.ty))
                    .sum::<u64>()
                + data
                    .constructors
                    .iter()
                    .map(|constructor| expr_node_count(&constructor.ty))
                    .sum::<u64>()
                + data
                    .recursor
                    .iter()
                    .map(|recursor| expr_node_count(&recursor.ty))
                    .sum::<u64>()
        }
        Decl::MutualInductiveBlock { data, .. } => data
            .inductives
            .iter()
            .map(|inductive| {
                inductive
                    .params
                    .iter()
                    .map(|binder| expr_node_count(&binder.ty))
                    .sum::<u64>()
                    + inductive
                        .indices
                        .iter()
                        .map(|binder| expr_node_count(&binder.ty))
                        .sum::<u64>()
                    + inductive
                        .constructors
                        .iter()
                        .map(|constructor| expr_node_count(&constructor.ty))
                        .sum::<u64>()
                    + inductive
                        .recursor
                        .iter()
                        .map(|recursor| expr_node_count(&recursor.ty))
                        .sum::<u64>()
            })
            .sum(),
        Decl::Constructor { ty, .. } | Decl::Recursor { ty, .. } => expr_node_count(ty),
    }
}

fn expr_node_count(expr: &Expr) -> u64 {
    match expr {
        Expr::Sort(_) | Expr::BVar(_) | Expr::Const { .. } => 1,
        Expr::App(fun, arg) => 1 + expr_node_count(fun) + expr_node_count(arg),
        Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
            1 + expr_node_count(ty) + expr_node_count(body)
        }
        Expr::Let {
            ty, value, body, ..
        } => 1 + expr_node_count(ty) + expr_node_count(value) + expr_node_count(body),
    }
}

fn decl_level_node_count(decl: &Decl) -> u64 {
    let constraint_count: u64 = decl
        .universe_constraints()
        .iter()
        .map(|constraint| level_node_count(&constraint.lhs) + level_node_count(&constraint.rhs))
        .sum();
    match decl {
        Decl::Axiom { ty, .. } | Decl::AxiomConstrained { ty, .. } => {
            expr_level_node_count(ty) + constraint_count
        }
        Decl::Def { ty, value, .. } | Decl::DefConstrained { ty, value, .. } => {
            expr_level_node_count(ty) + expr_level_node_count(value) + constraint_count
        }
        Decl::Theorem { ty, proof, .. } | Decl::TheoremConstrained { ty, proof, .. } => {
            expr_level_node_count(ty) + expr_level_node_count(proof) + constraint_count
        }
        Decl::Inductive { ty, data, .. } => {
            expr_level_node_count(ty)
                + level_node_count(&data.sort)
                + data
                    .params
                    .iter()
                    .map(|binder| expr_level_node_count(&binder.ty))
                    .sum::<u64>()
                + data
                    .indices
                    .iter()
                    .map(|binder| expr_level_node_count(&binder.ty))
                    .sum::<u64>()
                + data
                    .constructors
                    .iter()
                    .map(|constructor| expr_level_node_count(&constructor.ty))
                    .sum::<u64>()
                + data
                    .recursor
                    .iter()
                    .map(|recursor| expr_level_node_count(&recursor.ty))
                    .sum::<u64>()
                + constraint_count
        }
        Decl::MutualInductiveBlock { data, .. } => {
            data.inductives
                .iter()
                .map(|inductive| {
                    level_node_count(&inductive.sort)
                        + inductive
                            .params
                            .iter()
                            .map(|binder| expr_level_node_count(&binder.ty))
                            .sum::<u64>()
                        + inductive
                            .indices
                            .iter()
                            .map(|binder| expr_level_node_count(&binder.ty))
                            .sum::<u64>()
                        + inductive
                            .constructors
                            .iter()
                            .map(|constructor| expr_level_node_count(&constructor.ty))
                            .sum::<u64>()
                        + inductive
                            .recursor
                            .iter()
                            .map(|recursor| expr_level_node_count(&recursor.ty))
                            .sum::<u64>()
                })
                .sum::<u64>()
                + constraint_count
        }
        Decl::Constructor { ty, .. } | Decl::Recursor { ty, .. } => expr_level_node_count(ty),
    }
}

fn expr_level_node_count(expr: &Expr) -> u64 {
    match expr {
        Expr::Sort(level) => level_node_count(level),
        Expr::BVar(_) => 0,
        Expr::Const { levels, .. } => levels.iter().map(level_node_count).sum(),
        Expr::App(fun, arg) => expr_level_node_count(fun) + expr_level_node_count(arg),
        Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
            expr_level_node_count(ty) + expr_level_node_count(body)
        }
        Expr::Let {
            ty, value, body, ..
        } => expr_level_node_count(ty) + expr_level_node_count(value) + expr_level_node_count(body),
    }
}

fn level_node_count(level: &Level) -> u64 {
    match level {
        Level::Zero | Level::Param(_) => 1,
        Level::Succ(level) => 1 + level_node_count(level),
        Level::Max(lhs, rhs) | Level::IMax(lhs, rhs) => {
            1 + level_node_count(lhs) + level_node_count(rhs)
        }
    }
}

fn decl_max_name_components(decl: &Decl) -> u64 {
    match decl {
        Decl::Axiom {
            name,
            universe_params,
            ty,
        }
        | Decl::AxiomConstrained {
            name,
            universe_params,
            ty,
            ..
        } => {
            let max_constraint_name_components = decl
                .universe_constraints()
                .iter()
                .map(|constraint| {
                    level_max_name_components(&constraint.lhs)
                        .max(level_max_name_components(&constraint.rhs))
                })
                .max()
                .unwrap_or(0);
            max_name_components(
                std::iter::once(name.as_str()).chain(universe_params.iter().map(String::as_str)),
                std::iter::once(ty),
            )
            .max(max_constraint_name_components)
        }
        Decl::Def {
            name,
            universe_params,
            ty,
            value,
            ..
        }
        | Decl::DefConstrained {
            name,
            universe_params,
            ty,
            value,
            ..
        } => {
            let max_constraint_name_components = decl
                .universe_constraints()
                .iter()
                .map(|constraint| {
                    level_max_name_components(&constraint.lhs)
                        .max(level_max_name_components(&constraint.rhs))
                })
                .max()
                .unwrap_or(0);
            max_name_components(
                std::iter::once(name.as_str()).chain(universe_params.iter().map(String::as_str)),
                [ty, value],
            )
            .max(max_constraint_name_components)
        }
        Decl::Theorem {
            name,
            universe_params,
            ty,
            proof,
        }
        | Decl::TheoremConstrained {
            name,
            universe_params,
            ty,
            proof,
            ..
        } => {
            let max_constraint_name_components = decl
                .universe_constraints()
                .iter()
                .map(|constraint| {
                    level_max_name_components(&constraint.lhs)
                        .max(level_max_name_components(&constraint.rhs))
                })
                .max()
                .unwrap_or(0);
            max_name_components(
                std::iter::once(name.as_str()).chain(universe_params.iter().map(String::as_str)),
                [ty, proof],
            )
            .max(max_constraint_name_components)
        }
        Decl::Inductive {
            name,
            universe_params,
            ty,
            data,
        } => {
            let names = std::iter::once(name.as_str())
                .chain(universe_params.iter().map(String::as_str))
                .chain(std::iter::once(data.name.as_str()))
                .chain(data.universe_params.iter().map(String::as_str))
                .chain(data.params.iter().map(|binder| binder.name.as_str()))
                .chain(data.indices.iter().map(|binder| binder.name.as_str()))
                .chain(
                    data.constructors
                        .iter()
                        .map(|constructor| constructor.name.as_str()),
                )
                .chain(data.recursor.iter().map(|recursor| recursor.name.as_str()))
                .chain(
                    data.recursor
                        .iter()
                        .flat_map(|recursor| recursor.universe_params.iter().map(String::as_str)),
                );
            let exprs = std::iter::once(ty)
                .chain(data.params.iter().map(|binder| &binder.ty))
                .chain(data.indices.iter().map(|binder| &binder.ty))
                .chain(data.constructors.iter().map(|constructor| &constructor.ty))
                .chain(data.recursor.iter().map(|recursor| &recursor.ty));
            let max_constraint_name_components = data
                .universe_constraints
                .iter()
                .map(|constraint| {
                    level_max_name_components(&constraint.lhs)
                        .max(level_max_name_components(&constraint.rhs))
                })
                .max()
                .unwrap_or(0);
            max_name_components(names, exprs)
                .max(level_max_name_components(&data.sort))
                .max(max_constraint_name_components)
        }
        Decl::MutualInductiveBlock {
            name,
            universe_params,
            data,
        } => {
            let mut names = vec![name.as_str(), data.name.as_str()];
            names.extend(universe_params.iter().map(String::as_str));
            names.extend(data.universe_params.iter().map(String::as_str));
            let mut exprs = Vec::new();
            let mut max_sort_name_components = 0;
            for inductive in &data.inductives {
                names.push(inductive.name.as_str());
                names.extend(inductive.universe_params.iter().map(String::as_str));
                names.extend(inductive.params.iter().map(|binder| binder.name.as_str()));
                names.extend(inductive.indices.iter().map(|binder| binder.name.as_str()));
                names.extend(
                    inductive
                        .constructors
                        .iter()
                        .map(|constructor| constructor.name.as_str()),
                );
                names.extend(
                    inductive
                        .recursor
                        .iter()
                        .map(|recursor| recursor.name.as_str()),
                );
                if let Some(recursor) = &inductive.recursor {
                    names.extend(recursor.universe_params.iter().map(String::as_str));
                }
                exprs.extend(inductive.params.iter().map(|binder| &binder.ty));
                exprs.extend(inductive.indices.iter().map(|binder| &binder.ty));
                exprs.extend(
                    inductive
                        .constructors
                        .iter()
                        .map(|constructor| &constructor.ty),
                );
                exprs.extend(inductive.recursor.iter().map(|recursor| &recursor.ty));
                max_sort_name_components =
                    max_sort_name_components.max(level_max_name_components(&inductive.sort));
            }
            let max_constraint_name_components = data
                .universe_constraints
                .iter()
                .map(|constraint| {
                    level_max_name_components(&constraint.lhs)
                        .max(level_max_name_components(&constraint.rhs))
                })
                .max()
                .unwrap_or(0);
            max_name_components(names, exprs)
                .max(max_sort_name_components)
                .max(max_constraint_name_components)
        }
        Decl::Constructor {
            name,
            universe_params,
            ty,
            inductive,
        } => max_name_components(
            std::iter::once(name.as_str())
                .chain(universe_params.iter().map(String::as_str))
                .chain(std::iter::once(inductive.as_str())),
            std::iter::once(ty),
        ),
        Decl::Recursor {
            name,
            universe_params,
            ty,
            inductive,
            ..
        } => max_name_components(
            std::iter::once(name.as_str())
                .chain(universe_params.iter().map(String::as_str))
                .chain(std::iter::once(inductive.as_str())),
            std::iter::once(ty),
        ),
    }
}

fn max_name_components<'a>(
    names: impl IntoIterator<Item = &'a str>,
    exprs: impl IntoIterator<Item = &'a Expr>,
) -> u64 {
    names
        .into_iter()
        .map(name_component_count)
        .chain(exprs.into_iter().map(expr_max_name_components))
        .max()
        .unwrap_or(0)
}

fn expr_max_name_components(expr: &Expr) -> u64 {
    match expr {
        Expr::Sort(level) => level_max_name_components(level),
        Expr::BVar(_) => 0,
        Expr::Const { name, levels } => levels
            .iter()
            .map(level_max_name_components)
            .chain(std::iter::once(name_component_count(name)))
            .max()
            .unwrap_or(0),
        Expr::App(fun, arg) => expr_max_name_components(fun).max(expr_max_name_components(arg)),
        Expr::Lam {
            binder, ty, body, ..
        }
        | Expr::Pi {
            binder, ty, body, ..
        } => name_component_count(binder)
            .max(expr_max_name_components(ty))
            .max(expr_max_name_components(body)),
        Expr::Let {
            binder,
            ty,
            value,
            body,
        } => name_component_count(binder)
            .max(expr_max_name_components(ty))
            .max(expr_max_name_components(value))
            .max(expr_max_name_components(body)),
    }
}

fn level_max_name_components(level: &Level) -> u64 {
    match level {
        Level::Zero => 0,
        Level::Param(name) => name_component_count(name),
        Level::Succ(level) => level_max_name_components(level),
        Level::Max(lhs, rhs) | Level::IMax(lhs, rhs) => {
            level_max_name_components(lhs).max(level_max_name_components(rhs))
        }
    }
}

fn name_component_count(name: &str) -> u64 {
    name.split('.').count() as u64
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_limits() -> ProducerLimits {
        ProducerLimits {
            max_declarations: 1,
            max_expr_nodes: 8,
            max_level_nodes: 2,
            max_name_components: 4,
            max_reduction_steps: 16,
            max_conversion_steps: 16,
        }
    }

    fn test_token(limits: ProducerLimits, limit_profile_hash: Hash) -> CheckedDeclCandidate {
        let zero = [0_u8; 32];
        CheckedDeclCandidate {
            declaration: Decl::Axiom {
                name: "P".to_owned(),
                universe_params: vec![],
                ty: Expr::sort(Level::zero()),
            },
            preview_hashes: CandidateHashPreview {
                type_hash: None,
                body_hash: None,
                decl_interface_hash: None,
                decl_certificate_hash: None,
            },
            pre_env_fingerprint: zero,
            post_env_fingerprint: zero,
            prior_chain_fingerprint: zero,
            limits,
            limit_profile_hash,
            decl_interface_hash: zero,
            decl_certificate_hash: zero,
        }
    }

    fn hash(byte: u8) -> Hash {
        [byte; 32]
    }

    fn looser_limits(limits: ProducerLimits) -> ProducerLimits {
        ProducerLimits {
            max_declarations: limits.max_declarations + 1,
            max_expr_nodes: limits.max_expr_nodes + 1,
            max_level_nodes: limits.max_level_nodes + 1,
            max_name_components: limits.max_name_components + 1,
            max_reduction_steps: limits.max_reduction_steps + 1,
            max_conversion_steps: limits.max_conversion_steps + 1,
        }
    }

    fn prior_axiom(name: &str) -> Decl {
        Decl::Axiom {
            name: name.to_owned(),
            universe_params: vec![],
            ty: Expr::sort(Level::zero()),
        }
    }

    fn valid_prior_token(
        declaration: Decl,
        token_limits: ProducerLimits,
        checked_before: &[ProducerCheckedDeclInterface],
        prior_chain_before: &[ProducerPriorChainEntry],
    ) -> (
        CheckedDeclCandidate,
        ProducerCheckedDeclInterface,
        ProducerPriorChainEntry,
    ) {
        let imports: &[VerifiedModule] = &[];
        let direct_imports = canonical_import_env_keys(imports).unwrap();
        let pre_env_fingerprint = producer_env_fingerprint(&ProducerEnvFingerprintBytes {
            direct_imports: direct_imports.clone(),
            checked_decls: checked_before.to_vec(),
        });
        let lookup_env = producer_lookup_env(imports, checked_before).unwrap();
        let (interface, hashes) =
            crate::canonical_producer_checked_decl_hashes(&declaration, &lookup_env).unwrap();
        let mut checked_after = checked_before.to_vec();
        checked_after.push(interface.clone());
        let post_env_fingerprint = producer_env_fingerprint(&ProducerEnvFingerprintBytes {
            direct_imports,
            checked_decls: checked_after,
        });
        let prior_chain_fingerprint = prior_chain_fingerprint(&ProducerPriorChainBytes {
            checked_decls: prior_chain_before.to_vec(),
        });
        let token = CheckedDeclCandidate {
            declaration,
            preview_hashes: CandidateHashPreview {
                type_hash: Some(hash(0x91)),
                body_hash: Some(hash(0x92)),
                decl_interface_hash: Some(hash(0x93)),
                decl_certificate_hash: Some(hash(0x94)),
            },
            pre_env_fingerprint,
            post_env_fingerprint,
            prior_chain_fingerprint,
            limits: token_limits,
            limit_profile_hash: producer_limits_hash(&token_limits),
            decl_interface_hash: hashes.decl_interface_hash,
            decl_certificate_hash: hashes.decl_certificate_hash,
        };
        let entry = ProducerPriorChainEntry {
            decl_interface_hash: hashes.decl_interface_hash,
            decl_certificate_hash: hashes.decl_certificate_hash,
            pre_env_fingerprint,
            post_env_fingerprint,
        };
        (token, interface, entry)
    }

    fn empty_prior_batch<'a>(
        prior_current_decls: &'a [CheckedDeclCandidate],
        limits: ProducerLimits,
    ) -> CandidateBatch<'a> {
        CandidateBatch {
            imports: &[],
            prior_current_decls,
            candidates: vec![],
            limits,
        }
    }

    fn assert_token_hash_mismatch(
        err: CertError,
        expected_token_index: usize,
        expected_field: ProducerTokenHashField,
        expected_actual: Hash,
    ) {
        match err {
            CertError::ProducerTokenHashMismatch {
                token_index,
                field,
                actual,
                ..
            } => {
                assert_eq!(token_index, expected_token_index);
                assert_eq!(field, expected_field);
                assert_eq!(actual, expected_actual);
            }
            other => panic!("unexpected error: {other:?}"),
        }
    }

    #[test]
    fn checked_decl_candidate_limit_helpers_use_private_limits() {
        let limits = test_limits();
        let token = test_token(limits, producer_limits_hash(&limits));

        assert!(token.limit_profile_hash_matches());

        let reusable_batch_limits = ProducerLimits {
            max_declarations: limits.max_declarations + 1,
            max_expr_nodes: limits.max_expr_nodes + 1,
            max_level_nodes: limits.max_level_nodes + 1,
            max_name_components: limits.max_name_components + 1,
            max_reduction_steps: limits.max_reduction_steps + 1,
            max_conversion_steps: limits.max_conversion_steps + 1,
        };
        assert!(token.limits_are_reusable_under(&reusable_batch_limits));

        let too_strict_batch_limits = ProducerLimits {
            max_expr_nodes: limits.max_expr_nodes - 1,
            ..reusable_batch_limits
        };
        assert!(!token.limits_are_reusable_under(&too_strict_batch_limits));

        let mismatched_token = test_token(limits, [0_u8; 32]);
        assert!(!mismatched_token.limit_profile_hash_matches());
    }

    #[test]
    fn validate_prior_current_decls_accepts_stricter_token_and_ignores_previews() {
        let token_limits = test_limits();
        let (token, interface, _) = valid_prior_token(prior_axiom("P"), token_limits, &[], &[]);
        let prior = [token];
        let batch = empty_prior_batch(&prior, looser_limits(token_limits));

        assert_eq!(
            validate_prior_current_decls(&batch).unwrap(),
            vec![interface]
        );
    }

    #[test]
    fn validate_prior_current_decls_rejects_looser_token_limits() {
        let token_limits = test_limits();
        let (token, _, _) = valid_prior_token(prior_axiom("P"), token_limits, &[], &[]);
        let prior = [token];
        let mut batch_limits = token_limits;
        batch_limits.max_expr_nodes -= 1;
        let batch = empty_prior_batch(&prior, batch_limits);

        assert_eq!(
            validate_prior_current_decls(&batch).unwrap_err(),
            CertError::ProducerTokenLimitTooLoose { token_index: 0 }
        );
    }

    #[test]
    fn validate_prior_current_decls_rejects_first_pre_env_mismatch() {
        let token_limits = test_limits();
        let (mut token, _, _) = valid_prior_token(prior_axiom("P"), token_limits, &[], &[]);
        let forged = hash(0x51);
        token.pre_env_fingerprint = forged;
        let prior = [token];
        let batch = empty_prior_batch(&prior, token_limits);

        assert_token_hash_mismatch(
            validate_prior_current_decls(&batch).unwrap_err(),
            0,
            ProducerTokenHashField::PreEnvFingerprint,
            forged,
        );
    }

    #[test]
    fn validate_prior_current_decls_rejects_second_pre_env_mismatch() {
        let token_limits = test_limits();
        let (token1, interface1, entry1) =
            valid_prior_token(prior_axiom("P"), token_limits, &[], &[]);
        let (mut token2, _, _) = valid_prior_token(
            prior_axiom("Q"),
            token_limits,
            std::slice::from_ref(&interface1),
            std::slice::from_ref(&entry1),
        );
        let forged = hash(0x52);
        token2.pre_env_fingerprint = forged;
        let prior = [token1, token2];
        let batch = empty_prior_batch(&prior, token_limits);

        assert_token_hash_mismatch(
            validate_prior_current_decls(&batch).unwrap_err(),
            1,
            ProducerTokenHashField::PreEnvFingerprint,
            forged,
        );
    }

    #[test]
    fn validate_prior_current_decls_rejects_prior_chain_mismatch() {
        let token_limits = test_limits();
        let (token1, interface1, entry1) =
            valid_prior_token(prior_axiom("P"), token_limits, &[], &[]);
        let (mut token2, _, _) = valid_prior_token(
            prior_axiom("Q"),
            token_limits,
            std::slice::from_ref(&interface1),
            std::slice::from_ref(&entry1),
        );
        let forged = hash(0x53);
        token2.prior_chain_fingerprint = forged;
        let prior = [token1, token2];
        let batch = empty_prior_batch(&prior, token_limits);

        assert_token_hash_mismatch(
            validate_prior_current_decls(&batch).unwrap_err(),
            1,
            ProducerTokenHashField::PriorChainFingerprint,
            forged,
        );
    }

    #[test]
    fn validate_prior_current_decls_rejects_limit_profile_hash_mismatch() {
        let token_limits = test_limits();
        let (mut token, _, _) = valid_prior_token(prior_axiom("P"), token_limits, &[], &[]);
        let forged = hash(0x54);
        token.limit_profile_hash = forged;
        let prior = [token];
        let batch = empty_prior_batch(&prior, token_limits);

        assert_token_hash_mismatch(
            validate_prior_current_decls(&batch).unwrap_err(),
            0,
            ProducerTokenHashField::LimitProfileHash,
            forged,
        );
    }

    #[test]
    fn validate_prior_current_decls_rejects_decl_interface_hash_mismatch() {
        let token_limits = test_limits();
        let (mut token, _, _) = valid_prior_token(prior_axiom("P"), token_limits, &[], &[]);
        let forged = hash(0x55);
        token.decl_interface_hash = forged;
        let prior = [token];
        let batch = empty_prior_batch(&prior, token_limits);

        assert_token_hash_mismatch(
            validate_prior_current_decls(&batch).unwrap_err(),
            0,
            ProducerTokenHashField::DeclInterfaceHash,
            forged,
        );
    }

    #[test]
    fn validate_prior_current_decls_rejects_decl_certificate_hash_mismatch() {
        let token_limits = test_limits();
        let (mut token, _, _) = valid_prior_token(prior_axiom("P"), token_limits, &[], &[]);
        let forged = hash(0x56);
        token.decl_certificate_hash = forged;
        let prior = [token];
        let batch = empty_prior_batch(&prior, token_limits);

        assert_token_hash_mismatch(
            validate_prior_current_decls(&batch).unwrap_err(),
            0,
            ProducerTokenHashField::DeclCertificateHash,
            forged,
        );
    }

    #[test]
    fn validate_prior_current_decls_rejects_post_env_mismatch() {
        let token_limits = test_limits();
        let (mut token, _, _) = valid_prior_token(prior_axiom("P"), token_limits, &[], &[]);
        let forged = hash(0x57);
        token.post_env_fingerprint = forged;
        let prior = [token];
        let batch = empty_prior_batch(&prior, token_limits);

        assert_token_hash_mismatch(
            validate_prior_current_decls(&batch).unwrap_err(),
            0,
            ProducerTokenHashField::PostEnvFingerprint,
            forged,
        );
    }

    #[test]
    fn check_core_decl_candidates_rejects_invalid_prior_token_at_batch_level() {
        let token_limits = test_limits();
        let (mut token, _, _) = valid_prior_token(prior_axiom("P"), token_limits, &[], &[]);
        let forged = hash(0x58);
        token.pre_env_fingerprint = forged;
        let prior = [token];
        let batch = CandidateBatch {
            imports: &[],
            prior_current_decls: &prior,
            candidates: vec![CoreDeclCandidate {
                declaration: prior_axiom("Q"),
            }],
            limits: token_limits,
        };

        assert_token_hash_mismatch(
            check_core_decl_candidates(batch).unwrap_err(),
            0,
            ProducerTokenHashField::PreEnvFingerprint,
            forged,
        );
    }

    #[test]
    fn build_module_cert_from_checked_candidates_rejects_forged_limit_profile_hash() {
        let token_limits = test_limits();
        let (mut token, _, _) = valid_prior_token(prior_axiom("P"), token_limits, &[], &[]);
        let forged = hash(0x59);
        token.limit_profile_hash = forged;
        let tokens = [token];

        assert_token_hash_mismatch(
            build_module_cert_from_checked_candidates(
                crate::Name::from_dotted("Forged"),
                &[],
                &tokens,
            )
            .unwrap_err(),
            0,
            ProducerTokenHashField::LimitProfileHash,
            forged,
        );
    }

    #[test]
    fn build_module_cert_from_checked_candidates_ignores_preview_hashes() {
        let token_limits = test_limits();
        let (token, _, _) = valid_prior_token(prior_axiom("P"), token_limits, &[], &[]);
        let tokens = [token];

        let cert = build_module_cert_from_checked_candidates(
            crate::Name::from_dotted("Preview"),
            &[],
            &tokens,
        )
        .unwrap();

        assert_eq!(cert.declarations.len(), 1);
    }

    #[test]
    fn build_module_cert_from_checked_candidates_rejects_forged_decl_hash() {
        let token_limits = test_limits();
        let (mut token, _, _) = valid_prior_token(prior_axiom("P"), token_limits, &[], &[]);
        let forged = hash(0x5a);
        token.decl_certificate_hash = forged;
        let tokens = [token];

        assert_token_hash_mismatch(
            build_module_cert_from_checked_candidates(
                crate::Name::from_dotted("Forged"),
                &[],
                &tokens,
            )
            .unwrap_err(),
            0,
            ProducerTokenHashField::DeclCertificateHash,
            forged,
        );
    }

    #[test]
    fn build_module_cert_from_checked_candidates_rejects_forged_prior_chain() {
        let token_limits = test_limits();
        let (token1, interface1, entry1) =
            valid_prior_token(prior_axiom("P"), token_limits, &[], &[]);
        let (mut token2, _, _) = valid_prior_token(
            prior_axiom("Q"),
            token_limits,
            std::slice::from_ref(&interface1),
            std::slice::from_ref(&entry1),
        );
        let forged = hash(0x5b);
        token2.prior_chain_fingerprint = forged;
        let tokens = [token1, token2];

        assert_token_hash_mismatch(
            build_module_cert_from_checked_candidates(
                crate::Name::from_dotted("Forged"),
                &[],
                &tokens,
            )
            .unwrap_err(),
            1,
            ProducerTokenHashField::PriorChainFingerprint,
            forged,
        );
    }
}

use std::collections::BTreeSet;

use npa_kernel::{
    expr::collect_apps, level::level_eq, level::levels_eq, Binder, ConstructorDecl, Env, Expr,
    InductiveDecl, KernelExecutionOptions, KernelWorkCounterSink, Level, MutualInductiveBlock,
};

use crate::local_authoring::{
    certificate_file_hash, CertificateImportView, LocalAuthoringInterfaceIdentity,
    LocalAuthoringReconstructionIdentity,
};
use crate::*;

struct ValidatedLevelReferences(());

struct ValidatedTermReferences(());

struct ValidatedCertificateTables {
    level_hashes: Vec<Hash>,
    term_hashes: Vec<Hash>,
}

#[allow(dead_code)]
enum CanonicalCertificateEncoding<'a> {
    AuthoritativeBytes {
        version: CertificateFormatVersion,
        bytes: &'a [u8],
        certificate_hash_input_end: usize,
    },
    Streamed {
        version: CertificateFormatVersion,
        computed_certificate_hash: Hash,
    },
}

struct BuiltCertificateHashEncoding {
    version: CertificateFormatVersion,
    bytes: Vec<u8>,
}

#[allow(dead_code)]
enum CanonicalCertificateHashInput<'a> {
    AuthoritativeBytes {
        version: CertificateFormatVersion,
        bytes: &'a [u8],
    },
    StreamedHash {
        version: CertificateFormatVersion,
        computed_certificate_hash: Hash,
    },
}

struct PendingCertificateHashChecks {
    version: CertificateFormatVersion,
    expected_export_block: ExportBlock,
    export_domain: &'static [u8],
    export_bytes: Vec<u8>,
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct ValidationReuseWorkCounter {
    pub(crate) level_key_encodings: u64,
    pub(crate) term_key_encodings: u64,
    pub(crate) level_hash_passes: u64,
    pub(crate) term_hash_passes: u64,
    pub(crate) canonical_full_encodings: u64,
    pub(crate) authoritative_prefix_uses: u64,
    pub(crate) streamed_prehash_uses: u64,
    pub(crate) lazy_built_materializations: u64,
    pub(crate) canonical_encoding_allocated_bytes: u64,
    pub(crate) key_scratch_allocated_bytes: u64,
}

struct ValidationReuseObserver<'a> {
    #[cfg(test)]
    counter: Option<&'a mut ValidationReuseWorkCounter>,
    #[cfg(not(test))]
    marker: std::marker::PhantomData<&'a mut ()>,
}

#[derive(Clone, Copy)]
enum ValidationReuseMetric {
    LevelKeyEncodings,
    TermKeyEncodings,
    LevelHashPasses,
    TermHashPasses,
    CanonicalFullEncodings,
    AuthoritativePrefixUses,
    StreamedPrehashUses,
    LazyBuiltMaterializations,
    CanonicalEncodingAllocatedBytes,
    KeyScratchAllocatedBytes,
}

impl<'a> ValidationReuseObserver<'a> {
    fn unobserved() -> Self {
        Self {
            #[cfg(test)]
            counter: None,
            #[cfg(not(test))]
            marker: std::marker::PhantomData,
        }
    }

    #[cfg(test)]
    fn observed(counter: &'a mut ValidationReuseWorkCounter) -> Self {
        Self {
            counter: Some(counter),
        }
    }

    fn increment(&mut self, metric: ValidationReuseMetric) {
        #[cfg(test)]
        if let Some(counter) = self.counter.as_deref_mut() {
            let value = match metric {
                ValidationReuseMetric::LevelKeyEncodings => &mut counter.level_key_encodings,
                ValidationReuseMetric::TermKeyEncodings => &mut counter.term_key_encodings,
                ValidationReuseMetric::LevelHashPasses => &mut counter.level_hash_passes,
                ValidationReuseMetric::TermHashPasses => &mut counter.term_hash_passes,
                ValidationReuseMetric::CanonicalFullEncodings => {
                    &mut counter.canonical_full_encodings
                }
                ValidationReuseMetric::AuthoritativePrefixUses => {
                    &mut counter.authoritative_prefix_uses
                }
                ValidationReuseMetric::StreamedPrehashUses => &mut counter.streamed_prehash_uses,
                ValidationReuseMetric::LazyBuiltMaterializations => {
                    &mut counter.lazy_built_materializations
                }
                ValidationReuseMetric::CanonicalEncodingAllocatedBytes => {
                    &mut counter.canonical_encoding_allocated_bytes
                }
                ValidationReuseMetric::KeyScratchAllocatedBytes => {
                    &mut counter.key_scratch_allocated_bytes
                }
            };
            *value = value.saturating_add(1);
        }
        #[cfg(not(test))]
        let _ = metric;
    }

    fn add(&mut self, metric: ValidationReuseMetric, amount: usize) {
        #[cfg(test)]
        if let Some(counter) = self.counter.as_deref_mut() {
            let value = match metric {
                ValidationReuseMetric::CanonicalEncodingAllocatedBytes => {
                    &mut counter.canonical_encoding_allocated_bytes
                }
                ValidationReuseMetric::KeyScratchAllocatedBytes => {
                    &mut counter.key_scratch_allocated_bytes
                }
                _ => return self.increment(metric),
            };
            *value = value.saturating_add(u64::try_from(amount).unwrap_or(u64::MAX));
        }
        #[cfg(not(test))]
        let _ = (metric, amount);
    }
}

pub(crate) fn verify_module_cert_impl(
    bytes: &[u8],
    session: &mut VerifierSession,
    policy: &AxiomPolicy,
) -> Result<VerifiedModule> {
    let cert = decode_module_cert(bytes)?;
    let verified = verify_owned_module_cert_with_import_resolver(
        cert,
        bytes,
        policy,
        KernelExecutionOptions::default(),
        |cert| resolve_imports(cert, session, policy),
    )?;
    session.insert_verified(verified.clone(), policy.mode);
    Ok(verified)
}

pub(crate) fn verify_module_cert_hashes_impl(bytes: &[u8]) -> Result<ModuleCert> {
    let mut observer = ValidationReuseObserver::unobserved();
    verify_module_cert_hashes_impl_observed(bytes, &mut observer)
}

fn verify_module_cert_hashes_impl_observed(
    bytes: &[u8],
    observer: &mut ValidationReuseObserver<'_>,
) -> Result<ModuleCert> {
    let cert = decode_module_cert(bytes)?;
    structural_preflight(&cert)?;
    let canonical = verify_canonical_encoding(&cert, bytes, observer)?;
    verify_pre_import_checks(&cert, &canonical, observer)?;
    Ok(cert)
}

#[cfg(test)]
pub(crate) fn verify_module_cert_hashes_impl_with_validation_reuse_counter(
    bytes: &[u8],
    counter: &mut ValidationReuseWorkCounter,
) -> Result<ModuleCert> {
    let mut observer = ValidationReuseObserver::observed(counter);
    verify_module_cert_hashes_impl_observed(bytes, &mut observer)
}

#[cfg(test)]
pub(crate) fn verify_built_module_cert_hashes_impl_with_validation_reuse_counter(
    cert: &ModuleCert,
    counter: &mut ValidationReuseWorkCounter,
) -> Result<()> {
    structural_preflight(cert)?;
    let mut observer = ValidationReuseObserver::observed(counter);
    verify_built_hash_and_table_checks(cert, &mut observer)
}

#[cfg(test)]
pub(crate) fn validation_reuse_verify_tables_for_test(
    cert: &ModuleCert,
) -> Result<(Vec<Hash>, Vec<Hash>)> {
    let mut observer = ValidationReuseObserver::unobserved();
    let tables = verify_tables(cert, &mut observer)?;
    Ok((tables.level_hashes, tables.term_hashes))
}

#[cfg(test)]
pub(crate) fn validation_reuse_verify_tables_with_counter_for_test(
    cert: &ModuleCert,
    counter: &mut ValidationReuseWorkCounter,
) -> Result<(Vec<Hash>, Vec<Hash>)> {
    let mut observer = ValidationReuseObserver::observed(counter);
    let tables = verify_tables(cert, &mut observer)?;
    Ok((tables.level_hashes, tables.term_hashes))
}

/// Frozen copy of the pre-reuse table validator. Keep this independent of
/// `verify_tables`/`process_*_table`: it is the differential oracle for the
/// one-pass table processor rather than another entry into that processor.
#[cfg(test)]
pub(crate) fn validation_reuse_legacy_table_oracle_for_test(
    cert: &ModuleCert,
) -> Result<(Vec<Hash>, Vec<Hash>)> {
    if !cert.imports().windows(2).all(|pair| {
        (
            pair[0].module.clone(),
            pair[0].export_hash,
            pair[0].certificate_hash,
        ) < (
            pair[1].module.clone(),
            pair[1].export_hash,
            pair[1].certificate_hash,
        )
    }) {
        return Err(CertError::NonCanonicalEncoding { object: "Imports" });
    }
    if !cert.name_table().windows(2).all(|pair| pair[0] < pair[1]) {
        return Err(CertError::NonCanonicalEncoding {
            object: "NameTable",
        });
    }
    for (index, level) in cert.level_table().iter().enumerate() {
        let ordered = match level {
            LevelNode::Zero | LevelNode::Param(_) => true,
            LevelNode::Succ(inner) => *inner < index,
            LevelNode::Max(lhs, rhs) | LevelNode::IMax(lhs, rhs) => *lhs < index && *rhs < index,
        };
        let name_in_range = match level {
            LevelNode::Param(name) => *name < cert.name_table().len(),
            _ => true,
        };
        if !ordered || !name_in_range {
            return Err(CertError::NonCanonicalEncoding {
                object: "LevelTable",
            });
        }
    }
    if !level_table_is_normalized(cert)? {
        return Err(CertError::NonCanonicalEncoding {
            object: "LevelTable",
        });
    }

    fn level_heights(levels: &[LevelNode]) -> Result<Vec<usize>> {
        fn child(heights: &[usize], index: usize) -> Result<usize> {
            heights.get(index).copied().ok_or(CertError::DecodeError)
        }
        let mut heights = Vec::with_capacity(levels.len());
        for level in levels {
            let height = match level {
                LevelNode::Zero | LevelNode::Param(_) => 0,
                LevelNode::Succ(inner) => child(&heights, *inner)? + 1,
                LevelNode::Max(lhs, rhs) | LevelNode::IMax(lhs, rhs) => {
                    child(&heights, *lhs)?.max(child(&heights, *rhs)?) + 1
                }
            };
            heights.push(height);
        }
        Ok(heights)
    }

    let level_hashes = compute_level_hashes(cert.level_table(), cert.name_table())?;
    let level_heights = level_heights(cert.level_table())?;
    let mut previous_level_key = None;
    for (index, level) in cert.level_table().iter().enumerate() {
        let key = (
            level_heights[index],
            level_node_key(level, &level_hashes, cert.name_table())?,
        );
        if previous_level_key
            .as_ref()
            .is_some_and(|previous| previous >= &key)
        {
            return Err(CertError::NonCanonicalEncoding {
                object: "LevelTable",
            });
        }
        previous_level_key = Some(key);
    }

    for (index, term) in cert.term_table().iter().enumerate() {
        let ordered = match term {
            TermNode::Sort(_) | TermNode::BVar(_) | TermNode::Const { .. } => true,
            TermNode::App(fun, arg) => *fun < index && *arg < index,
            TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => *ty < index && *body < index,
        };
        let references_in_range = match term {
            TermNode::Sort(level) => *level < cert.level_table().len(),
            TermNode::Const { global_ref, levels } => {
                global_ref_is_in_range(cert, global_ref)
                    && levels.iter().all(|level| *level < cert.level_table().len())
            }
            _ => true,
        };
        if !ordered || !references_in_range {
            return Err(CertError::NonCanonicalEncoding {
                object: "TermTable",
            });
        }
    }

    fn term_heights(terms: &[TermNode]) -> Result<Vec<usize>> {
        fn child(heights: &[usize], index: usize) -> Result<usize> {
            heights.get(index).copied().ok_or(CertError::DecodeError)
        }
        let mut heights = Vec::with_capacity(terms.len());
        for term in terms {
            let height = match term {
                TermNode::Sort(_) | TermNode::BVar(_) | TermNode::Const { .. } => 0,
                TermNode::App(fun, arg) => child(&heights, *fun)?.max(child(&heights, *arg)?) + 1,
                TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => {
                    child(&heights, *ty)?.max(child(&heights, *body)?) + 1
                }
            };
            heights.push(height);
        }
        Ok(heights)
    }

    let term_hashes = compute_term_hashes(cert.term_table(), &level_hashes)?;
    let term_heights = term_heights(cert.term_table())?;
    let mut previous_term_key = None;
    for (index, term) in cert.term_table().iter().enumerate() {
        let key = (
            term_heights[index],
            term_node_key(term, &term_hashes, &level_hashes)?,
        );
        if previous_term_key
            .as_ref()
            .is_some_and(|previous| previous >= &key)
        {
            return Err(CertError::NonCanonicalEncoding {
                object: "TermTable",
            });
        }
        previous_term_key = Some(key);
    }
    verify_decl_universe_contexts(cert)?;
    verify_reachable_tables_and_bvars(cert)?;
    verify_name_table_reachable(cert)?;
    Ok((level_hashes, term_hashes))
}

/// Frozen copy of the pre-reuse post-table hash validator. This deliberately
/// recomputes the legacy hash vectors and owns the old format dispatch.
#[cfg(test)]
pub(crate) fn validation_reuse_legacy_hash_oracle_for_test(cert: &ModuleCert) -> Result<()> {
    let level_hashes = compute_level_hashes(cert.level_table(), cert.name_table())?;
    let term_hashes = compute_term_hashes(cert.term_table(), &level_hashes)?;
    let version = certificate_format_version(cert.header())?;
    for decl in cert.declarations() {
        let expected = compute_decl_hashes(
            version,
            &decl.decl,
            &decl.dependencies,
            &decl.axiom_dependencies,
            DeclHashTables {
                terms: cert.term_table(),
                level_hashes: &level_hashes,
                term_hashes: &term_hashes,
                names: cert.name_table(),
            },
        )?;
        if expected.decl_interface_hash != decl.hashes.decl_interface_hash {
            return Err(CertError::HashMismatch {
                object: HashObject::DeclInterface,
                expected: decl.hashes.decl_interface_hash,
                actual: expected.decl_interface_hash,
            });
        }
        if expected.decl_certificate_hash != decl.hashes.decl_certificate_hash {
            return Err(CertError::HashMismatch {
                object: HashObject::DeclCertificate,
                expected: decl.hashes.decl_certificate_hash,
                actual: expected.decl_certificate_hash,
            });
        }
    }

    let expected_export_block =
        build_export_block(cert.declarations(), cert.term_table(), &term_hashes)?;
    let export_domain = MODULE_EXPORT_DOMAIN;
    let export_bytes = encode_export_block(&expected_export_block);
    let cert_domain = version.module_certificate_domain();
    let cert_bytes = encode_module_cert_without_certificate_hash_for_header(cert)?;
    let expected_export = hash_with_domain(export_domain, &export_bytes);
    if expected_export_block != cert.export_block() || expected_export != cert.hashes().export_hash
    {
        return Err(CertError::HashMismatch {
            object: HashObject::ExportBlock,
            expected: cert.hashes().export_hash,
            actual: expected_export,
        });
    }
    let expected_axioms = hash_with_domain(
        b"NPA-AXIOM-REPORT-0.1",
        &encode_axiom_report(cert.axiom_report()),
    );
    if expected_axioms != cert.hashes().axiom_report_hash {
        return Err(CertError::HashMismatch {
            object: HashObject::AxiomReport,
            expected: cert.hashes().axiom_report_hash,
            actual: expected_axioms,
        });
    }
    let expected_cert = hash_with_domain(cert_domain, &cert_bytes);
    if expected_cert != cert.hashes().certificate_hash {
        return Err(CertError::HashMismatch {
            object: HashObject::ModuleCertificate,
            expected: cert.hashes().certificate_hash,
            actual: expected_cert,
        });
    }
    Ok(())
}

pub(crate) fn verify_decoded_module_cert_with_observations_impl(
    cert: &ModuleCert,
    bytes: &[u8],
    session: &mut VerifierSession,
    policy: &AxiomPolicy,
    mut observations: CertificateVerificationObservationSinks<'_>,
) -> Result<VerifiedModule> {
    let kernel_sink = observations
        .kernel
        .as_ref()
        .map(|_| KernelWorkCounterSink::default());
    let verified = verify_decoded_module_cert_with_import_resolver_observed(
        cert,
        bytes,
        policy,
        KernelExecutionOptions::default(),
        kernel_sink.clone(),
        observations.term.as_deref_mut(),
        |cert| resolve_imports(cert, session, policy),
    );
    if let (Some(output), Some(sink)) = (observations.kernel.as_deref_mut(), kernel_sink) {
        output.merge(sink.snapshot());
    }
    let verified = verified?;
    session.register_verified_module_with_trust_observed(
        verified.clone(),
        policy.mode,
        observations.payload,
    );
    Ok(verified)
}

pub(crate) fn verify_module_cert_with_import_refs_impl(
    bytes: &[u8],
    imports: &[&VerifiedModule],
    policy: &AxiomPolicy,
) -> Result<VerifiedModule> {
    verify_module_cert_with_import_refs_and_options_impl(
        bytes,
        imports,
        policy,
        KernelExecutionOptions::default(),
    )
}

pub(crate) fn verify_module_cert_with_import_refs_and_options_impl(
    bytes: &[u8],
    imports: &[&VerifiedModule],
    policy: &AxiomPolicy,
    kernel_options: KernelExecutionOptions,
) -> Result<VerifiedModule> {
    verify_module_cert_with_import_refs_and_options_and_observations_impl(
        bytes,
        imports,
        policy,
        kernel_options,
        CertificateVerificationObservationSinks::new(),
    )
}

pub(crate) fn verify_module_cert_with_import_refs_and_options_and_observations_impl(
    bytes: &[u8],
    imports: &[&VerifiedModule],
    policy: &AxiomPolicy,
    kernel_options: KernelExecutionOptions,
    mut observations: CertificateVerificationObservationSinks<'_>,
) -> Result<VerifiedModule> {
    let cert = decode_module_cert_observed(bytes, observations.payload.as_deref_mut())?;
    let kernel_sink = observations
        .kernel
        .as_ref()
        .map(|_| KernelWorkCounterSink::default());
    let result = verify_owned_module_cert_with_import_resolver_observed(
        cert,
        bytes,
        policy,
        kernel_options,
        kernel_sink.clone(),
        observations.term,
        |cert| resolve_import_refs(cert, imports, policy),
    );
    if let (Some(output), Some(sink)) = (observations.kernel, kernel_sink) {
        output.merge(sink.snapshot());
    }
    result
}

/// Test-only semantic oracle that retains the pre-materialization recursive
/// converter for both current declarations and referenced imports.
///
/// Keeping this entry separate from production lane selection lets
/// differential tests compare complete verifier results and logical fuel
/// without a process-global switch that could race with parallel tests.
#[cfg(test)]
pub(crate) fn verify_module_cert_with_import_refs_legacy_for_test(
    bytes: &[u8],
    available_imports: &[&VerifiedModule],
    policy: &AxiomPolicy,
    kernel_options: KernelExecutionOptions,
    work_counter_sink: Option<KernelWorkCounterSink>,
) -> Result<VerifiedModule> {
    ensure_certificate_byte_limit(bytes)?;
    let cert = decode_module_cert(bytes)?;
    let structural_cost = structural_preflight(&cert)?;
    let mut observer = ValidationReuseObserver::unobserved();
    let canonical = verify_canonical_encoding(&cert, bytes, &mut observer)?;
    verify_hash_and_table_checks(&cert, &canonical, &mut observer)?;
    enforce_core_feature_policy(cert.axiom_report(), policy)?;
    verify_declaration_order(&cert)?;

    let current_terms = KernelTermConversion::Legacy(&cert);
    verify_inductive_generated_artifacts(&cert, &current_terms, None)?;
    let imports = resolve_import_refs(&cert, available_imports, policy)?;
    let structural_closure = build_closure_summary(&cert, structural_cost, &imports)?;
    verify_dependencies_and_axioms(&cert, &imports)?;
    enforce_axiom_policy(&cert, policy)?;
    enforce_import_axiom_policy(&imports, policy)?;

    let mut env = match work_counter_sink {
        Some(sink) => Env::with_execution_options_and_work_counter_sink(kernel_options, sink),
        None => Env::with_execution_options(kernel_options),
    };
    let builtin_refs = referenced_builtins_from_cert(&cert)?;
    add_referenced_imports_to_env_legacy(&mut env, &cert, &imports)?;
    add_referenced_builtins_to_env(&mut env, &builtin_refs)?;
    let version = certificate_format_version(cert.header())?;
    for decl in cert.declarations() {
        add_current_module_decl_to_env(
            &mut env,
            cert_decl_to_kernel_decl_with_terms(&cert, &current_terms, decl, None)?,
            version,
        )?;
    }
    drop(env);

    Ok(verified_module_from_owned_cert(cert, structural_closure))
}

pub(crate) fn verify_decoded_module_cert_with_import_refs_impl(
    cert: &ModuleCert,
    bytes: &[u8],
    imports: &[&VerifiedModule],
    policy: &AxiomPolicy,
) -> Result<VerifiedModule> {
    verify_decoded_module_cert_with_import_refs_and_options_impl(
        cert,
        bytes,
        imports,
        policy,
        KernelExecutionOptions::default(),
    )
}

pub(crate) fn verify_decoded_module_cert_with_import_refs_and_options_impl(
    cert: &ModuleCert,
    bytes: &[u8],
    imports: &[&VerifiedModule],
    policy: &AxiomPolicy,
    kernel_options: KernelExecutionOptions,
) -> Result<VerifiedModule> {
    verify_decoded_module_cert_with_import_refs_and_options_and_observations_impl(
        cert,
        bytes,
        imports,
        policy,
        kernel_options,
        CertificateVerificationObservationSinks::new(),
    )
}

pub(crate) fn verify_decoded_module_cert_with_import_refs_and_options_and_observations_impl(
    cert: &ModuleCert,
    bytes: &[u8],
    imports: &[&VerifiedModule],
    policy: &AxiomPolicy,
    kernel_options: KernelExecutionOptions,
    observations: CertificateVerificationObservationSinks<'_>,
) -> Result<VerifiedModule> {
    let kernel_sink = observations
        .kernel
        .as_ref()
        .map(|_| KernelWorkCounterSink::default());
    let result = verify_decoded_module_cert_with_import_resolver_observed(
        cert,
        bytes,
        policy,
        kernel_options,
        kernel_sink.clone(),
        observations.term,
        |cert| resolve_import_refs(cert, imports, policy),
    );
    if let (Some(output), Some(sink)) = (observations.kernel, kernel_sink) {
        output.merge(sink.snapshot());
    }
    result
}

pub(crate) fn verify_built_module_cert_with_import_refs_impl(
    cert: &ModuleCert,
    imports: &[&VerifiedModule],
    policy: &AxiomPolicy,
) -> Result<VerifiedModule> {
    verify_built_module_cert_with_import_refs_and_options_impl(
        cert,
        imports,
        policy,
        KernelExecutionOptions::default(),
    )
}

pub(crate) fn verify_built_module_cert_with_import_refs_and_options_impl(
    cert: &ModuleCert,
    imports: &[&VerifiedModule],
    policy: &AxiomPolicy,
    kernel_options: KernelExecutionOptions,
) -> Result<VerifiedModule> {
    verify_built_module_cert_with_import_refs_and_options_and_observations_impl(
        cert,
        imports,
        policy,
        kernel_options,
        CertificateVerificationObservationSinks::new(),
    )
}

pub(crate) fn verify_built_module_cert_with_import_refs_and_options_and_observations_impl(
    cert: &ModuleCert,
    imports: &[&VerifiedModule],
    policy: &AxiomPolicy,
    kernel_options: KernelExecutionOptions,
    observations: CertificateVerificationObservationSinks<'_>,
) -> Result<VerifiedModule> {
    let structural_cost = structural_preflight(cert)?;
    let mut observer = ValidationReuseObserver::unobserved();
    verify_built_hash_and_table_checks(cert, &mut observer)?;
    let kernel_sink = observations
        .kernel
        .as_ref()
        .map(|_| KernelWorkCounterSink::default());
    let structural_closure = verify_decoded_module_cert_checks_after_hashes_inner(
        cert,
        structural_cost,
        policy,
        kernel_options,
        kernel_sink.clone(),
        observations.term,
        |cert| resolve_import_refs(cert, imports, policy),
    );
    if let (Some(output), Some(sink)) = (observations.kernel, kernel_sink) {
        output.merge(sink.snapshot());
    }
    structural_closure.map(|closure| verified_module_from_cert(cert, closure))
}

fn verify_decoded_module_cert_with_import_resolver_observed<'a>(
    cert: &ModuleCert,
    bytes: &[u8],
    policy: &AxiomPolicy,
    kernel_options: KernelExecutionOptions,
    work_counter_sink: Option<KernelWorkCounterSink>,
    term_observation: Option<&mut CertificateTermMaterializationObservation>,
    resolve_imports: impl FnOnce(&ModuleCert) -> Result<Vec<&'a dyn CertificateImportView>>,
) -> Result<VerifiedModule> {
    ensure_certificate_byte_limit(bytes)?;
    let structural_cost = structural_preflight(cert)?;
    let mut observer = ValidationReuseObserver::unobserved();
    let canonical = verify_canonical_encoding(cert, bytes, &mut observer)?;
    let structural_closure = verify_decoded_module_cert_checks_inner(
        cert,
        structural_cost,
        policy,
        kernel_options,
        work_counter_sink,
        &canonical,
        &mut observer,
        term_observation,
        resolve_imports,
    )?;
    Ok(verified_module_from_cert(cert, structural_closure))
}

fn verify_owned_module_cert_with_import_resolver<'a>(
    cert: ModuleCert,
    bytes: &[u8],
    policy: &AxiomPolicy,
    kernel_options: KernelExecutionOptions,
    resolve_imports: impl FnOnce(&ModuleCert) -> Result<Vec<&'a dyn CertificateImportView>>,
) -> Result<VerifiedModule> {
    ensure_certificate_byte_limit(bytes)?;
    let structural_cost = structural_preflight(&cert)?;
    let mut observer = ValidationReuseObserver::unobserved();
    let canonical = verify_canonical_encoding(&cert, bytes, &mut observer)?;
    let structural_closure = verify_decoded_module_cert_checks(
        &cert,
        structural_cost,
        policy,
        kernel_options,
        &canonical,
        &mut observer,
        resolve_imports,
    )?;
    Ok(verified_module_from_owned_cert(cert, structural_closure))
}

fn verify_owned_module_cert_with_import_resolver_observed<'a>(
    cert: ModuleCert,
    bytes: &[u8],
    policy: &AxiomPolicy,
    kernel_options: KernelExecutionOptions,
    work_counter_sink: Option<KernelWorkCounterSink>,
    term_observation: Option<&mut CertificateTermMaterializationObservation>,
    resolve_imports: impl FnOnce(&ModuleCert) -> Result<Vec<&'a dyn CertificateImportView>>,
) -> Result<VerifiedModule> {
    ensure_certificate_byte_limit(bytes)?;
    let structural_cost = structural_preflight(&cert)?;
    let mut observer = ValidationReuseObserver::unobserved();
    let canonical = verify_canonical_encoding(&cert, bytes, &mut observer)?;
    let structural_closure = verify_decoded_module_cert_checks_inner(
        &cert,
        structural_cost,
        policy,
        kernel_options,
        work_counter_sink,
        &canonical,
        &mut observer,
        term_observation,
        resolve_imports,
    )?;
    Ok(verified_module_from_owned_cert(cert, structural_closure))
}

fn verify_canonical_encoding<'a>(
    cert: &ModuleCert,
    bytes: &'a [u8],
    observer: &mut ValidationReuseObserver<'_>,
) -> Result<CanonicalCertificateEncoding<'a>> {
    let canonical = encode_module_cert_full_with_boundary_for_header(cert)?;
    observer.increment(ValidationReuseMetric::CanonicalFullEncodings);
    observer.add(
        ValidationReuseMetric::CanonicalEncodingAllocatedBytes,
        canonical.bytes.capacity(),
    );
    if canonical.bytes != bytes {
        return Err(CertError::NonCanonicalEncoding {
            object: "ModuleCert",
        });
    }
    if canonical.certificate_hash_input_end > bytes.len() {
        return Err(CertError::NonCanonicalEncoding {
            object: "ModuleCert",
        });
    }
    Ok(CanonicalCertificateEncoding::AuthoritativeBytes {
        version: canonical.version,
        bytes,
        certificate_hash_input_end: canonical.certificate_hash_input_end,
    })
}

fn verify_decoded_module_cert_checks<'a>(
    cert: &ModuleCert,
    structural_cost: StructuralCost,
    policy: &AxiomPolicy,
    kernel_options: KernelExecutionOptions,
    canonical: &CanonicalCertificateEncoding<'_>,
    observer: &mut ValidationReuseObserver<'_>,
    resolve_imports: impl FnOnce(&ModuleCert) -> Result<Vec<&'a dyn CertificateImportView>>,
) -> Result<StructuralClosureSummary> {
    verify_decoded_module_cert_checks_inner(
        cert,
        structural_cost,
        policy,
        kernel_options,
        None,
        canonical,
        observer,
        None,
        resolve_imports,
    )
}

// Keep the stage inputs explicit: bundling them would make the canonical-byte
// witness or work-counter sink easier to route into the wrong verification lane.
#[allow(clippy::too_many_arguments)]
fn verify_decoded_module_cert_checks_inner<'a>(
    cert: &ModuleCert,
    structural_cost: StructuralCost,
    policy: &AxiomPolicy,
    kernel_options: KernelExecutionOptions,
    work_counter_sink: Option<KernelWorkCounterSink>,
    canonical: &CanonicalCertificateEncoding<'_>,
    observer: &mut ValidationReuseObserver<'_>,
    term_observation: Option<&mut CertificateTermMaterializationObservation>,
    resolve_imports: impl FnOnce(&ModuleCert) -> Result<Vec<&'a dyn CertificateImportView>>,
) -> Result<StructuralClosureSummary> {
    verify_hash_and_table_checks(cert, canonical, observer)?;
    verify_decoded_module_cert_checks_after_hashes_inner(
        cert,
        structural_cost,
        policy,
        kernel_options,
        work_counter_sink,
        term_observation,
        resolve_imports,
    )
}

fn verify_decoded_module_cert_checks_after_hashes_inner<'a>(
    cert: &ModuleCert,
    structural_cost: StructuralCost,
    policy: &AxiomPolicy,
    kernel_options: KernelExecutionOptions,
    work_counter_sink: Option<KernelWorkCounterSink>,
    mut term_observation: Option<&mut CertificateTermMaterializationObservation>,
    resolve_imports: impl FnOnce(&ModuleCert) -> Result<Vec<&'a dyn CertificateImportView>>,
) -> Result<StructuralClosureSummary> {
    enforce_core_feature_policy(cert.axiom_report(), policy)?;
    verify_declaration_order(cert)?;
    let mut term_budget = TermMaterializationBudgetV1::new();
    let current_terms =
        select_current_term_conversion(cert, &mut term_budget, term_observation.as_deref_mut());
    verify_inductive_generated_artifacts(cert, &current_terms, term_observation.as_deref_mut())?;

    let imports = resolve_imports(cert)?;
    verify_decoded_module_cert_checks_with_imports_inner(
        cert,
        structural_cost,
        policy,
        kernel_options,
        work_counter_sink,
        &imports,
        &current_terms,
        &mut term_budget,
        term_observation,
    )
}

#[allow(clippy::too_many_arguments)]
fn verify_decoded_module_cert_checks_with_imports_inner(
    cert: &ModuleCert,
    structural_cost: StructuralCost,
    policy: &AxiomPolicy,
    kernel_options: KernelExecutionOptions,
    work_counter_sink: Option<KernelWorkCounterSink>,
    imports: &[&dyn CertificateImportView],
    current_terms: &KernelTermConversion<'_, ModuleCert>,
    term_budget: &mut TermMaterializationBudgetV1,
    mut term_observation: Option<&mut CertificateTermMaterializationObservation>,
) -> Result<StructuralClosureSummary> {
    let structural_closure = build_closure_summary(cert, structural_cost, imports)?;
    verify_dependencies_and_axioms(cert, imports)?;
    enforce_axiom_policy(cert, policy)?;
    enforce_import_axiom_policy(imports, policy)?;

    let mut env = match work_counter_sink {
        Some(sink) => Env::with_execution_options_and_work_counter_sink(kernel_options, sink),
        None => Env::with_execution_options(kernel_options),
    };
    let builtin_refs = referenced_builtins_from_cert(cert)?;
    add_referenced_imports_to_env(
        &mut env,
        cert,
        imports,
        term_budget,
        term_observation.as_deref_mut(),
    )?;
    add_referenced_builtins_to_env(&mut env, &builtin_refs)?;

    let version = certificate_format_version(cert.header())?;
    for decl in cert.declarations() {
        add_current_module_decl_to_env(
            &mut env,
            cert_decl_to_kernel_decl_with_terms(
                cert,
                current_terms,
                decl,
                term_observation.as_deref_mut(),
            )?,
            version,
        )?;
    }
    drop(env);

    Ok(structural_closure)
}

fn select_current_term_conversion<'a>(
    cert: &'a ModuleCert,
    budget: &mut TermMaterializationBudgetV1,
    mut observation: Option<&mut CertificateTermMaterializationObservation>,
) -> KernelTermConversion<'a, ModuleCert> {
    match collect_current_module_term_roots(cert, observation.as_deref_mut()) {
        MaterializationAttempt::Ready(roots) => {
            let attempt = KernelExprMaterialization::for_current_module(
                cert,
                &roots,
                budget,
                observation.as_deref_mut(),
            );
            KernelTermConversion::from_attempt(cert, attempt, observation)
        }
        MaterializationAttempt::Fallback(stop) => KernelTermConversion::from_attempt(
            cert,
            MaterializationAttempt::Fallback(stop),
            observation,
        ),
    }
}

#[cfg(test)]
pub(crate) fn select_current_term_conversion_with_budget_for_test(
    cert: &ModuleCert,
    budget: &mut TermMaterializationBudgetV1,
    observation: Option<&mut CertificateTermMaterializationObservation>,
) -> bool {
    select_current_term_conversion(cert, budget, observation)
        .materialized()
        .is_some()
}

pub(crate) fn reconstruct_local_authoring_context(
    bytes: &[u8],
    expected: &LocalAuthoringReconstructionIdentity,
    interface: &LocalAuthoringInterfaceIdentity,
    available_imports: &[&dyn CertificateImportView],
    policy: &AxiomPolicy,
) -> Result<(ModuleCert, StructuralClosureSummary)> {
    ensure_certificate_byte_limit(bytes)?;
    if certificate_file_hash(bytes) != expected.certificate_file_hash {
        return Err(CertError::NonCanonicalEncoding {
            object: "local authoring certificate file identity",
        });
    }

    let cert = decode_module_cert(bytes)?;
    let structural_cost = structural_preflight(&cert)?;
    let mut observer = ValidationReuseObserver::unobserved();
    let canonical = verify_canonical_encoding(&cert, bytes, &mut observer)?;
    verify_pre_import_checks(&cert, &canonical, &mut observer)?;
    verify_local_authoring_identity(&cert, expected, interface, policy)?;
    enforce_core_feature_policy(cert.axiom_report(), policy)?;
    enforce_axiom_policy(&cert, policy)?;

    let imports = resolve_import_views(&cert, available_imports, policy)?;
    enforce_import_axiom_policy(&imports, policy)?;
    let structural_closure = build_closure_summary(&cert, structural_cost, &imports)?;
    Ok((cert, structural_closure))
}

pub(crate) fn verify_built_local_authoring_module_cert(
    cert: &ModuleCert,
    available_imports: &[&dyn CertificateImportView],
    policy: &AxiomPolicy,
    kernel_options: KernelExecutionOptions,
) -> Result<StructuralClosureSummary> {
    let structural_cost = structural_preflight(cert)?;
    let mut observer = ValidationReuseObserver::unobserved();
    verify_built_hash_and_table_checks(cert, &mut observer)?;
    enforce_core_feature_policy(cert.axiom_report(), policy)?;
    verify_declaration_order(cert)?;
    let mut term_budget = TermMaterializationBudgetV1::new();
    let current_terms = select_current_term_conversion(cert, &mut term_budget, None);
    verify_inductive_generated_artifacts(cert, &current_terms, None)?;
    let imports = resolve_import_views(cert, available_imports, policy)?;
    verify_decoded_module_cert_checks_with_imports_inner(
        cert,
        structural_cost,
        policy,
        kernel_options,
        None,
        &imports,
        &current_terms,
        &mut term_budget,
        None,
    )
}

fn verify_local_authoring_identity(
    cert: &ModuleCert,
    expected: &LocalAuthoringReconstructionIdentity,
    interface: &LocalAuthoringInterfaceIdentity,
    policy: &AxiomPolicy,
) -> Result<()> {
    if cert.header().format != expected.certificate_format
        || cert.header().core_spec != expected.core_spec
    {
        return Err(CertError::NonCanonicalEncoding {
            object: "local authoring format identity",
        });
    }
    if cert.header().module != expected.module || cert.imports() != expected.imports {
        return Err(CertError::NonCanonicalEncoding {
            object: "local authoring module/import identity",
        });
    }
    verify_local_authoring_hash(
        HashObject::ExportBlock,
        expected.export_hash,
        cert.hashes().export_hash,
    )?;
    verify_local_authoring_hash(
        HashObject::AxiomReport,
        expected.axiom_report_hash,
        cert.hashes().axiom_report_hash,
    )?;
    verify_local_authoring_hash(
        HashObject::ModuleCertificate,
        expected.certificate_hash,
        cert.hashes().certificate_hash,
    )?;
    if expected.axiom_policy_hash != policy.policy_hash() {
        return Err(CertError::NonCanonicalEncoding {
            object: "local authoring axiom policy identity",
        });
    }
    if interface.module != cert.header().module
        || interface.export_hash != cert.hashes().export_hash
        || interface.certificate_hash != cert.hashes().certificate_hash
    {
        return Err(CertError::NonCanonicalEncoding {
            object: "local authoring parsed interface identity",
        });
    }
    Ok(())
}

fn verify_local_authoring_hash(object: HashObject, expected: Hash, actual: Hash) -> Result<()> {
    if expected == actual {
        Ok(())
    } else {
        Err(CertError::HashMismatch {
            object,
            expected,
            actual,
        })
    }
}

fn verify_pre_import_checks(
    cert: &ModuleCert,
    canonical: &CanonicalCertificateEncoding<'_>,
    observer: &mut ValidationReuseObserver<'_>,
) -> Result<()> {
    verify_hash_and_table_checks(cert, canonical, observer)?;
    verify_declaration_order(cert)?;
    verify_inductive_generated_artifacts_legacy(cert)?;
    Ok(())
}

fn verify_hash_and_table_checks(
    cert: &ModuleCert,
    canonical: &CanonicalCertificateEncoding<'_>,
    observer: &mut ValidationReuseObserver<'_>,
) -> Result<()> {
    verify_header(cert.header())?;
    let tables = verify_tables(cert, observer)?;
    verify_hashes_from_canonical_input(cert, &tables, canonical, observer)
}

fn verify_built_hash_and_table_checks(
    cert: &ModuleCert,
    observer: &mut ValidationReuseObserver<'_>,
) -> Result<()> {
    verify_header(cert.header())?;
    let tables = verify_tables(cert, observer)?;
    verify_hashes_for_built_certificate(cert, &tables, observer)
}

fn verified_module_from_cert(
    cert: &ModuleCert,
    structural_closure: StructuralClosureSummary,
) -> VerifiedModule {
    let logical_retained_bytes_v1 =
        crate::logical_charge::verified_module_logical_retained_bytes_v1(
            cert.logical_retained_bytes_v1(),
            &structural_closure,
        );
    VerifiedModule::from_parts(VerifiedModuleParts {
        certificate: cert.clone(),
        structural_closure,
        logical_retained_bytes_v1,
    })
}

fn verified_module_from_owned_cert(
    cert: ModuleCert,
    structural_closure: StructuralClosureSummary,
) -> VerifiedModule {
    let certificate_charge = cert.logical_retained_bytes_v1();
    let logical_retained_bytes_v1 =
        crate::logical_charge::verified_module_logical_retained_bytes_v1(
            certificate_charge,
            &structural_closure,
        );
    VerifiedModule::from_parts(VerifiedModuleParts {
        certificate: cert,
        structural_closure,
        logical_retained_bytes_v1,
    })
}
fn verify_header(header: &CertHeader) -> Result<()> {
    certificate_format_version(header).map(|_| ())
}

fn verify_import_ordering(cert: &ModuleCert) -> Result<()> {
    if !cert.imports().windows(2).all(|pair| {
        (
            pair[0].module.clone(),
            pair[0].export_hash,
            pair[0].certificate_hash,
        ) < (
            pair[1].module.clone(),
            pair[1].export_hash,
            pair[1].certificate_hash,
        )
    }) {
        return Err(CertError::NonCanonicalEncoding { object: "Imports" });
    }
    Ok(())
}

fn verify_name_ordering(cert: &ModuleCert) -> Result<()> {
    if !cert.name_table().windows(2).all(|pair| pair[0] < pair[1]) {
        return Err(CertError::NonCanonicalEncoding {
            object: "NameTable",
        });
    }
    Ok(())
}

fn validate_level_references(cert: &ModuleCert) -> Result<ValidatedLevelReferences> {
    for (index, level) in cert.level_table().iter().enumerate() {
        let ok = match level {
            LevelNode::Zero | LevelNode::Param(_) => true,
            LevelNode::Succ(inner) => *inner < index,
            LevelNode::Max(lhs, rhs) | LevelNode::IMax(lhs, rhs) => *lhs < index && *rhs < index,
        };
        let name_ok = match level {
            LevelNode::Param(name) => *name < cert.name_table().len(),
            _ => true,
        };
        if !ok || !name_ok {
            return Err(CertError::NonCanonicalEncoding {
                object: "LevelTable",
            });
        }
    }
    Ok(ValidatedLevelReferences(()))
}

fn validate_term_references(cert: &ModuleCert) -> Result<ValidatedTermReferences> {
    for (index, term) in cert.term_table().iter().enumerate() {
        let ok = match term {
            TermNode::Sort(_) | TermNode::BVar(_) | TermNode::Const { .. } => true,
            TermNode::App(fun, arg) => *fun < index && *arg < index,
            TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => *ty < index && *body < index,
        };
        let refs_ok = match term {
            TermNode::Sort(level) => *level < cert.level_table().len(),
            TermNode::Const { global_ref, levels } => {
                global_ref_is_in_range(cert, global_ref)
                    && levels.iter().all(|level| *level < cert.level_table().len())
            }
            _ => true,
        };
        if !ok || !refs_ok {
            return Err(CertError::NonCanonicalEncoding {
                object: "TermTable",
            });
        }
    }
    Ok(ValidatedTermReferences(()))
}

fn process_level_table(
    cert: &ModuleCert,
    _references: &ValidatedLevelReferences,
    heights: &[usize],
    observer: &mut ValidationReuseObserver<'_>,
) -> Result<Vec<Hash>> {
    let mut hashes = Vec::with_capacity(cert.level_table().len());
    let mut previous_height = None;
    let mut previous_key = Vec::new();
    let mut current_key = Vec::new();
    for (index, level) in cert.level_table().iter().enumerate() {
        current_key.clear();
        let capacity_before = current_key.capacity();
        encode_level_node_key_to(&mut current_key, level, &hashes, cert.name_table())?;
        observer.increment(ValidationReuseMetric::LevelKeyEncodings);
        observer.add(
            ValidationReuseMetric::KeyScratchAllocatedBytes,
            current_key.capacity().saturating_sub(capacity_before),
        );
        let height = heights[index];
        if previous_height.is_some_and(|previous| {
            previous > height
                || (previous == height && previous_key.as_slice() >= current_key.as_slice())
        }) {
            return Err(CertError::NonCanonicalEncoding {
                object: "LevelTable",
            });
        }
        hashes.push(hash_with_domain(b"NPA-LEVEL-0.1", &current_key));
        previous_height = Some(height);
        std::mem::swap(&mut previous_key, &mut current_key);
    }
    observer.increment(ValidationReuseMetric::LevelHashPasses);
    Ok(hashes)
}

fn process_term_table(
    cert: &ModuleCert,
    _references: &ValidatedTermReferences,
    level_hashes: &[Hash],
    heights: &[usize],
    observer: &mut ValidationReuseObserver<'_>,
) -> Result<Vec<Hash>> {
    let mut hashes = Vec::with_capacity(cert.term_table().len());
    let mut previous_height = None;
    let mut previous_key = Vec::new();
    let mut current_key = Vec::new();
    for (index, term) in cert.term_table().iter().enumerate() {
        current_key.clear();
        let capacity_before = current_key.capacity();
        encode_term_node_key_to(&mut current_key, term, &hashes, level_hashes)?;
        observer.increment(ValidationReuseMetric::TermKeyEncodings);
        observer.add(
            ValidationReuseMetric::KeyScratchAllocatedBytes,
            current_key.capacity().saturating_sub(capacity_before),
        );
        let height = heights[index];
        if previous_height.is_some_and(|previous| {
            previous > height
                || (previous == height && previous_key.as_slice() >= current_key.as_slice())
        }) {
            return Err(CertError::NonCanonicalEncoding {
                object: "TermTable",
            });
        }
        hashes.push(hash_with_domain(b"NPA-TERM-0.1", &current_key));
        previous_height = Some(height);
        std::mem::swap(&mut previous_key, &mut current_key);
    }
    observer.increment(ValidationReuseMetric::TermHashPasses);
    Ok(hashes)
}

fn verify_tables(
    cert: &ModuleCert,
    observer: &mut ValidationReuseObserver<'_>,
) -> Result<ValidatedCertificateTables> {
    verify_import_ordering(cert)?;
    verify_name_ordering(cert)?;
    let level_references = validate_level_references(cert)?;
    if !level_table_is_normalized(cert)? {
        return Err(CertError::NonCanonicalEncoding {
            object: "LevelTable",
        });
    }
    let level_heights = level_node_heights(cert.level_table(), &level_references);
    let level_hashes = process_level_table(cert, &level_references, &level_heights, observer)?;
    let term_references = validate_term_references(cert)?;
    let term_heights = term_node_heights(cert.term_table(), &term_references);
    let term_hashes = process_term_table(
        cert,
        &term_references,
        &level_hashes,
        &term_heights,
        observer,
    )?;
    verify_decl_universe_contexts(cert)?;
    verify_reachable_tables_and_bvars(cert)?;
    verify_name_table_reachable(cert)?;
    Ok(ValidatedCertificateTables {
        level_hashes,
        term_hashes,
    })
}

fn verify_name_table_reachable(cert: &ModuleCert) -> Result<()> {
    let mut names = BTreeSet::new();
    names.insert(cert.header().module.clone());
    for import in cert.imports() {
        names.insert(import.module.clone());
    }

    for level in cert.level_table() {
        collect_level_node_names(cert, level, &mut names)?;
    }
    for term in cert.term_table() {
        collect_term_node_names(cert, term, &mut names)?;
    }
    for decl in cert.declarations() {
        collect_decl_payload_names(cert, &decl.decl, &mut names)?;
        collect_dependency_entry_names(cert, &decl.dependencies, &mut names)?;
        collect_axiom_ref_names(cert, &decl.axiom_dependencies, &mut names)?;
    }
    for entry in cert.export_block() {
        collect_name_id(cert, entry.name, &mut names)?;
        collect_name_ids(cert, &entry.universe_params, &mut names)?;
        collect_universe_constraint_names(cert, &entry.universe_constraints, &mut names)?;
        collect_axiom_ref_names(cert, &entry.axiom_dependencies, &mut names)?;
    }
    for report in &cert.axiom_report().per_declaration {
        collect_axiom_ref_names(cert, &report.direct_axioms, &mut names)?;
        collect_axiom_ref_names(cert, &report.transitive_axioms, &mut names)?;
    }
    collect_axiom_ref_names(cert, &cert.axiom_report().module_axioms, &mut names)?;

    let expected = names.into_iter().collect::<Vec<_>>();
    if expected != cert.name_table() {
        return Err(CertError::NonCanonicalEncoding {
            object: "NameTable",
        });
    }
    Ok(())
}

fn verify_decl_universe_contexts(cert: &ModuleCert) -> Result<()> {
    for decl in cert.declarations() {
        let params = decl_universe_params(&decl.decl);
        let constraints = decl_universe_constraints(&decl.decl);
        if decl_has_empty_constrained_universe_payload(&decl.decl) {
            return Err(CertError::NonCanonicalEncoding {
                object: "UniverseConstraints",
            });
        }
        let param_names = universe_names(cert, params)?;
        let delta =
            npa_kernel::level::validate_universe_params(&param_names).map_err(CertError::Kernel)?;
        let kernel_constraints = constraints
            .iter()
            .map(|constraint| {
                Ok(npa_kernel::UniverseConstraint {
                    lhs: level_from_node(cert, constraint.lhs)?,
                    relation: constraint.relation,
                    rhs: level_from_node(cert, constraint.rhs)?,
                })
            })
            .collect::<Result<Vec<_>>>()?;
        npa_kernel::level::ensure_universe_constraints_wf(&delta, &kernel_constraints)
            .map_err(CertError::Kernel)?;
    }
    Ok(())
}

fn decl_has_empty_constrained_universe_payload(decl: &DeclPayload) -> bool {
    match decl {
        DeclPayload::AxiomConstrained {
            universe_constraints,
            ..
        }
        | DeclPayload::DefConstrained {
            universe_constraints,
            ..
        }
        | DeclPayload::TheoremConstrained {
            universe_constraints,
            ..
        }
        | DeclPayload::InductiveConstrained {
            universe_constraints,
            ..
        } => universe_constraints.is_empty(),
        DeclPayload::Axiom { .. }
        | DeclPayload::Def { .. }
        | DeclPayload::Theorem { .. }
        | DeclPayload::Inductive { .. }
        | DeclPayload::MutualInductiveBlock { .. } => false,
    }
}

fn collect_level_node_names(
    cert: &ModuleCert,
    level: &LevelNode,
    names: &mut BTreeSet<Name>,
) -> Result<()> {
    if let LevelNode::Param(name) = level {
        collect_name_id(cert, *name, names)?;
    }
    Ok(())
}

fn collect_term_node_names(
    cert: &ModuleCert,
    term: &TermNode,
    names: &mut BTreeSet<Name>,
) -> Result<()> {
    if let TermNode::Const { global_ref, .. } = term {
        collect_global_ref_names(cert, global_ref, names)?;
    }
    Ok(())
}

fn collect_decl_payload_names(
    cert: &ModuleCert,
    decl: &DeclPayload,
    names: &mut BTreeSet<Name>,
) -> Result<()> {
    match decl {
        DeclPayload::Axiom {
            name,
            universe_params,
            ..
        }
        | DeclPayload::AxiomConstrained {
            name,
            universe_params,
            ..
        }
        | DeclPayload::Def {
            name,
            universe_params,
            ..
        }
        | DeclPayload::DefConstrained {
            name,
            universe_params,
            ..
        }
        | DeclPayload::Theorem {
            name,
            universe_params,
            ..
        }
        | DeclPayload::TheoremConstrained {
            name,
            universe_params,
            ..
        } => {
            collect_name_id(cert, *name, names)?;
            collect_name_ids(cert, universe_params, names)?;
            collect_universe_constraint_names(cert, decl_universe_constraints(decl), names)?;
        }
        DeclPayload::Inductive {
            name,
            universe_params,
            constructors,
            recursor,
            ..
        }
        | DeclPayload::InductiveConstrained {
            name,
            universe_params,
            constructors,
            recursor,
            ..
        } => {
            collect_name_id(cert, *name, names)?;
            collect_name_ids(cert, universe_params, names)?;
            collect_universe_constraint_names(cert, decl_universe_constraints(decl), names)?;
            for constructor in constructors {
                collect_name_id(cert, constructor.name, names)?;
            }
            if let Some(recursor) = recursor {
                collect_name_id(cert, recursor.name, names)?;
                collect_name_ids(cert, &recursor.universe_params, names)?;
            }
        }
        DeclPayload::MutualInductiveBlock {
            name,
            universe_params,
            inductives,
            ..
        } => {
            collect_name_id(cert, *name, names)?;
            collect_name_ids(cert, universe_params, names)?;
            collect_universe_constraint_names(cert, decl_universe_constraints(decl), names)?;
            for inductive in inductives {
                collect_name_id(cert, inductive.name, names)?;
                for constructor in &inductive.constructors {
                    collect_name_id(cert, constructor.name, names)?;
                }
                if let Some(recursor) = &inductive.recursor {
                    collect_name_id(cert, recursor.name, names)?;
                    collect_name_ids(cert, &recursor.universe_params, names)?;
                }
            }
        }
    }
    Ok(())
}

fn collect_dependency_entry_names(
    cert: &ModuleCert,
    dependencies: &[DependencyEntry],
    names: &mut BTreeSet<Name>,
) -> Result<()> {
    for dependency in dependencies {
        collect_global_ref_names(cert, dependency.global_ref(), names)?;
    }
    Ok(())
}

fn collect_axiom_ref_names(
    cert: &ModuleCert,
    axioms: &[AxiomRef],
    names: &mut BTreeSet<Name>,
) -> Result<()> {
    for axiom in axioms {
        collect_global_ref_names(cert, &axiom.global_ref, names)?;
        collect_name_id(cert, axiom.name, names)?;
    }
    Ok(())
}

fn collect_global_ref_names(
    cert: &ModuleCert,
    global_ref: &GlobalRef,
    names: &mut BTreeSet<Name>,
) -> Result<()> {
    match global_ref {
        GlobalRef::Builtin { name, .. }
        | GlobalRef::Imported { name, .. }
        | GlobalRef::LocalGenerated { name, .. } => {
            collect_name_id(cert, *name, names)?;
        }
        GlobalRef::Local { .. } => {}
    }
    Ok(())
}

fn collect_name_ids(cert: &ModuleCert, ids: &[NameId], names: &mut BTreeSet<Name>) -> Result<()> {
    for id in ids {
        collect_name_id(cert, *id, names)?;
    }
    Ok(())
}

fn collect_universe_constraint_names(
    cert: &ModuleCert,
    constraints: &[UniverseConstraintSpec],
    names: &mut BTreeSet<Name>,
) -> Result<()> {
    for constraint in constraints {
        collect_level_names_from_level_id(cert, constraint.lhs, names)?;
        collect_level_names_from_level_id(cert, constraint.rhs, names)?;
    }
    Ok(())
}

fn collect_level_names_from_level_id(
    cert: &ModuleCert,
    level: LevelId,
    names: &mut BTreeSet<Name>,
) -> Result<()> {
    let mut stack = vec![level];
    let mut seen = BTreeSet::new();
    while let Some(level) = stack.pop() {
        if !seen.insert(level) {
            continue;
        }
        match cert
            .level_table()
            .get(level)
            .ok_or(CertError::DecodeError)?
        {
            LevelNode::Zero => {}
            LevelNode::Succ(inner) => stack.push(*inner),
            LevelNode::Max(lhs, rhs) | LevelNode::IMax(lhs, rhs) => {
                stack.push(*rhs);
                stack.push(*lhs);
            }
            LevelNode::Param(name) => collect_name_id(cert, *name, names)?,
        }
    }
    Ok(())
}

fn collect_name_id(cert: &ModuleCert, id: NameId, names: &mut BTreeSet<Name>) -> Result<()> {
    names.insert(
        cert.name_table()
            .get(id)
            .cloned()
            .ok_or(CertError::DecodeError)?,
    );
    Ok(())
}

fn verify_reachable_tables_and_bvars(cert: &ModuleCert) -> Result<()> {
    // Child indices precede parent indices in the term table (verified by the
    // table encoding pass before this function runs), so one forward pass
    // yields every node's loose-bvar upper bound, and per-root verification
    // is an O(1) bound check plus a single-visit reachability walk — the old
    // per-(term, depth) depth-first search re-visited shared subtrees once
    // per distinct depth. The rare failing root replays the original search
    // so the reported error is identical.
    let bounds = term_node_loose_bvar_bounds(cert.term_table())?;
    let mut reachable_terms = vec![false; cert.term_table().len()];

    let mut verify_root = |root: TermId| -> Result<()> {
        if root >= cert.term_table().len() {
            return Err(CertError::DecodeError);
        }
        if bounds[root] > 0 {
            // Cold path: a loose bvar escapes this root. Replay the
            // depth-tracking search to surface the same first error.
            let mut seen_term_depths = BTreeSet::new();
            let mut reachable = BTreeSet::new();
            verify_term_scope(cert, root, 0, &mut seen_term_depths, &mut reachable)?;
        }
        mark_term_reachable(cert.term_table(), root, &mut reachable_terms);
        Ok(())
    };

    for decl in cert.declarations() {
        match &decl.decl {
            DeclPayload::Axiom { ty, .. } | DeclPayload::AxiomConstrained { ty, .. } => {
                verify_root(*ty)?;
            }
            DeclPayload::Def { ty, value, .. } | DeclPayload::DefConstrained { ty, value, .. } => {
                verify_root(*ty)?;
                verify_root(*value)?;
            }
            DeclPayload::Theorem { ty, proof, .. }
            | DeclPayload::TheoremConstrained { ty, proof, .. } => {
                verify_root(*ty)?;
                verify_root(*proof)?;
            }
            DeclPayload::Inductive {
                params,
                indices,
                sort,
                constructors,
                recursor,
                ..
            }
            | DeclPayload::InductiveConstrained {
                params,
                indices,
                sort,
                constructors,
                recursor,
                ..
            } => {
                let ty = inductive_export_type_term_id(cert.term_table(), params, indices, *sort)?;
                verify_root(ty)?;
                for constructor in constructors {
                    verify_root(constructor.ty)?;
                }
                if let Some(recursor) = recursor {
                    verify_root(recursor.ty)?;
                }
            }
            DeclPayload::MutualInductiveBlock { inductives, .. } => {
                for inductive in inductives {
                    let ty = inductive_export_type_term_id(
                        cert.term_table(),
                        &inductive.params,
                        &inductive.indices,
                        inductive.sort,
                    )?;
                    verify_root(ty)?;
                    for constructor in &inductive.constructors {
                        verify_root(constructor.ty)?;
                    }
                    if let Some(recursor) = &inductive.recursor {
                        verify_root(recursor.ty)?;
                    }
                }
            }
        }
    }

    if reachable_terms.iter().filter(|seen| **seen).count() != cert.term_table().len() {
        return Err(CertError::NonCanonicalEncoding {
            object: "TermTable",
        });
    }

    // Every term node is reachable past this point, so level reachability
    // can scan the term table directly.
    let mut reachable_levels = vec![false; cert.level_table().len()];
    for term in cert.term_table() {
        match term {
            TermNode::Sort(level) => collect_level_reachable(cert, *level, &mut reachable_levels)?,
            TermNode::Const { levels, .. } => {
                for level in levels {
                    collect_level_reachable(cert, *level, &mut reachable_levels)?;
                }
            }
            TermNode::BVar(_)
            | TermNode::App(_, _)
            | TermNode::Lam { .. }
            | TermNode::Pi { .. } => {}
        }
    }
    for decl in cert.declarations() {
        for constraint in decl_universe_constraints(&decl.decl) {
            collect_level_reachable(cert, constraint.lhs, &mut reachable_levels)?;
            collect_level_reachable(cert, constraint.rhs, &mut reachable_levels)?;
        }
    }
    for entry in cert.export_block() {
        for constraint in &entry.universe_constraints {
            collect_level_reachable(cert, constraint.lhs, &mut reachable_levels)?;
            collect_level_reachable(cert, constraint.rhs, &mut reachable_levels)?;
        }
    }
    if reachable_levels.iter().filter(|seen| **seen).count() != cert.level_table().len() {
        return Err(CertError::NonCanonicalEncoding {
            object: "LevelTable",
        });
    }

    Ok(())
}

/// Loose-bvar upper bound per table node in one forward pass; children
/// always precede parents in the canonical table, which the encoding pass
/// has verified before this is called.
fn term_node_loose_bvar_bounds(terms: &[TermNode]) -> Result<Vec<u32>> {
    fn child(bounds: &[u32], index: usize) -> Result<u32> {
        bounds.get(index).copied().ok_or(CertError::DecodeError)
    }
    let mut bounds = Vec::with_capacity(terms.len());
    for term in terms {
        let bound = match term {
            TermNode::Sort(_) | TermNode::Const { .. } => 0,
            TermNode::BVar(index) => index.saturating_add(1),
            TermNode::App(fun, arg) => child(&bounds, *fun)?.max(child(&bounds, *arg)?),
            TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => {
                child(&bounds, *ty)?.max(child(&bounds, *body)?.saturating_sub(1))
            }
        };
        bounds.push(bound);
    }
    Ok(bounds)
}

fn mark_term_reachable(terms: &[TermNode], root: TermId, reachable: &mut [bool]) {
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if reachable[term] {
            continue;
        }
        reachable[term] = true;
        match &terms[term] {
            TermNode::Sort(_) | TermNode::BVar(_) | TermNode::Const { .. } => {}
            TermNode::App(fun, arg) => {
                stack.push(*arg);
                stack.push(*fun);
            }
            TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => {
                stack.push(*body);
                stack.push(*ty);
            }
        }
    }
}

fn verify_term_scope(
    cert: &ModuleCert,
    term: TermId,
    depth: u32,
    seen: &mut BTreeSet<(TermId, u32)>,
    reachable_terms: &mut BTreeSet<TermId>,
) -> Result<()> {
    let mut stack = vec![(term, depth)];
    while let Some((term, depth)) = stack.pop() {
        if !seen.insert((term, depth)) {
            reachable_terms.insert(term);
            continue;
        }
        reachable_terms.insert(term);
        match cert.term_table().get(term).ok_or(CertError::DecodeError)? {
            TermNode::Sort(_) | TermNode::Const { .. } => {}
            TermNode::BVar(index) => {
                if *index >= depth {
                    return Err(CertError::InvalidBVar { index: *index });
                }
            }
            TermNode::App(fun, arg) => {
                stack.push((*arg, depth));
                stack.push((*fun, depth));
            }
            TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => {
                stack.push((*body, depth.saturating_add(1)));
                stack.push((*ty, depth));
            }
        }
    }
    Ok(())
}

fn collect_level_reachable(
    cert: &ModuleCert,
    level: LevelId,
    reachable_levels: &mut [bool],
) -> Result<()> {
    let mut stack = vec![level];
    while let Some(level) = stack.pop() {
        let node = cert
            .level_table()
            .get(level)
            .ok_or(CertError::DecodeError)?;
        if reachable_levels[level] {
            continue;
        }
        reachable_levels[level] = true;
        match node {
            LevelNode::Zero | LevelNode::Param(_) => {}
            LevelNode::Succ(inner) => stack.push(*inner),
            LevelNode::Max(lhs, rhs) | LevelNode::IMax(lhs, rhs) => {
                stack.push(*rhs);
                stack.push(*lhs);
            }
        }
    }
    Ok(())
}

fn verify_hashes_through_export(
    cert: &ModuleCert,
    tables: &ValidatedCertificateTables,
) -> Result<PendingCertificateHashChecks> {
    let version = certificate_format_version(cert.header())?;
    for decl in cert.declarations() {
        let expected = compute_decl_hashes(
            version,
            &decl.decl,
            &decl.dependencies,
            &decl.axiom_dependencies,
            DeclHashTables {
                terms: cert.term_table(),
                level_hashes: &tables.level_hashes,
                term_hashes: &tables.term_hashes,
                names: cert.name_table(),
            },
        )?;
        if expected.decl_interface_hash != decl.hashes.decl_interface_hash {
            return Err(CertError::HashMismatch {
                object: HashObject::DeclInterface,
                expected: decl.hashes.decl_interface_hash,
                actual: expected.decl_interface_hash,
            });
        }
        if expected.decl_certificate_hash != decl.hashes.decl_certificate_hash {
            return Err(CertError::HashMismatch {
                object: HashObject::DeclCertificate,
                expected: decl.hashes.decl_certificate_hash,
                actual: expected.decl_certificate_hash,
            });
        }
    }

    let expected_export_block =
        build_export_block(cert.declarations(), cert.term_table(), &tables.term_hashes)?;
    let export_domain = MODULE_EXPORT_DOMAIN;
    let export_bytes = encode_export_block(&expected_export_block);
    Ok(PendingCertificateHashChecks {
        version,
        expected_export_block,
        export_domain,
        export_bytes,
    })
}

fn canonical_certificate_hash_input<'a>(
    canonical: &'a CanonicalCertificateEncoding<'a>,
    version: CertificateFormatVersion,
    observer: &mut ValidationReuseObserver<'_>,
) -> CanonicalCertificateHashInput<'a> {
    match canonical {
        CanonicalCertificateEncoding::AuthoritativeBytes {
            version: encoded_version,
            bytes,
            certificate_hash_input_end,
        } => {
            debug_assert_eq!(*encoded_version, version);
            debug_assert!(*certificate_hash_input_end <= bytes.len());
            observer.increment(ValidationReuseMetric::AuthoritativePrefixUses);
            CanonicalCertificateHashInput::AuthoritativeBytes {
                version: *encoded_version,
                bytes: &bytes[..*certificate_hash_input_end],
            }
        }
        CanonicalCertificateEncoding::Streamed {
            version: encoded_version,
            computed_certificate_hash,
        } => {
            debug_assert_eq!(*encoded_version, version);
            observer.increment(ValidationReuseMetric::StreamedPrehashUses);
            CanonicalCertificateHashInput::StreamedHash {
                version: *encoded_version,
                computed_certificate_hash: *computed_certificate_hash,
            }
        }
    }
}

fn materialize_built_certificate_hash_encoding(
    cert: &ModuleCert,
    version: CertificateFormatVersion,
    observer: &mut ValidationReuseObserver<'_>,
) -> Result<BuiltCertificateHashEncoding> {
    let bytes = encode_module_cert_without_certificate_hash_for_header(cert)?;
    observer.increment(ValidationReuseMetric::LazyBuiltMaterializations);
    Ok(BuiltCertificateHashEncoding { version, bytes })
}

fn verify_pending_export_and_axiom_claims(
    cert: &ModuleCert,
    pending: &PendingCertificateHashChecks,
) -> Result<()> {
    let expected_export = hash_with_domain(pending.export_domain, &pending.export_bytes);
    if pending.expected_export_block != cert.export_block()
        || expected_export != cert.hashes().export_hash
    {
        return Err(CertError::HashMismatch {
            object: HashObject::ExportBlock,
            expected: cert.hashes().export_hash,
            actual: expected_export,
        });
    }

    let expected_axioms = hash_with_domain(
        b"NPA-AXIOM-REPORT-0.1",
        &encode_axiom_report(cert.axiom_report()),
    );
    if expected_axioms != cert.hashes().axiom_report_hash {
        return Err(CertError::HashMismatch {
            object: HashObject::AxiomReport,
            expected: cert.hashes().axiom_report_hash,
            actual: expected_axioms,
        });
    }

    Ok(())
}

#[cfg(test)]
pub(crate) fn verify_module_certificate_hash_from_input_prefix_for_test(
    cert: &ModuleCert,
    version: CertificateFormatVersion,
    prefix: &[u8],
) -> Result<()> {
    let expected_cert = hash_with_domain(version.module_certificate_domain(), prefix);
    if expected_cert == cert.hashes().certificate_hash {
        Ok(())
    } else {
        Err(CertError::HashMismatch {
            object: HashObject::ModuleCertificate,
            expected: cert.hashes().certificate_hash,
            actual: expected_cert,
        })
    }
}

fn verify_hashes_from_canonical_input(
    cert: &ModuleCert,
    tables: &ValidatedCertificateTables,
    canonical: &CanonicalCertificateEncoding<'_>,
    observer: &mut ValidationReuseObserver<'_>,
) -> Result<()> {
    let pending = verify_hashes_through_export(cert, tables)?;
    let hash_input = canonical_certificate_hash_input(canonical, pending.version, observer);
    verify_pending_export_and_axiom_claims(cert, &pending)?;

    let expected_cert = match hash_input {
        CanonicalCertificateHashInput::AuthoritativeBytes { version, bytes } => {
            debug_assert_eq!(version, pending.version);
            hash_with_domain(version.module_certificate_domain(), bytes)
        }
        CanonicalCertificateHashInput::StreamedHash {
            version,
            computed_certificate_hash,
        } => {
            debug_assert_eq!(version, pending.version);
            computed_certificate_hash
        }
    };
    if expected_cert == cert.hashes().certificate_hash {
        Ok(())
    } else {
        Err(CertError::HashMismatch {
            object: HashObject::ModuleCertificate,
            expected: cert.hashes().certificate_hash,
            actual: expected_cert,
        })
    }
}

fn verify_hashes_for_built_certificate(
    cert: &ModuleCert,
    tables: &ValidatedCertificateTables,
    observer: &mut ValidationReuseObserver<'_>,
) -> Result<()> {
    let pending = verify_hashes_through_export(cert, tables)?;
    let encoding = materialize_built_certificate_hash_encoding(cert, pending.version, observer)?;
    verify_pending_export_and_axiom_claims(cert, &pending)?;

    debug_assert_eq!(encoding.version, pending.version);
    let expected_cert = hash_with_domain(
        encoding.version.module_certificate_domain(),
        &encoding.bytes,
    );
    if expected_cert != cert.hashes().certificate_hash {
        return Err(CertError::HashMismatch {
            object: HashObject::ModuleCertificate,
            expected: cert.hashes().certificate_hash,
            actual: expected_cert,
        });
    }

    Ok(())
}

fn verify_declaration_order(cert: &ModuleCert) -> Result<()> {
    let local_names = (0..cert.declarations().len())
        .map(|index| decl_name_as_name(cert, index))
        .collect::<Result<Vec<_>>>()?;
    ensure_unique_names(&local_names)?;
    for name in &local_names {
        if reserved_core_primitive_name(name) {
            return Err(CertError::ReservedCorePrimitive { name: name.clone() });
        }
    }

    let dependencies = cert
        .declarations()
        .iter()
        .enumerate()
        .map(|(decl_index, decl)| {
            let mut deps = BTreeSet::new();
            for dependency in &decl.dependencies {
                if dependency.kind() == DependencyEntryKind::LocalImplementation {
                    if let GlobalRef::Local {
                        decl_index: dependency_index,
                    } = dependency.global_ref()
                    {
                        if *dependency_index < decl_index {
                            deps.insert(*dependency_index);
                        }
                    }
                    continue;
                }
                match dependency.global_ref() {
                    GlobalRef::Local {
                        decl_index: dependency_index,
                    } => {
                        if *dependency_index >= decl_index {
                            return Err(CertError::DependencyCycle {
                                name: local_names[decl_index].clone(),
                            });
                        }
                        deps.insert(*dependency_index);
                    }
                    GlobalRef::LocalGenerated {
                        decl_index: dependency_index,
                        name,
                    } => {
                        if *dependency_index >= decl_index {
                            return Err(CertError::DependencyCycle {
                                name: local_names[decl_index].clone(),
                            });
                        }
                        if !local_generated_entry_exists(cert, *dependency_index, *name)? {
                            return Err(CertError::UnknownDependency {
                                name: cert
                                    .name_table()
                                    .get(*name)
                                    .cloned()
                                    .ok_or(CertError::DecodeError)?,
                            });
                        }
                        deps.insert(*dependency_index);
                    }
                    GlobalRef::Builtin { .. } | GlobalRef::Imported { .. } => {}
                }
            }
            Ok(deps)
        })
        .collect::<Result<Vec<_>>>()?;

    let mut emitted = BTreeSet::new();
    let mut remaining: BTreeSet<_> = (0..cert.declarations().len()).collect();
    let mut expected = Vec::with_capacity(cert.declarations().len());
    while !remaining.is_empty() {
        let mut ready: Vec<_> = remaining
            .iter()
            .copied()
            .filter(|index| dependencies[*index].is_subset(&emitted))
            .collect();
        if ready.is_empty() {
            let index = *remaining.iter().next().ok_or(CertError::DecodeError)?;
            return Err(CertError::DependencyCycle {
                name: local_names[index].clone(),
            });
        }
        ready.sort_by_key(|index| local_names[*index].clone());
        for index in ready {
            remaining.remove(&index);
            emitted.insert(index);
            expected.push(index);
        }
    }

    if expected != (0..cert.declarations().len()).collect::<Vec<_>>() {
        return Err(CertError::NonCanonicalEncoding {
            object: "Declarations",
        });
    }

    Ok(())
}

fn global_ref_is_in_range(cert: &ModuleCert, global_ref: &GlobalRef) -> bool {
    match global_ref {
        GlobalRef::Builtin {
            name,
            decl_interface_hash,
        } => cert
            .name_table()
            .get(*name)
            .is_some_and(|name| builtin_decl_interface_hash(name) == Some(*decl_interface_hash)),
        GlobalRef::Imported {
            import_index, name, ..
        } => *import_index < cert.imports().len() && *name < cert.name_table().len(),
        GlobalRef::Local { decl_index } => *decl_index < cert.declarations().len(),
        GlobalRef::LocalGenerated { decl_index, name } => {
            *decl_index < cert.declarations().len() && *name < cert.name_table().len()
        }
    }
}

fn level_table_is_normalized(cert: &ModuleCert) -> Result<bool> {
    fn tag(node: &LevelNode) -> u8 {
        match node {
            LevelNode::Zero => 0,
            LevelNode::Succ(_) => 1,
            LevelNode::Max(_, _) => 2,
            LevelNode::IMax(_, _) => 3,
            LevelNode::Param(_) => 4,
        }
    }

    fn compare_levels(cert: &ModuleCert, lhs: LevelId, rhs: LevelId) -> Result<std::cmp::Ordering> {
        let mut pending = vec![(lhs, rhs)];
        while let Some((lhs, rhs)) = pending.pop() {
            if lhs == rhs {
                continue;
            }
            let lhs_node = cert.level_table().get(lhs).ok_or(CertError::DecodeError)?;
            let rhs_node = cert.level_table().get(rhs).ok_or(CertError::DecodeError)?;
            let tag_order = tag(lhs_node).cmp(&tag(rhs_node));
            if tag_order != std::cmp::Ordering::Equal {
                return Ok(tag_order);
            }
            match (lhs_node, rhs_node) {
                (LevelNode::Zero, LevelNode::Zero) => {}
                (LevelNode::Succ(lhs), LevelNode::Succ(rhs)) => pending.push((*lhs, *rhs)),
                (LevelNode::Max(lhs_l, lhs_r), LevelNode::Max(rhs_l, rhs_r))
                | (LevelNode::IMax(lhs_l, lhs_r), LevelNode::IMax(rhs_l, rhs_r)) => {
                    pending.push((*lhs_r, *rhs_r));
                    pending.push((*lhs_l, *rhs_l));
                }
                (LevelNode::Param(lhs), LevelNode::Param(rhs)) => {
                    let lhs = cert
                        .name_table()
                        .get(*lhs)
                        .ok_or(CertError::DecodeError)?
                        .as_dotted();
                    let rhs = cert
                        .name_table()
                        .get(*rhs)
                        .ok_or(CertError::DecodeError)?
                        .as_dotted();
                    let order = lhs.cmp(&rhs);
                    if order != std::cmp::Ordering::Equal {
                        return Ok(order);
                    }
                }
                _ => return Err(CertError::DecodeError),
            }
        }
        Ok(std::cmp::Ordering::Equal)
    }

    let mut naturals: Vec<Option<u64>> = Vec::with_capacity(cert.level_table().len());
    for (index, node) in cert.level_table().iter().enumerate() {
        let natural = match node {
            LevelNode::Zero => Some(0u64),
            LevelNode::Succ(inner) => naturals
                .get(*inner)
                .copied()
                .flatten()
                .and_then(|value| value.checked_add(1)),
            LevelNode::Param(_) | LevelNode::Max(_, _) | LevelNode::IMax(_, _) => None,
        };
        let normalized = match node {
            LevelNode::Zero | LevelNode::Param(_) | LevelNode::Succ(_) => true,
            LevelNode::Max(lhs, rhs) => {
                *lhs != *rhs
                    && !matches!(cert.level_table().get(*lhs), Some(LevelNode::Zero))
                    && !matches!(cert.level_table().get(*rhs), Some(LevelNode::Zero))
                    && !(naturals.get(*lhs).is_some_and(Option::is_some)
                        && naturals.get(*rhs).is_some_and(Option::is_some))
                    && compare_levels(cert, *lhs, *rhs)? != std::cmp::Ordering::Greater
            }
            LevelNode::IMax(_, rhs) => !matches!(
                cert.level_table().get(*rhs),
                Some(LevelNode::Zero | LevelNode::Succ(_))
            ),
        };
        if !normalized {
            return Ok(false);
        }
        if matches!(node, LevelNode::Succ(inner) if *inner >= index) {
            return Err(CertError::DecodeError);
        }
        naturals.push(natural);
    }
    Ok(true)
}

/// Computes every level node's height in one forward pass. Children always
/// precede their parents in a canonically encoded table (verified by the
/// caller before the heights are needed), so each height is derived from
/// already-computed child heights.
fn level_node_heights(levels: &[LevelNode], _references: &ValidatedLevelReferences) -> Vec<usize> {
    fn child(heights: &[usize], index: usize) -> usize {
        debug_assert!(index < heights.len());
        heights[index]
    }
    let mut heights = Vec::with_capacity(levels.len());
    for level in levels {
        let height = match level {
            LevelNode::Zero | LevelNode::Param(_) => 0,
            LevelNode::Succ(inner) => child(&heights, *inner) + 1,
            LevelNode::Max(lhs, rhs) | LevelNode::IMax(lhs, rhs) => {
                child(&heights, *lhs).max(child(&heights, *rhs)) + 1
            }
        };
        heights.push(height);
    }
    heights
}

/// Computes every term node's height in one forward pass; same
/// child-precedes-parent reasoning as [`level_node_heights`].
fn term_node_heights(terms: &[TermNode], _references: &ValidatedTermReferences) -> Vec<usize> {
    fn child(heights: &[usize], index: usize) -> usize {
        debug_assert!(index < heights.len());
        heights[index]
    }
    let mut heights = Vec::with_capacity(terms.len());
    for term in terms {
        let height = match term {
            TermNode::Sort(_) | TermNode::BVar(_) | TermNode::Const { .. } => 0,
            TermNode::App(fun, arg) => child(&heights, *fun).max(child(&heights, *arg)) + 1,
            TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => {
                child(&heights, *ty).max(child(&heights, *body)) + 1
            }
        };
        heights.push(height);
    }
    heights
}

fn resolve_imports<'a>(
    cert: &ModuleCert,
    session: &'a VerifierSession,
    policy: &AxiomPolicy,
) -> Result<Vec<&'a dyn CertificateImportView>> {
    let mut imports: Vec<&'a dyn CertificateImportView> = Vec::new();
    for entry in cert.imports() {
        if policy.mode == TrustMode::HighTrust && entry.certificate_hash.is_none() {
            return Err(CertError::MissingImportCertificateHash {
                module: entry.module.clone(),
            });
        }
        imports.push(session.find_import(entry, policy.mode)?);
    }
    Ok(imports)
}

fn resolve_import_refs<'a>(
    cert: &ModuleCert,
    available_imports: &'a [&'a VerifiedModule],
    policy: &AxiomPolicy,
) -> Result<Vec<&'a dyn CertificateImportView>> {
    let mut imports: Vec<&'a dyn CertificateImportView> = Vec::new();
    for entry in cert.imports() {
        if policy.mode == TrustMode::HighTrust && entry.certificate_hash.is_none() {
            return Err(CertError::MissingImportCertificateHash {
                module: entry.module.clone(),
            });
        }
        imports.push(find_import_ref(available_imports, entry, policy.mode)?);
    }
    Ok(imports)
}

fn resolve_import_views<'a>(
    cert: &ModuleCert,
    available_imports: &'a [&'a dyn CertificateImportView],
    policy: &AxiomPolicy,
) -> Result<Vec<&'a dyn CertificateImportView>> {
    let mut imports = Vec::with_capacity(cert.imports().len());
    for entry in cert.imports() {
        if policy.mode == TrustMode::HighTrust && entry.certificate_hash.is_none() {
            return Err(CertError::MissingImportCertificateHash {
                module: entry.module.clone(),
            });
        }
        imports.push(find_import_view(available_imports, entry, policy.mode)?);
    }
    Ok(imports)
}

fn find_import_ref<'a>(
    available_imports: &'a [&'a VerifiedModule],
    entry: &ImportEntry,
    mode: TrustMode,
) -> Result<&'a VerifiedModule> {
    let module_export_matches = available_imports.iter().any(|module| {
        module.module() == &entry.module && module.export_hash() == entry.export_hash
    });

    let found = available_imports.iter().copied().find(|module| {
        module.module() == &entry.module
            && module.export_hash() == entry.export_hash
            && match (mode, entry.certificate_hash) {
                (TrustMode::Normal, None) => true,
                (_, Some(hash)) => module.certificate_hash() == hash,
                (TrustMode::HighTrust, None) => false,
            }
    });

    if let Some(module) = found {
        return Ok(module);
    }

    if mode == TrustMode::HighTrust && !module_export_matches {
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

fn find_import_view<'a>(
    available_imports: &'a [&'a dyn CertificateImportView],
    entry: &ImportEntry,
    mode: TrustMode,
) -> Result<&'a dyn CertificateImportView> {
    let module_export_matches = available_imports.iter().any(|module| {
        module.module() == &entry.module && module.export_hash() == entry.export_hash
    });

    let found = available_imports.iter().copied().find(|module| {
        module.module() == &entry.module
            && module.export_hash() == entry.export_hash
            && match (mode, entry.certificate_hash) {
                (TrustMode::Normal, None) => true,
                (_, Some(hash)) => module.certificate_hash() == hash,
                (TrustMode::HighTrust, None) => false,
            }
    });

    if let Some(module) = found {
        return Ok(module);
    }
    if mode == TrustMode::HighTrust && !module_export_matches {
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

fn add_referenced_imports_to_env(
    env: &mut Env,
    cert: &ModuleCert,
    imports: &[&dyn CertificateImportView],
    budget: &mut TermMaterializationBudgetV1,
    mut observation: Option<&mut CertificateTermMaterializationObservation>,
) -> Result<()> {
    let attempt = add_referenced_imports_to_env_planned(
        env,
        cert.declarations(),
        cert.name_table(),
        imports,
        budget,
        observation.as_deref_mut(),
    );
    match attempt {
        MaterializationAttempt::Ready(result) => result,
        MaterializationAttempt::Fallback(stop) => {
            if let Some(observation) = observation {
                if stop == MaterializationStop::Capacity {
                    observation.observe_capacity_stop();
                }
                observation.observe_legacy_fallback();
            }
            add_referenced_imports_to_env_legacy(env, cert, imports)
        }
    }
}

fn add_referenced_imports_to_env_legacy(
    env: &mut Env,
    cert: &ModuleCert,
    imports: &[&dyn CertificateImportView],
) -> Result<()> {
    let mut loader = ReferencedImportLoader {
        imports,
        loaded: BTreeSet::new(),
        loading: BTreeSet::new(),
    };
    let mut refs = BTreeSet::new();
    for decl in cert.declarations() {
        for dependency in &decl.dependencies {
            refs.insert(dependency.global_ref().clone());
        }
    }
    for global_ref in refs {
        match global_ref {
            GlobalRef::Builtin {
                name,
                decl_interface_hash,
            } => add_builtin_ref_to_env(env, cert.name_table(), name, decl_interface_hash)?,
            GlobalRef::Imported { .. } => {
                loader.load_imported_global_ref_from_cert(env, cert, &global_ref)?;
            }
            GlobalRef::Local { .. } | GlobalRef::LocalGenerated { .. } => {}
        }
    }
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ExactImportedModuleIdentity {
    module: Name,
    export_hash: Hash,
    certificate_hash: Hash,
}

struct PlannedImportedModule<'a> {
    identity: ExactImportedModuleIdentity,
    source: &'a (dyn CertificateImportView + 'a),
    declaration_state: Vec<u8>,
    roots: Vec<TermId>,
    table_plan: Option<SelectedTermMaterializationPlan>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ExportEntryIdentity {
    module_slot: usize,
    export_index: usize,
    source_decl_index: usize,
}

#[derive(Debug, PartialEq, Eq)]
enum ImportedBuiltinOwner {
    Current,
    Imported {
        module_slot: usize,
        identity: ExactImportedModuleIdentity,
    },
}

#[derive(Debug, PartialEq, Eq)]
enum ImportedLoadAction {
    Builtin {
        owner: ImportedBuiltinOwner,
        name: NameId,
        decl_interface_hash: Hash,
    },
    Declaration {
        key: ImportedDeclKey,
        export: ExportEntryIdentity,
    },
}

struct PlannedImportLoader<'a> {
    imports: &'a [&'a dyn CertificateImportView],
    modules: Vec<PlannedImportedModule<'a>>,
    actions: Vec<ImportedLoadAction>,
    action_capacity: usize,
}

const _: () = {
    assert!(
        std::mem::size_of::<ExactImportedModuleIdentity>()
            <= TERM_PLANNER_RECORD_CHARGE_BYTES_V1 as usize
    );
    assert!(
        std::mem::size_of::<PlannedImportedModule<'static>>()
            <= TERM_PLANNER_RECORD_CHARGE_BYTES_V1 as usize
    );
    assert!(
        std::mem::size_of::<ExportEntryIdentity>() <= TERM_PLANNER_RECORD_CHARGE_BYTES_V1 as usize
    );
    assert!(
        std::mem::size_of::<ImportedBuiltinOwner>() <= TERM_PLANNER_RECORD_CHARGE_BYTES_V1 as usize
    );
    assert!(
        std::mem::size_of::<ImportedLoadAction>() <= TERM_PLANNER_RECORD_CHARGE_BYTES_V1 as usize
    );
    assert!(std::mem::size_of::<ImportedDeclKey>() <= TERM_PLANNER_RECORD_CHARGE_BYTES_V1 as usize);
};

fn try_clone_planner_name(name: &Name) -> std::result::Result<Name, MaterializationStop> {
    let mut components = Vec::new();
    components
        .try_reserve_exact(name.0.len())
        .map_err(|_| MaterializationStop::Capacity)?;
    for component in &name.0 {
        let mut cloned = String::new();
        cloned
            .try_reserve_exact(component.len())
            .map_err(|_| MaterializationStop::Capacity)?;
        cloned.push_str(component);
        components.push(cloned);
    }
    Ok(Name(components))
}

fn planner_name_charge(name: &Name) -> Option<u64> {
    let component_slots = u64::try_from(name.0.len())
        .ok()?
        .checked_mul(TERM_PLANNER_NAME_COMPONENT_CHARGE_BYTES_V1)?;
    name.0.iter().try_fold(component_slots, |total, component| {
        total.checked_add(u64::try_from(component.len()).ok()?)
    })
}

fn try_exact_imported_module_identity(
    module: &dyn CertificateImportView,
) -> std::result::Result<ExactImportedModuleIdentity, MaterializationStop> {
    Ok(ExactImportedModuleIdentity {
        module: try_clone_planner_name(module.module())?,
        export_hash: module.export_hash(),
        certificate_hash: module.certificate_hash(),
    })
}

fn try_clone_exact_imported_module_identity(
    identity: &ExactImportedModuleIdentity,
) -> std::result::Result<ExactImportedModuleIdentity, MaterializationStop> {
    Ok(ExactImportedModuleIdentity {
        module: try_clone_planner_name(&identity.module)?,
        export_hash: identity.export_hash,
        certificate_hash: identity.certificate_hash,
    })
}

fn checked_planner_records(count: usize) -> Option<u64> {
    u64::try_from(count)
        .ok()?
        .checked_mul(TERM_PLANNER_RECORD_CHARGE_BYTES_V1)
}

fn imported_module_root_capacity(module: &dyn CertificateImportView) -> Option<usize> {
    module
        .export_block()
        .iter()
        .try_fold(0_usize, |total, entry| {
            let count = match entry.kind {
                ExportKind::Axiom | ExportKind::Theorem => 1,
                ExportKind::Def => 2,
                ExportKind::Inductive | ExportKind::Constructor | ExportKind::Recursor => {
                    let decl_index = source_decl_index_for_export_entry(module, entry).ok()?;
                    decl_payload_term_root_count(&module.declarations().get(decl_index)?.decl)?
                }
            };
            total.checked_add(count)
        })
}

fn collect_imported_kernel_refs_for_export_planned(
    module: &dyn CertificateImportView,
    entry: &ExportEntry,
) -> std::result::Result<Vec<GlobalRef>, MaterializationStop> {
    let mut roots = Vec::new();
    match entry.kind {
        ExportKind::Inductive | ExportKind::Constructor | ExportKind::Recursor => {
            let decl_index = source_decl_index_for_export_entry(module, entry)
                .map_err(|_| MaterializationStop::SpeculativeInvariant)?;
            let decl = module
                .declarations()
                .get(decl_index)
                .ok_or(MaterializationStop::SpeculativeInvariant)?;
            let root_count =
                decl_payload_term_root_count(&decl.decl).ok_or(MaterializationStop::Capacity)?;
            roots
                .try_reserve_exact(root_count)
                .map_err(|_| MaterializationStop::Capacity)?;
            collect_decl_payload_term_roots(&decl.decl, &mut roots);
        }
        ExportKind::Axiom | ExportKind::Theorem | ExportKind::Def => {
            let root_count = 1_usize.saturating_add(usize::from(entry.body.is_some()));
            roots
                .try_reserve_exact(root_count)
                .map_err(|_| MaterializationStop::Capacity)?;
            roots.push(entry.ty);
            if let Some(body) = entry.body {
                roots.push(body);
            }
        }
    }

    let table_len = module.term_table().len();
    let mut selected = Vec::new();
    selected
        .try_reserve_exact(table_len)
        .map_err(|_| MaterializationStop::Capacity)?;
    selected.resize(table_len, 0_u8);
    let mut pending = Vec::new();
    pending
        .try_reserve_exact(table_len)
        .map_err(|_| MaterializationStop::Capacity)?;
    let mut refs = Vec::new();
    refs.try_reserve_exact(table_len)
        .map_err(|_| MaterializationStop::Capacity)?;

    for root in roots.into_iter().rev() {
        if root >= table_len {
            return Err(MaterializationStop::SpeculativeInvariant);
        }
        if selected[root] == 0 {
            selected[root] = 1;
            pending.push(root);
        }
    }
    while let Some(term) = pending.pop() {
        let node = module
            .term_table()
            .get(term)
            .ok_or(MaterializationStop::SpeculativeInvariant)?;
        if let TermNode::Const { global_ref, .. } = node {
            refs.push(global_ref.clone());
        }
        let mut push_child = |child: TermId| {
            if child >= term || child >= table_len {
                return Err(MaterializationStop::SpeculativeInvariant);
            }
            if selected[child] == 0 {
                selected[child] = 1;
                pending.push(child);
            }
            Ok(())
        };
        match node {
            TermNode::Sort(_) | TermNode::BVar(_) | TermNode::Const { .. } => {}
            TermNode::App(fun, arg) => {
                push_child(*arg)?;
                push_child(*fun)?;
            }
            TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => {
                push_child(*body)?;
                push_child(*ty)?;
            }
        }
    }
    refs.sort();
    refs.dedup();
    if matches!(
        entry.kind,
        ExportKind::Inductive | ExportKind::Constructor | ExportKind::Recursor
    ) {
        let decl_index = source_decl_index_for_export_entry(module, entry)
            .map_err(|_| MaterializationStop::SpeculativeInvariant)?;
        refs.retain(|global_ref| {
            !matches!(
                global_ref,
                GlobalRef::Local {
                    decl_index: local_decl_index
                } | GlobalRef::LocalGenerated {
                    decl_index: local_decl_index,
                    ..
                } if *local_decl_index == decl_index
            )
        });
    }
    Ok(refs)
}

fn append_export_entry_roots_planned(
    module: &dyn CertificateImportView,
    entry: &ExportEntry,
    destination: &mut Vec<TermId>,
) -> std::result::Result<(), MaterializationStop> {
    let root_count = match entry.kind {
        ExportKind::Axiom | ExportKind::Theorem => 1,
        ExportKind::Def => 1_usize
            .checked_add(usize::from(
                entry.reducibility == Some(CertReducibility::Reducible),
            ))
            .ok_or(MaterializationStop::Capacity)?,
        ExportKind::Inductive | ExportKind::Constructor | ExportKind::Recursor => {
            let decl_index = source_decl_index_for_export_entry(module, entry)
                .map_err(|_| MaterializationStop::SpeculativeInvariant)?;
            let decl = module
                .declarations()
                .get(decl_index)
                .ok_or(MaterializationStop::SpeculativeInvariant)?;
            decl_payload_term_root_count(&decl.decl).ok_or(MaterializationStop::Capacity)?
        }
    };
    if destination.capacity().saturating_sub(destination.len()) < root_count {
        return Err(MaterializationStop::Capacity);
    }
    match entry.kind {
        ExportKind::Axiom | ExportKind::Theorem => destination.push(entry.ty),
        ExportKind::Def => {
            destination.push(entry.ty);
            if entry.reducibility == Some(CertReducibility::Reducible) {
                destination.push(
                    entry
                        .body
                        .ok_or(MaterializationStop::SpeculativeInvariant)?,
                );
            }
        }
        ExportKind::Inductive | ExportKind::Constructor | ExportKind::Recursor => {
            let decl_index = source_decl_index_for_export_entry(module, entry)
                .map_err(|_| MaterializationStop::SpeculativeInvariant)?;
            let decl = module
                .declarations()
                .get(decl_index)
                .ok_or(MaterializationStop::SpeculativeInvariant)?;
            collect_decl_payload_term_roots(&decl.decl, destination);
        }
    }
    Ok(())
}

fn imported_planner_preflight(
    declarations: &[DeclCert],
    imports: &[&dyn CertificateImportView],
    budget: &TermMaterializationBudgetV1,
    mut observation: Option<&mut CertificateTermMaterializationObservation>,
) -> std::result::Result<usize, MaterializationStop> {
    let top_reference_capacity = declarations
        .iter()
        .try_fold(0_usize, |total, decl| {
            total.checked_add(decl.dependencies.len())
        })
        .ok_or_else(|| {
            if let Some(observation) = observation.as_deref_mut() {
                observation.observe_overflow();
            }
            MaterializationStop::Capacity
        })?;
    imported_planner_preflight_for_reference_capacity(
        top_reference_capacity,
        imports,
        budget,
        observation,
    )
}

fn imported_planner_preflight_for_reference_capacity(
    top_reference_capacity: usize,
    imports: &[&dyn CertificateImportView],
    budget: &TermMaterializationBudgetV1,
    mut observation: Option<&mut CertificateTermMaterializationObservation>,
) -> std::result::Result<usize, MaterializationStop> {
    let mut action_capacity = top_reference_capacity;
    let mut planner_records = imports.len();
    let mut conservative_tables = 0_u64;
    let mut retained_module_name_charge = 0_u64;
    let mut largest_module_name_charge = 0_u64;
    for module in imports {
        let Some(module_name_charge) = planner_name_charge(module.module()) else {
            if let Some(observation) = observation.as_deref_mut() {
                observation.observe_overflow();
            }
            return Err(MaterializationStop::Capacity);
        };
        retained_module_name_charge = retained_module_name_charge
            .checked_add(module_name_charge)
            .ok_or_else(|| {
                if let Some(observation) = observation.as_deref_mut() {
                    observation.observe_overflow();
                }
                MaterializationStop::Capacity
            })?;
        largest_module_name_charge = largest_module_name_charge.max(module_name_charge);
        let declarations = module.declarations().len();
        let dependencies = module
            .declarations()
            .iter()
            .try_fold(0_usize, |total, decl| {
                total.checked_add(decl.dependencies.len())
            });
        let roots = imported_module_root_capacity(*module);
        let Some((dependencies, roots)) = dependencies.zip(roots) else {
            if let Some(observation) = observation.as_deref_mut() {
                observation.observe_overflow();
            }
            return Err(MaterializationStop::Capacity);
        };
        action_capacity = action_capacity
            .checked_add(dependencies)
            .and_then(|value| value.checked_add(declarations))
            .ok_or_else(|| {
                if let Some(observation) = observation.as_deref_mut() {
                    observation.observe_overflow();
                }
                MaterializationStop::Capacity
            })?;
        planner_records = planner_records
            .checked_add(declarations)
            .and_then(|value| value.checked_add(roots))
            .and_then(|value| value.checked_add(dependencies))
            .and_then(|value| value.checked_add(module.term_table().len()))
            .and_then(|value| value.checked_add(module.term_table().len()))
            .and_then(|value| value.checked_add(module.term_table().len()))
            .ok_or_else(|| {
                if let Some(observation) = observation.as_deref_mut() {
                    observation.observe_overflow();
                }
                MaterializationStop::Capacity
            })?;
        let Some(table_bound) =
            KernelExprMaterialization::conservative_all_roots_selected_charge(*module)
        else {
            if let Some(observation) = observation.as_deref_mut() {
                observation.observe_overflow();
            }
            return Err(MaterializationStop::Capacity);
        };
        conservative_tables = conservative_tables
            .checked_add(table_bound)
            .ok_or_else(|| {
                if let Some(observation) = observation.as_deref_mut() {
                    observation.observe_overflow();
                }
                MaterializationStop::Capacity
            })?;
    }
    planner_records = planner_records
        .checked_add(action_capacity)
        .and_then(|value| value.checked_add(top_reference_capacity))
        .ok_or_else(|| {
            if let Some(observation) = observation.as_deref_mut() {
                observation.observe_overflow();
            }
            MaterializationStop::Capacity
        })?;
    let planner_charge = checked_planner_records(planner_records).ok_or_else(|| {
        if let Some(observation) = observation.as_deref_mut() {
            observation.observe_overflow();
        }
        MaterializationStop::Capacity
    })?;
    let conservative = planner_charge
        .checked_add(conservative_tables)
        .and_then(|value| value.checked_add(retained_module_name_charge))
        .and_then(|value| {
            value.checked_add(
                u64::try_from(action_capacity)
                    .ok()?
                    .checked_mul(largest_module_name_charge)?,
            )
        })
        .ok_or_else(|| {
            if let Some(observation) = observation.as_deref_mut() {
                observation.observe_overflow();
            }
            MaterializationStop::Capacity
        })?;
    if !budget.fits(conservative, observation) {
        return Err(MaterializationStop::Capacity);
    }
    Ok(action_capacity)
}

impl<'a> PlannedImportLoader<'a> {
    fn new(
        imports: &'a [&'a dyn CertificateImportView],
        action_capacity: usize,
    ) -> std::result::Result<Self, MaterializationStop> {
        let mut sources = Vec::new();
        sources
            .try_reserve_exact(imports.len())
            .map_err(|_| MaterializationStop::Capacity)?;
        sources.extend_from_slice(imports);
        sources.sort_by(|left, right| {
            left.module()
                .cmp(right.module())
                .then_with(|| left.export_hash().cmp(&right.export_hash()))
                .then_with(|| left.certificate_hash().cmp(&right.certificate_hash()))
        });
        sources.dedup_by(|lhs, rhs| {
            lhs.module() == rhs.module()
                && lhs.export_hash() == rhs.export_hash()
                && lhs.certificate_hash() == rhs.certificate_hash()
        });

        let mut modules = Vec::new();
        modules
            .try_reserve_exact(sources.len())
            .map_err(|_| MaterializationStop::Capacity)?;
        for source in sources {
            let declaration_count = source.declarations().len();
            let root_capacity = imported_module_root_capacity(source)
                .ok_or(MaterializationStop::SpeculativeInvariant)?;
            let mut declaration_state = Vec::new();
            declaration_state
                .try_reserve_exact(declaration_count)
                .map_err(|_| MaterializationStop::Capacity)?;
            declaration_state.resize(declaration_count, 0_u8);
            let mut roots = Vec::new();
            roots
                .try_reserve_exact(root_capacity)
                .map_err(|_| MaterializationStop::Capacity)?;
            modules.push(PlannedImportedModule {
                identity: try_exact_imported_module_identity(source)?,
                source,
                declaration_state,
                roots,
                table_plan: None,
            });
        }
        let mut actions = Vec::new();
        actions
            .try_reserve_exact(action_capacity)
            .map_err(|_| MaterializationStop::Capacity)?;
        Ok(Self {
            imports,
            modules,
            actions,
            action_capacity,
        })
    }

    fn module_slot(
        &self,
        source: &dyn CertificateImportView,
    ) -> std::result::Result<usize, MaterializationStop> {
        self.modules
            .iter()
            .position(|module| {
                module.identity.module == *source.module()
                    && module.identity.export_hash == source.export_hash()
                    && module.identity.certificate_hash == source.certificate_hash()
            })
            .ok_or(MaterializationStop::SpeculativeInvariant)
    }

    fn append_action(
        &mut self,
        action: ImportedLoadAction,
    ) -> std::result::Result<(), MaterializationStop> {
        if self.actions.len() == self.actions.capacity() {
            return Err(MaterializationStop::Capacity);
        }
        self.actions.push(action);
        Ok(())
    }

    fn plan_top_level(
        &mut self,
        declarations: &[DeclCert],
        name_table: &[Name],
    ) -> std::result::Result<(), MaterializationStop> {
        let reference_capacity = declarations
            .iter()
            .try_fold(0_usize, |total, decl| {
                total.checked_add(decl.dependencies.len())
            })
            .ok_or(MaterializationStop::Capacity)?;
        let mut refs = Vec::new();
        refs.try_reserve_exact(reference_capacity)
            .map_err(|_| MaterializationStop::Capacity)?;
        for decl in declarations {
            refs.extend(
                decl.dependencies
                    .iter()
                    .map(|dependency| dependency.global_ref().clone()),
            );
        }
        refs.sort();
        refs.dedup();
        for global_ref in refs {
            match global_ref {
                GlobalRef::Builtin {
                    name,
                    decl_interface_hash,
                } => self.append_action(ImportedLoadAction::Builtin {
                    owner: ImportedBuiltinOwner::Current,
                    name,
                    decl_interface_hash,
                })?,
                GlobalRef::Imported { import_index, .. } => {
                    let source = self
                        .imports
                        .get(import_index)
                        .copied()
                        .ok_or(MaterializationStop::SpeculativeInvariant)?;
                    let entry =
                        imported_export_entry_for_global_ref(name_table, self.imports, &global_ref)
                            .map_err(|_| MaterializationStop::SpeculativeInvariant)?;
                    self.plan_module_export_entry(source, entry)?;
                }
                GlobalRef::Local { .. } | GlobalRef::LocalGenerated { .. } => {}
            }
        }
        Ok(())
    }

    fn plan_selected_exports(
        &mut self,
        exports: &[&(usize, Name, Hash)],
    ) -> std::result::Result<(), MaterializationStop> {
        for export in exports {
            let (import_index, name, decl_interface_hash) = *export;
            let source = self
                .imports
                .get(*import_index)
                .copied()
                .ok_or(MaterializationStop::SpeculativeInvariant)?;
            let entry = imported_export_entry_by_name(source, name, *decl_interface_hash)
                .map_err(|_| MaterializationStop::SpeculativeInvariant)?;
            self.plan_module_export_entry(source, entry)?;
        }
        Ok(())
    }

    fn plan_imported_global_ref(
        &mut self,
        owner: &'a dyn CertificateImportView,
        global_ref: &GlobalRef,
    ) -> std::result::Result<(), MaterializationStop> {
        let GlobalRef::Imported {
            import_index,
            name,
            decl_interface_hash,
        } = global_ref
        else {
            return Err(MaterializationStop::SpeculativeInvariant);
        };
        let import_entry = owner
            .imports()
            .get(*import_index)
            .ok_or(MaterializationStop::SpeculativeInvariant)?;
        let source = find_import_view(self.imports, import_entry, TrustMode::Normal)
            .map_err(|_| MaterializationStop::SpeculativeInvariant)?;
        let wanted_name = owner
            .name_table()
            .get(*name)
            .ok_or(MaterializationStop::SpeculativeInvariant)?;
        let entry = imported_export_entry_by_name(source, wanted_name, *decl_interface_hash)
            .map_err(|_| MaterializationStop::SpeculativeInvariant)?;
        self.plan_module_export_entry(source, entry)
    }

    fn plan_module_export_entry(
        &mut self,
        source: &'a dyn CertificateImportView,
        entry: &ExportEntry,
    ) -> std::result::Result<(), MaterializationStop> {
        let module_slot = self.module_slot(source)?;
        let decl_index = source_decl_index_for_export_entry(source, entry)
            .map_err(|_| MaterializationStop::SpeculativeInvariant)?;
        let state = *self
            .modules
            .get(module_slot)
            .and_then(|module| module.declaration_state.get(decl_index))
            .ok_or(MaterializationStop::SpeculativeInvariant)?;
        match state {
            2 => return Ok(()),
            1 => return Err(MaterializationStop::SpeculativeInvariant),
            0 => {}
            _ => return Err(MaterializationStop::SpeculativeInvariant),
        }
        self.modules[module_slot].declaration_state[decl_index] = 1;

        let refs = collect_imported_kernel_refs_for_export_planned(source, entry)?;
        for global_ref in refs {
            match global_ref {
                GlobalRef::Builtin {
                    name,
                    decl_interface_hash,
                } => {
                    let identity = try_clone_exact_imported_module_identity(
                        &self.modules[module_slot].identity,
                    )?;
                    self.append_action(ImportedLoadAction::Builtin {
                        owner: ImportedBuiltinOwner::Imported {
                            module_slot,
                            identity,
                        },
                        name,
                        decl_interface_hash,
                    })?;
                }
                GlobalRef::Imported { .. } => {
                    self.plan_imported_global_ref(source, &global_ref)?;
                }
                GlobalRef::Local { decl_index } => {
                    let local_entry = export_entry_for_local_decl(source, decl_index)
                        .map_err(|_| MaterializationStop::SpeculativeInvariant)?;
                    self.plan_module_export_entry(source, local_entry)?;
                }
                GlobalRef::LocalGenerated {
                    decl_index, name, ..
                } => {
                    let local_entry =
                        export_entry_for_local_generated_decl(source, decl_index, name)
                            .map_err(|_| MaterializationStop::SpeculativeInvariant)?;
                    self.plan_module_export_entry(source, local_entry)?;
                }
            }
        }

        let export_index = source
            .export_block()
            .iter()
            .position(|candidate| std::ptr::eq(candidate, entry))
            .ok_or(MaterializationStop::SpeculativeInvariant)?;
        if source_decl_index_for_export_entry(source, &source.export_block()[export_index])
            .map_err(|_| MaterializationStop::SpeculativeInvariant)?
            != decl_index
        {
            return Err(MaterializationStop::SpeculativeInvariant);
        }
        let module_roots = &mut self.modules[module_slot].roots;
        append_export_entry_roots_planned(source, entry, module_roots)?;
        let key = ImportedDeclKey {
            module: try_clone_planner_name(source.module())?,
            certificate_hash: source.certificate_hash(),
            decl_index,
        };
        self.append_action(ImportedLoadAction::Declaration {
            key,
            export: ExportEntryIdentity {
                module_slot,
                export_index,
                source_decl_index: decl_index,
            },
        })?;
        self.modules[module_slot].declaration_state[decl_index] = 2;
        Ok(())
    }

    fn retained_planner_charge(&self) -> Option<u64> {
        // Module records, conversion-table slots, the admission token, and all
        // requested capacities kept alive through authoritative replay.
        let mut record_count = 1_usize
            .checked_add(self.modules.len())?
            .checked_add(self.modules.len())?
            .checked_add(self.action_capacity)?;
        for module in &self.modules {
            record_count = record_count
                .checked_add(module.declaration_state.len())?
                .checked_add(imported_module_root_capacity(module.source)?)?;
        }
        let mut total = checked_planner_records(record_count)?;
        for module in &self.modules {
            total = total.checked_add(planner_name_charge(&module.identity.module)?)?;
        }
        for action in &self.actions {
            let name = match action {
                ImportedLoadAction::Builtin {
                    owner: ImportedBuiltinOwner::Imported { identity, .. },
                    ..
                } => Some(&identity.module),
                ImportedLoadAction::Declaration { key, .. } => Some(&key.module),
                ImportedLoadAction::Builtin {
                    owner: ImportedBuiltinOwner::Current,
                    ..
                } => None,
            };
            if let Some(name) = name {
                total = total.checked_add(planner_name_charge(name)?)?;
            }
        }
        Some(total)
    }

    fn plan_tables(
        &mut self,
        mut observation: Option<&mut CertificateTermMaterializationObservation>,
    ) -> std::result::Result<u64, MaterializationStop> {
        let Some(mut aggregate) = self.retained_planner_charge() else {
            if let Some(observation) = observation.as_deref_mut() {
                observation.observe_overflow();
            }
            return Err(MaterializationStop::Capacity);
        };
        for module in &mut self.modules {
            if module.roots.is_empty() {
                continue;
            }
            let plan = match KernelExprMaterialization::plan_selected_roots_unadmitted(
                module.source,
                &module.roots,
            ) {
                MaterializationAttempt::Ready(plan) => plan,
                MaterializationAttempt::Fallback(stop) => return Err(stop),
            };
            let Some(next) = aggregate.checked_add(plan.charge()) else {
                if let Some(observation) = observation.as_deref_mut() {
                    observation.observe_overflow();
                }
                return Err(MaterializationStop::Capacity);
            };
            aggregate = next;
            module.table_plan = Some(plan);
        }
        Ok(aggregate)
    }
}

fn add_referenced_imports_to_env_planned<'a>(
    env: &mut Env,
    root_declarations: &[DeclCert],
    root_name_table: &[Name],
    imports: &'a [&'a dyn CertificateImportView],
    budget: &mut TermMaterializationBudgetV1,
    mut observation: Option<&mut CertificateTermMaterializationObservation>,
) -> MaterializationAttempt<Result<()>> {
    let action_capacity = match imported_planner_preflight(
        root_declarations,
        imports,
        budget,
        observation.as_deref_mut(),
    ) {
        Ok(preflight) => preflight,
        Err(stop) => return MaterializationAttempt::Fallback(stop),
    };
    let mut loader = match PlannedImportLoader::new(imports, action_capacity) {
        Ok(loader) => loader,
        Err(stop) => return MaterializationAttempt::Fallback(stop),
    };
    if let Err(stop) = loader.plan_top_level(root_declarations, root_name_table) {
        return MaterializationAttempt::Fallback(stop);
    }
    materialize_and_replay_planned_imports(env, Some(root_name_table), loader, budget, observation)
}

fn materialize_and_replay_planned_imports<'a>(
    env: &mut Env,
    root_name_table: Option<&[Name]>,
    mut loader: PlannedImportLoader<'a>,
    budget: &mut TermMaterializationBudgetV1,
    mut observation: Option<&mut CertificateTermMaterializationObservation>,
) -> MaterializationAttempt<Result<()>> {
    let aggregate_charge = match loader.plan_tables(observation.as_deref_mut()) {
        Ok(charge) => charge,
        Err(stop) => return MaterializationAttempt::Fallback(stop),
    };
    let admission = match ImportedMaterializationAdmission::fit(
        budget,
        aggregate_charge,
        observation.as_deref_mut(),
    ) {
        MaterializationAttempt::Ready(admission) => admission,
        MaterializationAttempt::Fallback(stop) => return MaterializationAttempt::Fallback(stop),
    };

    let mut conversions = Vec::new();
    if conversions.try_reserve_exact(loader.modules.len()).is_err() {
        return MaterializationAttempt::Fallback(MaterializationStop::Capacity);
    }
    for module in &loader.modules {
        let conversion = if let Some(plan) = module.table_plan.as_ref() {
            let table = match KernelExprMaterialization::build_selected_roots_uncommitted(
                module.source,
                plan,
                &admission,
                observation.as_deref_mut(),
            ) {
                MaterializationAttempt::Ready(table) => table,
                MaterializationAttempt::Fallback(stop) => {
                    return MaterializationAttempt::Fallback(stop)
                }
            };
            Some(KernelTermConversion::Materialized(table))
        } else {
            None
        };
        conversions.push(conversion);
    }
    admission.commit(budget, observation.as_deref_mut());

    let result = (|| {
        for action in &loader.actions {
            match action {
                ImportedLoadAction::Builtin {
                    owner,
                    name,
                    decl_interface_hash,
                } => {
                    let name_table = match owner {
                        ImportedBuiltinOwner::Current => match root_name_table {
                            Some(name_table) => name_table,
                            None => return Err(CertError::DecodeError),
                        },
                        ImportedBuiltinOwner::Imported {
                            module_slot,
                            identity,
                        } => {
                            let module = loader
                                .modules
                                .get(*module_slot)
                                .ok_or(CertError::DecodeError)?;
                            if &module.identity != identity {
                                return Err(CertError::DecodeError);
                            }
                            module.source.name_table()
                        }
                    };
                    add_builtin_ref_to_env(env, name_table, *name, *decl_interface_hash)?;
                }
                ImportedLoadAction::Declaration { key, export } => {
                    let module = loader
                        .modules
                        .get(export.module_slot)
                        .ok_or(CertError::DecodeError)?;
                    if module.identity.module != key.module
                        || module.identity.certificate_hash != key.certificate_hash
                        || export.source_decl_index != key.decl_index
                    {
                        return Err(CertError::DecodeError);
                    }
                    let entry = module
                        .source
                        .export_block()
                        .get(export.export_index)
                        .ok_or(CertError::DecodeError)?;
                    if source_decl_index_for_export_entry(module.source, entry)?
                        != export.source_decl_index
                    {
                        return Err(CertError::DecodeError);
                    }
                    let terms = conversions
                        .get(export.module_slot)
                        .and_then(Option::as_ref)
                        .ok_or(CertError::DecodeError)?;
                    let decl = certificate_import_export_entry_to_kernel_decl_with_terms(
                        module.source,
                        entry,
                        terms,
                        observation.as_deref_mut(),
                    )?;
                    let decl_name = decl.name().to_owned();
                    let is_builtin_decl =
                        builtin_decl_interface_hash(&Name::from_dotted(&decl_name)).is_some();
                    if env.decl(&decl_name).is_none() || !is_builtin_decl {
                        add_decl_to_env(env, decl)?;
                    }
                }
            }
        }
        Ok(())
    })();
    MaterializationAttempt::Ready(result)
}

pub(crate) fn add_verified_module_referenced_imports_to_env(
    env: &mut Env,
    module: &VerifiedModule,
    imports: &[&VerifiedModule],
) -> Result<()> {
    let imports = imports
        .iter()
        .map(|import| *import as &dyn CertificateImportView)
        .collect::<Vec<_>>();
    add_certificate_import_referenced_imports_to_env(env, module, &imports)
}

#[cfg(test)]
pub(crate) fn add_verified_module_referenced_imports_to_env_observed_for_test(
    env: &mut Env,
    module: &VerifiedModule,
    imports: &[&VerifiedModule],
    observation: &mut CertificateTermMaterializationObservation,
) -> Result<()> {
    let mut budget = TermMaterializationBudgetV1::new();
    add_verified_module_referenced_imports_to_env_with_budget_for_test(
        env,
        module,
        imports,
        &mut budget,
        observation,
    )
}

#[cfg(test)]
pub(crate) fn add_verified_module_referenced_imports_to_env_with_budget_for_test(
    env: &mut Env,
    module: &VerifiedModule,
    imports: &[&VerifiedModule],
    budget: &mut TermMaterializationBudgetV1,
    observation: &mut CertificateTermMaterializationObservation,
) -> Result<()> {
    add_verified_module_referenced_imports_to_env_with_budget_and_optional_observation_for_test(
        env,
        module,
        imports,
        budget,
        Some(observation),
    )
}

#[cfg(test)]
pub(crate) fn add_verified_module_referenced_imports_to_env_with_budget_and_optional_observation_for_test(
    env: &mut Env,
    module: &VerifiedModule,
    imports: &[&VerifiedModule],
    budget: &mut TermMaterializationBudgetV1,
    mut observation: Option<&mut CertificateTermMaterializationObservation>,
) -> Result<()> {
    let imports = imports
        .iter()
        .map(|import| *import as &dyn CertificateImportView)
        .collect::<Vec<_>>();
    match add_referenced_imports_to_env_planned(
        env,
        module.declarations(),
        module.name_table(),
        &imports,
        budget,
        observation.as_deref_mut(),
    ) {
        MaterializationAttempt::Ready(result) => result,
        MaterializationAttempt::Fallback(stop) => {
            if let Some(observation) = observation {
                if stop == MaterializationStop::Capacity {
                    observation.observe_capacity_stop();
                }
                observation.observe_legacy_fallback();
            }
            add_certificate_import_referenced_imports_to_env_legacy(env, module, &imports)
        }
    }
}

#[cfg(test)]
pub(crate) fn imported_materialization_action_order_with_budget_for_test(
    env: &mut Env,
    root: &dyn CertificateImportView,
    imports: &[&dyn CertificateImportView],
    budget: &mut TermMaterializationBudgetV1,
    mut observation: Option<&mut CertificateTermMaterializationObservation>,
) -> Result<()> {
    match add_referenced_imports_to_env_planned(
        env,
        root.declarations(),
        root.name_table(),
        imports,
        budget,
        observation.as_deref_mut(),
    ) {
        MaterializationAttempt::Ready(result) => result,
        MaterializationAttempt::Fallback(stop) => {
            if let Some(observation) = observation {
                if stop == MaterializationStop::Capacity {
                    observation.observe_capacity_stop();
                }
                observation.observe_legacy_fallback();
            }
            add_root_referenced_imports_to_env_legacy_for_test(env, root, imports)
        }
    }
}

#[cfg(test)]
pub(crate) fn add_root_referenced_imports_to_env_legacy_for_test(
    env: &mut Env,
    root: &dyn CertificateImportView,
    imports: &[&dyn CertificateImportView],
) -> Result<()> {
    add_certificate_import_referenced_imports_to_env_legacy(env, root, imports)
}

fn add_certificate_import_referenced_imports_to_env(
    env: &mut Env,
    module: &dyn CertificateImportView,
    imports: &[&dyn CertificateImportView],
) -> Result<()> {
    let mut budget = TermMaterializationBudgetV1::new();
    match add_referenced_imports_to_env_planned(
        env,
        module.declarations(),
        module.name_table(),
        imports,
        &mut budget,
        None,
    ) {
        MaterializationAttempt::Ready(result) => result,
        MaterializationAttempt::Fallback(_) => {
            add_certificate_import_referenced_imports_to_env_legacy(env, module, imports)
        }
    }
}

fn add_certificate_import_referenced_imports_to_env_legacy(
    env: &mut Env,
    module: &dyn CertificateImportView,
    imports: &[&dyn CertificateImportView],
) -> Result<()> {
    let mut loader = ReferencedImportLoader {
        imports,
        loaded: BTreeSet::new(),
        loading: BTreeSet::new(),
    };
    let mut refs = BTreeSet::new();
    for decl in module.declarations() {
        for dependency in &decl.dependencies {
            refs.insert(dependency.global_ref().clone());
        }
    }
    for global_ref in refs {
        match global_ref {
            GlobalRef::Builtin {
                name,
                decl_interface_hash,
            } => add_builtin_ref_to_env(env, module.name_table(), name, decl_interface_hash)?,
            GlobalRef::Imported { .. } => {
                loader.load_imported_global_ref_from_module(env, module, &global_ref)?;
            }
            GlobalRef::Local { .. } | GlobalRef::LocalGenerated { .. } => {}
        }
    }
    Ok(())
}

pub(crate) fn add_selected_import_exports_to_env(
    env: &mut Env,
    imports: &[&dyn CertificateImportView],
    exports: &[(usize, Name, Hash)],
) -> Result<()> {
    let mut budget = TermMaterializationBudgetV1::new();
    let attempt =
        add_selected_import_exports_to_env_planned(env, imports, exports, &mut budget, None);
    match attempt {
        MaterializationAttempt::Ready(result) => result,
        MaterializationAttempt::Fallback(_) => {
            add_selected_import_exports_to_env_legacy(env, imports, exports)
        }
    }
}

#[cfg(test)]
pub(crate) fn add_selected_import_exports_to_env_observed_for_test(
    env: &mut Env,
    imports: &[&dyn CertificateImportView],
    exports: &[(usize, Name, Hash)],
    observation: &mut CertificateTermMaterializationObservation,
) -> Result<()> {
    let mut budget = TermMaterializationBudgetV1::new();
    add_selected_import_exports_to_env_with_budget_for_test(
        env,
        imports,
        exports,
        &mut budget,
        observation,
    )
}

#[cfg(test)]
pub(crate) fn add_selected_import_exports_to_env_with_budget_for_test(
    env: &mut Env,
    imports: &[&dyn CertificateImportView],
    exports: &[(usize, Name, Hash)],
    budget: &mut TermMaterializationBudgetV1,
    observation: &mut CertificateTermMaterializationObservation,
) -> Result<()> {
    match add_selected_import_exports_to_env_planned(
        env,
        imports,
        exports,
        budget,
        Some(observation),
    ) {
        MaterializationAttempt::Ready(result) => result,
        MaterializationAttempt::Fallback(stop) => {
            if stop == MaterializationStop::Capacity {
                observation.observe_capacity_stop();
            }
            observation.observe_legacy_fallback();
            add_selected_import_exports_to_env_legacy(env, imports, exports)
        }
    }
}

fn add_selected_import_exports_to_env_planned<'a>(
    env: &mut Env,
    imports: &'a [&'a dyn CertificateImportView],
    exports: &[(usize, Name, Hash)],
    budget: &mut TermMaterializationBudgetV1,
    mut observation: Option<&mut CertificateTermMaterializationObservation>,
) -> MaterializationAttempt<Result<()>> {
    // Fit the complete conservative planner capacity before allocating even
    // the top-level selection scratch. Charging the raw request count is safe
    // for duplicates and lets the scratch retain references instead of
    // infallibly cloning the owned `Name` payloads.
    let action_capacity = match imported_planner_preflight_for_reference_capacity(
        exports.len(),
        imports,
        budget,
        observation.as_deref_mut(),
    ) {
        Ok(capacity) => capacity,
        Err(stop) => return MaterializationAttempt::Fallback(stop),
    };
    let mut selected = Vec::new();
    if selected.try_reserve_exact(exports.len()).is_err() {
        return MaterializationAttempt::Fallback(MaterializationStop::Capacity);
    }
    selected.extend(exports.iter());
    selected.sort_unstable();
    selected.dedup();
    let mut loader = match PlannedImportLoader::new(imports, action_capacity) {
        Ok(loader) => loader,
        Err(stop) => return MaterializationAttempt::Fallback(stop),
    };
    if let Err(stop) = loader.plan_selected_exports(&selected) {
        return MaterializationAttempt::Fallback(stop);
    }
    materialize_and_replay_planned_imports(env, None, loader, budget, observation)
}

fn add_selected_import_exports_to_env_legacy(
    env: &mut Env,
    imports: &[&dyn CertificateImportView],
    exports: &[(usize, Name, Hash)],
) -> Result<()> {
    let mut loader = ReferencedImportLoader {
        imports,
        loaded: BTreeSet::new(),
        loading: BTreeSet::new(),
    };
    let mut exports = exports.to_vec();
    exports.sort();
    exports.dedup();
    for (import_index, name, decl_interface_hash) in exports {
        let module = imports
            .get(import_index)
            .copied()
            .ok_or(CertError::DecodeError)?;
        let entry = imported_export_entry_by_name(module, &name, decl_interface_hash)?;
        loader.load_module_export_entry(env, module, entry)?;
    }
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ImportedDeclKey {
    module: Name,
    certificate_hash: Hash,
    decl_index: usize,
}

struct ReferencedImportLoader<'a> {
    imports: &'a [&'a dyn CertificateImportView],
    loaded: BTreeSet<ImportedDeclKey>,
    loading: BTreeSet<ImportedDeclKey>,
}

impl<'a> ReferencedImportLoader<'a> {
    fn load_imported_global_ref_from_cert(
        &mut self,
        env: &mut Env,
        cert: &ModuleCert,
        global_ref: &GlobalRef,
    ) -> Result<()> {
        let GlobalRef::Imported { import_index, .. } = global_ref else {
            return Err(CertError::DecodeError);
        };
        let module = self
            .imports
            .get(*import_index)
            .copied()
            .ok_or(CertError::DecodeError)?;
        let entry =
            imported_export_entry_for_global_ref(cert.name_table(), self.imports, global_ref)?;
        self.load_module_export_entry(env, module, entry)
    }

    fn load_imported_global_ref_from_module(
        &mut self,
        env: &mut Env,
        module: &'a dyn CertificateImportView,
        global_ref: &GlobalRef,
    ) -> Result<()> {
        let GlobalRef::Imported {
            import_index,
            name,
            decl_interface_hash,
        } = global_ref
        else {
            return Err(CertError::DecodeError);
        };
        let import_entry = module
            .imports()
            .get(*import_index)
            .ok_or(CertError::DecodeError)?;
        let imported = self.find_available_import(import_entry)?;
        let wanted_name = module
            .name_table()
            .get(*name)
            .ok_or(CertError::DecodeError)?;
        let entry = imported_export_entry_by_name(imported, wanted_name, *decl_interface_hash)?;
        self.load_module_export_entry(env, imported, entry)
    }

    fn load_module_export_entry(
        &mut self,
        env: &mut Env,
        module: &'a dyn CertificateImportView,
        entry: &ExportEntry,
    ) -> Result<()> {
        let decl_index = source_decl_index_for_export_entry(module, entry)?;
        self.load_module_decl_for_export(env, module, decl_index, entry)
    }

    fn load_module_decl_for_export(
        &mut self,
        env: &mut Env,
        module: &'a dyn CertificateImportView,
        decl_index: usize,
        entry: &ExportEntry,
    ) -> Result<()> {
        let key = ImportedDeclKey {
            module: module.module().clone(),
            certificate_hash: module.certificate_hash(),
            decl_index,
        };
        if self.loaded.contains(&key) {
            return Ok(());
        }
        if !self.loading.insert(key.clone()) {
            return Err(CertError::DependencyCycle {
                name: module
                    .name_table()
                    .get(entry.name)
                    .cloned()
                    .ok_or(CertError::DecodeError)?,
            });
        }

        let mut refs = BTreeSet::new();
        collect_imported_kernel_refs_for_export(module, entry, &mut refs)?;
        for global_ref in refs {
            match global_ref {
                GlobalRef::Builtin {
                    name,
                    decl_interface_hash,
                } => add_builtin_ref_to_env(env, module.name_table(), name, decl_interface_hash)?,
                GlobalRef::Imported { .. } => {
                    self.load_imported_global_ref_from_module(env, module, &global_ref)?;
                }
                GlobalRef::Local { decl_index } => {
                    let local_entry = export_entry_for_local_decl(module, decl_index)?;
                    self.load_module_export_entry(env, module, local_entry)?;
                }
                GlobalRef::LocalGenerated {
                    decl_index, name, ..
                } => {
                    let local_entry =
                        export_entry_for_local_generated_decl(module, decl_index, name)?;
                    self.load_module_export_entry(env, module, local_entry)?;
                }
            }
        }

        let decl = certificate_import_export_entry_to_kernel_decl(module, entry)?;
        let decl_name = decl.name().to_owned();
        let is_builtin_decl = builtin_decl_interface_hash(&Name::from_dotted(&decl_name)).is_some();
        if env.decl(&decl_name).is_none() || !is_builtin_decl {
            add_decl_to_env(env, decl)?;
        }
        self.loading.remove(&key);
        self.loaded.insert(key);
        Ok(())
    }

    fn find_available_import(&self, entry: &ImportEntry) -> Result<&'a dyn CertificateImportView> {
        find_import_view(self.imports, entry, TrustMode::Normal)
    }
}

fn add_builtin_ref_to_env(
    env: &mut Env,
    name_table: &[Name],
    name: NameId,
    decl_interface_hash: Hash,
) -> Result<()> {
    let name_value = name_table.get(name).ok_or(CertError::DecodeError)?;
    if builtin_decl_interface_hash(name_value) != Some(decl_interface_hash) {
        return Err(CertError::UnknownDependency {
            name: name_value.clone(),
        });
    }
    add_referenced_builtins_to_env(env, &BTreeSet::from([name_value.clone()]))
}

fn imported_export_entry_by_name<'a>(
    module: &'a dyn CertificateImportView,
    name: &Name,
    decl_interface_hash: Hash,
) -> Result<&'a ExportEntry> {
    module
        .export_block()
        .iter()
        .find(|entry| {
            entry.decl_interface_hash == decl_interface_hash
                && module
                    .name_table()
                    .get(entry.name)
                    .is_some_and(|candidate| candidate == name)
        })
        .ok_or_else(|| CertError::ImportHashMismatch {
            module: module.module().clone(),
        })
}

fn export_entry_for_local_decl(
    module: &dyn CertificateImportView,
    decl_index: usize,
) -> Result<&ExportEntry> {
    let decl = module
        .declarations()
        .get(decl_index)
        .ok_or(CertError::DecodeError)?;
    let name = decl_primary_name(&decl.decl);
    module
        .export_block()
        .iter()
        .find(|entry| {
            entry.name == name && entry.decl_interface_hash == decl.hashes.decl_interface_hash
        })
        .ok_or(CertError::DecodeError)
}

fn export_entry_for_local_generated_decl(
    module: &dyn CertificateImportView,
    decl_index: usize,
    name: NameId,
) -> Result<&ExportEntry> {
    let decl = module
        .declarations()
        .get(decl_index)
        .ok_or(CertError::DecodeError)?;
    module
        .export_block()
        .iter()
        .find(|entry| {
            entry.name == name && entry.decl_interface_hash == decl.hashes.decl_interface_hash
        })
        .ok_or(CertError::DecodeError)
}

fn decl_primary_name(decl: &DeclPayload) -> NameId {
    match decl {
        DeclPayload::Axiom { name, .. }
        | DeclPayload::AxiomConstrained { name, .. }
        | DeclPayload::Def { name, .. }
        | DeclPayload::DefConstrained { name, .. }
        | DeclPayload::Theorem { name, .. }
        | DeclPayload::TheoremConstrained { name, .. }
        | DeclPayload::Inductive { name, .. }
        | DeclPayload::InductiveConstrained { name, .. }
        | DeclPayload::MutualInductiveBlock { name, .. } => *name,
    }
}

fn collect_imported_kernel_refs_for_export(
    module: &dyn CertificateImportView,
    entry: &ExportEntry,
    refs: &mut BTreeSet<GlobalRef>,
) -> Result<()> {
    match entry.kind {
        ExportKind::Inductive | ExportKind::Constructor | ExportKind::Recursor => {
            let decl_index = source_decl_index_for_export_entry(module, entry)?;
            let decl = module
                .declarations()
                .get(decl_index)
                .ok_or(CertError::DecodeError)?;
            for term in decl_term_ids(&decl.decl) {
                collect_global_refs_from_verified_term(module, term, refs)?;
            }
            refs.retain(|global_ref| {
                !matches!(
                    global_ref,
                    GlobalRef::Local {
                        decl_index: local_decl_index
                    } | GlobalRef::LocalGenerated {
                        decl_index: local_decl_index,
                        ..
                    } if *local_decl_index == decl_index
                )
            });
        }
        ExportKind::Axiom | ExportKind::Theorem | ExportKind::Def => {
            collect_global_refs_from_verified_term(module, entry.ty, refs)?;
            if let Some(body) = entry.body {
                collect_global_refs_from_verified_term(module, body, refs)?;
            }
        }
    }
    Ok(())
}

fn collect_global_refs_from_verified_term(
    module: &dyn CertificateImportView,
    term: TermId,
    refs: &mut BTreeSet<GlobalRef>,
) -> Result<()> {
    collect_global_refs_from_term_table(module.term_table(), term, refs)
}

#[allow(dead_code)]
pub(crate) fn add_imports_to_env(env: &mut Env, imports: &[&VerifiedModule]) -> Result<()> {
    let imports = imports
        .iter()
        .map(|module| *module as &dyn CertificateImportView)
        .collect::<Vec<_>>();
    add_context_imports_to_env(env, &imports)
}

fn add_context_imports_to_env(env: &mut Env, imports: &[&dyn CertificateImportView]) -> Result<()> {
    let ordered = import_kernel_order(imports)?;
    let mut referenced_builtins = BTreeSet::new();
    for import in &ordered {
        referenced_builtins.extend(certificate_import_referenced_builtin_names(*import)?);
    }
    let imports_export_eq = verified_modules_export_builtin_eq(&ordered)?;
    let imports_export_eq_rec = verified_modules_export_builtin_eq_rec(&ordered)?;
    let mut loaded_imports = vec![false; ordered.len()];
    if imports_export_eq {
        for (index, import) in ordered.iter().enumerate() {
            if verified_module_exports_builtin_eq(*import)? {
                for decl in certificate_import_to_kernel_decls(*import)? {
                    add_decl_to_env(env, decl)?;
                }
                loaded_imports[index] = true;
            }
        }
    }
    let mut pre_import_builtins = referenced_builtins.clone();
    if imports_export_eq {
        pre_import_builtins
            .retain(|name| !matches!(name.as_dotted().as_str(), "Eq" | "Eq.refl" | "Eq.rec"));
    }
    add_referenced_builtins_to_env(env, &pre_import_builtins)?;
    let needs_builtin_eq_rec = referenced_builtins
        .iter()
        .any(|name| name.as_dotted() == "Eq.rec");
    if (imports_export_eq_rec || needs_builtin_eq_rec) && env.decl("Eq.rec").is_none() {
        let referenced = BTreeSet::from([Name::from_dotted("Eq"), Name::from_dotted("Eq.rec")]);
        add_referenced_builtins_to_env(env, &referenced)?;
    }
    for (index, import) in ordered.into_iter().enumerate() {
        if loaded_imports[index] {
            continue;
        }
        for decl in certificate_import_to_kernel_decls(import)? {
            add_decl_to_env(env, decl)?;
        }
    }
    Ok(())
}

fn verified_modules_export_builtin_eq(imports: &[&dyn CertificateImportView]) -> Result<bool> {
    for import in imports {
        if verified_module_exports_builtin_eq(*import)? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn verified_module_exports_builtin_eq(import: &dyn CertificateImportView) -> Result<bool> {
    for entry in import.export_block() {
        let Some(entry_name) = import.name_table().get(entry.name) else {
            return Err(CertError::DecodeError);
        };
        // `Eq` is globally named in the kernel environment. If an import provides it,
        // load that declaration before adding builtins that depend on it.
        if entry.kind == ExportKind::Inductive && entry_name.as_dotted() == "Eq" {
            return Ok(true);
        }
    }
    Ok(false)
}

fn verified_modules_export_builtin_eq_rec(imports: &[&dyn CertificateImportView]) -> Result<bool> {
    for import in imports {
        for entry in import.export_block() {
            if verified_module_export_uses_builtin_eq_rec(*import, entry)? {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

fn verified_module_export_uses_builtin_eq_rec(
    import: &dyn CertificateImportView,
    entry: &ExportEntry,
) -> Result<bool> {
    let Some(entry_name) = import.name_table().get(entry.name) else {
        return Err(CertError::DecodeError);
    };
    if entry_name.as_dotted() != "Eq.rec" {
        return Ok(false);
    }
    for candidate in import.export_block() {
        let Some(candidate_name) = import.name_table().get(candidate.name) else {
            return Err(CertError::DecodeError);
        };
        if candidate.kind == ExportKind::Inductive && candidate_name.as_dotted() == "Eq" {
            return Ok(true);
        }
    }
    Ok(false)
}

fn import_kernel_order<'a>(
    imports: &[&'a dyn CertificateImportView],
) -> Result<Vec<&'a dyn CertificateImportView>> {
    let mut added = vec![false; imports.len()];
    let mut order = Vec::with_capacity(imports.len());

    while order.len() < imports.len() {
        let mut progressed = false;
        for (index, import) in imports.iter().enumerate() {
            if added[index] || !import_dependencies_satisfied(*import, imports, &added)? {
                continue;
            }
            added[index] = true;
            order.push(*import);
            progressed = true;
        }

        if !progressed {
            let name = imports
                .iter()
                .enumerate()
                .find_map(|(index, import)| (!added[index]).then(|| import.module().clone()))
                .ok_or(CertError::DecodeError)?;
            return Err(CertError::DependencyCycle { name });
        }
    }

    Ok(order)
}

fn import_dependencies_satisfied(
    import: &dyn CertificateImportView,
    imports: &[&dyn CertificateImportView],
    added: &[bool],
) -> Result<bool> {
    for (dep_name, decl_interface_hash) in imported_dependency_targets(import)? {
        let mut found = false;
        let mut satisfied = false;
        for (index, candidate) in imports.iter().enumerate() {
            if module_exports_dependency(*candidate, &dep_name, decl_interface_hash)? {
                found = true;
                satisfied |= added[index];
            }
        }
        if !found {
            return Err(CertError::UnknownDependency { name: dep_name });
        }
        if !satisfied {
            return Ok(false);
        }
    }
    Ok(true)
}

fn imported_dependency_targets(
    module: &dyn CertificateImportView,
) -> Result<BTreeSet<(Name, Hash)>> {
    let mut deps = BTreeSet::new();
    for entry in module.export_block() {
        collect_imported_dependency_targets_from_term(module, entry.ty, &mut deps)?;
        if let Some(body) = entry.body {
            collect_imported_dependency_targets_from_term(module, body, &mut deps)?;
        }
    }
    Ok(deps)
}

fn collect_imported_dependency_targets_from_term(
    module: &dyn CertificateImportView,
    term: TermId,
    deps: &mut BTreeSet<(Name, Hash)>,
) -> Result<()> {
    visit_reachable_terms(module.term_table(), term, |node| {
        if let TermNode::Const {
            global_ref:
                GlobalRef::Imported {
                    name,
                    decl_interface_hash,
                    ..
                },
            ..
        } = node
        {
            let name = module
                .name_table()
                .get(*name)
                .ok_or(CertError::DecodeError)?
                .clone();
            deps.insert((name, *decl_interface_hash));
        }
        Ok(())
    })
}

fn module_exports_dependency(
    module: &dyn CertificateImportView,
    name: &Name,
    decl_interface_hash: Hash,
) -> Result<bool> {
    for entry in module.export_block() {
        let entry_name = module
            .name_table()
            .get(entry.name)
            .ok_or(CertError::DecodeError)?;
        if entry_name == name && entry.decl_interface_hash == decl_interface_hash {
            return Ok(true);
        }
    }
    Ok(false)
}

fn verify_dependencies_and_axioms(
    cert: &ModuleCert,
    imports: &[&dyn CertificateImportView],
) -> Result<()> {
    let mut previous_axioms: Vec<Vec<AxiomRef>> = Vec::new();
    let mut expected_reports = Vec::new();
    let version = certificate_format_version(cert.header())?;
    let mut local_transparency_budget = LocalTransparencyBudget::default();

    for (decl_index, decl) in cert.declarations().iter().enumerate() {
        let expected_deps = expected_dependencies_for_decl_with_budget(
            cert,
            imports,
            decl_index,
            &decl.decl,
            version,
            &mut local_transparency_budget,
        )?;
        if expected_deps != decl.dependencies {
            return Err(CertError::AxiomReportMismatch {
                decl: Some(decl_name_as_name(cert, decl_index)?),
            });
        }

        let (direct_axioms, transitive_axioms) = expected_axioms_for_decl(
            cert,
            imports,
            decl_index,
            &decl.decl,
            &expected_deps,
            &previous_axioms,
        )?;
        if transitive_axioms != decl.axiom_dependencies {
            return Err(CertError::AxiomReportMismatch {
                decl: Some(decl_name_as_name(cert, decl_index)?),
            });
        }

        let expected_report = DeclAxiomReport {
            decl_index,
            direct_axioms,
            transitive_axioms,
        };
        if cert.axiom_report().per_declaration.get(decl_index) != Some(&expected_report) {
            return Err(CertError::AxiomReportMismatch {
                decl: Some(decl_name_as_name(cert, decl_index)?),
            });
        }

        previous_axioms.push(expected_report.transitive_axioms.clone());
        expected_reports.push(expected_report);
    }

    if cert.axiom_report().per_declaration.len() != expected_reports.len() {
        return Err(CertError::AxiomReportMismatch { decl: None });
    }

    let expected_module_axioms = union_axioms(
        expected_reports
            .iter()
            .flat_map(|report| report.transitive_axioms.iter().cloned()),
    );
    if expected_module_axioms != cert.axiom_report().module_axioms {
        return Err(CertError::AxiomReportMismatch { decl: None });
    }
    let expected_features = core_features_from_builtins(&referenced_builtins_from_cert(cert)?);
    if expected_features != cert.axiom_report().core_features {
        return Err(CertError::AxiomReportMismatch { decl: None });
    }

    Ok(())
}

fn collect_current_module_term_roots(
    cert: &ModuleCert,
    observation: Option<&mut CertificateTermMaterializationObservation>,
) -> MaterializationAttempt<Vec<TermId>> {
    let generated_count =
        cert.declarations()
            .iter()
            .try_fold(0_usize, |total, decl| match &decl.decl {
                DeclPayload::Inductive {
                    params,
                    indices,
                    constructors,
                    recursor: Some(_),
                    ..
                }
                | DeclPayload::InductiveConstrained {
                    params,
                    indices,
                    constructors,
                    recursor: Some(_),
                    ..
                } => total
                    .checked_add(params.len())?
                    .checked_add(indices.len())?
                    .checked_add(constructors.len())?
                    .checked_add(1),
                DeclPayload::MutualInductiveBlock { inductives, .. } => {
                    let expected = inductives.iter().try_fold(0_usize, |count, inductive| {
                        count
                            .checked_add(inductive.params.len())?
                            .checked_add(inductive.indices.len())?
                            .checked_add(inductive.constructors.len())
                    })?;
                    let actual = inductives
                        .iter()
                        .filter(|inductive| inductive.recursor.is_some())
                        .count();
                    total.checked_add(expected)?.checked_add(actual)
                }
                _ => Some(total),
            });
    let declaration_count = cert.declarations().iter().try_fold(0_usize, |total, decl| {
        total.checked_add(decl_payload_term_root_count(&decl.decl)?)
    });
    let Some(capacity) = generated_count.and_then(|generated| {
        declaration_count.and_then(|declarations| generated.checked_add(declarations))
    }) else {
        if let Some(observation) = observation {
            observation.observe_overflow();
        }
        return MaterializationAttempt::Fallback(MaterializationStop::Capacity);
    };
    let mut roots = Vec::new();
    if roots.try_reserve_exact(capacity).is_err() {
        return MaterializationAttempt::Fallback(MaterializationStop::Capacity);
    }

    for decl in cert.declarations() {
        match &decl.decl {
            DeclPayload::Inductive {
                params,
                indices,
                constructors,
                recursor: Some(recursor),
                ..
            }
            | DeclPayload::InductiveConstrained {
                params,
                indices,
                constructors,
                recursor: Some(recursor),
                ..
            } => {
                roots.extend(params.iter().map(|binder| binder.ty));
                roots.extend(indices.iter().map(|binder| binder.ty));
                roots.extend(constructors.iter().map(|constructor| constructor.ty));
                roots.push(recursor.ty);
            }
            DeclPayload::MutualInductiveBlock { inductives, .. } => {
                for inductive in inductives {
                    roots.extend(inductive.params.iter().map(|binder| binder.ty));
                    roots.extend(inductive.indices.iter().map(|binder| binder.ty));
                    roots.extend(
                        inductive
                            .constructors
                            .iter()
                            .map(|constructor| constructor.ty),
                    );
                }
                roots.extend(
                    inductives
                        .iter()
                        .filter_map(|inductive| inductive.recursor.as_ref())
                        .map(|recursor| recursor.ty),
                );
            }
            _ => {}
        }
    }
    for decl in cert.declarations() {
        collect_decl_payload_term_roots(&decl.decl, &mut roots);
    }
    debug_assert_eq!(roots.len(), capacity);
    MaterializationAttempt::Ready(roots)
}

fn verify_inductive_generated_artifacts(
    cert: &ModuleCert,
    terms: &KernelTermConversion<'_, ModuleCert>,
    mut observation: Option<&mut CertificateTermMaterializationObservation>,
) -> Result<()> {
    for decl in cert.declarations() {
        let (name, universe_params, params, indices, sort, constructors, recursor) =
            match &decl.decl {
                DeclPayload::Inductive {
                    name,
                    universe_params,
                    params,
                    indices,
                    sort,
                    constructors,
                    recursor: Some(recursor),
                    ..
                }
                | DeclPayload::InductiveConstrained {
                    name,
                    universe_params,
                    params,
                    indices,
                    sort,
                    constructors,
                    recursor: Some(recursor),
                    ..
                } => (
                    *name,
                    universe_params.as_slice(),
                    params.as_slice(),
                    indices.as_slice(),
                    *sort,
                    constructors.as_slice(),
                    recursor,
                ),
                DeclPayload::MutualInductiveBlock {
                    name,
                    universe_params,
                    universe_constraints,
                    inductives,
                } => {
                    verify_mutual_inductive_generated_artifacts(
                        cert,
                        terms,
                        observation.as_deref_mut(),
                        *name,
                        universe_params,
                        universe_constraints,
                        inductives,
                    )?;
                    continue;
                }
                _ => continue,
            };

        let expected_rules = RecursorRulesSpec {
            minor_start: params.len() + 1,
            major_index: params.len() + 1 + constructors.len() + indices.len(),
        };
        if recursor.rules != expected_rules {
            return Err(CertError::InductiveGeneratedArtifactMismatch {
                name: cert
                    .name_table()
                    .get(name)
                    .ok_or(CertError::DecodeError)?
                    .clone(),
            });
        }

        let expected_type = expected_recursor_type_expr(
            cert,
            terms,
            observation.as_deref_mut(),
            InductiveRecursorView {
                name,
                universe_params,
                params,
                indices,
                sort,
                constructors,
                recursor,
            },
        )?;
        if terms.root_expr(recursor.ty, observation.as_deref_mut())? != expected_type {
            return Err(CertError::InductiveGeneratedArtifactMismatch {
                name: cert
                    .name_table()
                    .get(name)
                    .ok_or(CertError::DecodeError)?
                    .clone(),
            });
        }
    }
    Ok(())
}

fn verify_inductive_generated_artifacts_legacy(cert: &ModuleCert) -> Result<()> {
    let terms = KernelTermConversion::Legacy(cert);
    verify_inductive_generated_artifacts(cert, &terms, None)
}

fn verify_mutual_inductive_generated_artifacts(
    cert: &ModuleCert,
    terms: &KernelTermConversion<'_, ModuleCert>,
    mut observation: Option<&mut CertificateTermMaterializationObservation>,
    name: NameId,
    universe_params: &[NameId],
    universe_constraints: &[UniverseConstraintSpec],
    inductives: &[MutualInductiveSpec],
) -> Result<()> {
    let block_name = name_to_string(cert, name)?;
    let block_universe_params = universe_names(cert, universe_params)?;
    let mut expected_block = MutualInductiveBlock::new(
        block_name.clone(),
        block_universe_params.clone(),
        inductives
            .iter()
            .map(|inductive| {
                Ok(InductiveDecl::new(
                    name_to_string(cert, inductive.name)?,
                    block_universe_params.clone(),
                    inductive
                        .params
                        .iter()
                        .enumerate()
                        .map(|(index, binder)| {
                            Ok(Binder::new(
                                format!("p{index}"),
                                terms.root_expr(binder.ty, observation.as_deref_mut())?,
                            ))
                        })
                        .collect::<Result<Vec<_>>>()?,
                    inductive
                        .indices
                        .iter()
                        .enumerate()
                        .map(|(index, binder)| {
                            Ok(Binder::new(
                                format!("i{index}"),
                                terms.root_expr(binder.ty, observation.as_deref_mut())?,
                            ))
                        })
                        .collect::<Result<Vec<_>>>()?,
                    level_from_node(cert, inductive.sort)?,
                    inductive
                        .constructors
                        .iter()
                        .map(|constructor| {
                            Ok(ConstructorDecl::new(
                                name_to_string(cert, constructor.name)?,
                                terms.root_expr(constructor.ty, observation.as_deref_mut())?,
                            ))
                        })
                        .collect::<Result<Vec<_>>>()?,
                    None,
                ))
            })
            .collect::<Result<Vec<_>>>()?,
    );
    expected_block.universe_constraints = universe_constraints
        .iter()
        .map(|constraint| {
            Ok(npa_kernel::UniverseConstraint {
                lhs: level_from_node(cert, constraint.lhs)?,
                relation: constraint.relation,
                rhs: level_from_node(cert, constraint.rhs)?,
            })
        })
        .collect::<Result<Vec<_>>>()?;
    let expected_block = generate_mutual_inductive_artifacts_v1(&expected_block)?;

    for (actual, expected) in inductives.iter().zip(expected_block.inductives.iter()) {
        let actual_recursor = actual.recursor.as_ref().ok_or_else(|| {
            CertError::InductiveGeneratedArtifactMismatch {
                name: Name::from_dotted(&block_name),
            }
        })?;
        let expected_recursor = expected.recursor.as_ref().ok_or_else(|| {
            CertError::InductiveGeneratedArtifactMismatch {
                name: Name::from_dotted(&block_name),
            }
        })?;
        let expected_rules = expected_recursor.rules.as_ref().ok_or_else(|| {
            CertError::InductiveGeneratedArtifactMismatch {
                name: Name::from_dotted(&block_name),
            }
        })?;
        if name_to_string(cert, actual_recursor.name)? != expected_recursor.name
            || universe_names(cert, &actual_recursor.universe_params)?
                != expected_recursor.universe_params
            || actual_recursor.rules.minor_start != expected_rules.minor_start
            || actual_recursor.rules.major_index != expected_rules.major_index
            || terms.root_expr(actual_recursor.ty, observation.as_deref_mut())?
                != expected_recursor.ty
        {
            return Err(CertError::InductiveGeneratedArtifactMismatch {
                name: Name::from_dotted(&block_name),
            });
        }
    }
    if inductives.len() != expected_block.inductives.len() {
        return Err(CertError::InductiveGeneratedArtifactMismatch {
            name: Name::from_dotted(&block_name),
        });
    }
    Ok(())
}

struct InductiveRecursorView<'a> {
    name: NameId,
    universe_params: &'a [NameId],
    params: &'a [BinderType],
    indices: &'a [BinderType],
    sort: LevelId,
    constructors: &'a [ConstructorSpec],
    recursor: &'a RecursorSpec,
}

fn expected_recursor_type_expr(
    cert: &ModuleCert,
    terms: &KernelTermConversion<'_, ModuleCert>,
    mut observation: Option<&mut CertificateTermMaterializationObservation>,
    view: InductiveRecursorView<'_>,
) -> Result<Expr> {
    let inductive_name = name_to_string(cert, view.name)?;
    let inductive_universe_params = universe_names(cert, view.universe_params)?;
    let recursor_universe_params = universe_names(cert, &view.recursor.universe_params)?;
    let param_domains = view
        .params
        .iter()
        .map(|param| terms.root_expr(param.ty, observation.as_deref_mut()))
        .collect::<Result<Vec<_>>>()?;
    let index_domains = view
        .indices
        .iter()
        .map(|index| terms.root_expr(index.ty, observation.as_deref_mut()))
        .collect::<Result<Vec<_>>>()?;
    let motive_level = expected_motive_level(
        cert,
        view.sort,
        &inductive_universe_params,
        &recursor_universe_params,
    )?;

    let param_count = param_domains.len();
    let index_count = index_domains.len();
    let mut domains = param_domains;
    domains.push(motive_domain_expr(
        &inductive_name,
        &inductive_universe_params,
        param_count,
        &index_domains,
        motive_level,
    )?);

    for (constructor_index, constructor) in view.constructors.iter().enumerate() {
        domains.push(expected_minor_type_expr(
            cert,
            terms,
            observation.as_deref_mut(),
            &inductive_name,
            &inductive_universe_params,
            param_count,
            index_count,
            constructor,
            constructor_index,
        )?);
    }

    let index_start = domains.len();
    append_index_domains(param_count, &index_domains, &mut domains)?;
    let major_domain = inductive_target_expr(
        &inductive_name,
        &inductive_universe_params,
        domains.len(),
        param_count,
        index_start,
        index_count,
    )?;
    domains.push(major_domain);
    let index_args = (0..index_count)
        .map(|index| bvar_for_abs(domains.len(), index_start + index))
        .collect::<Result<Vec<_>>>()?;
    let body = motive_app(
        domains.len(),
        param_count,
        index_args,
        bvar_for_abs(domains.len(), view.recursor.rules.major_index)?,
    )?;
    Ok(mk_pi_from_domains(domains, body))
}

fn expected_motive_level(
    cert: &ModuleCert,
    sort: LevelId,
    inductive_universe_params: &[String],
    recursor_universe_params: &[String],
) -> Result<Level> {
    let inductive_sort = level_from_node(cert, sort)?;
    if level_eq(&inductive_sort, &Level::zero()) {
        return Ok(Level::zero());
    }
    if let Some(param) = recursor_universe_params
        .iter()
        .rev()
        .find(|param| !inductive_universe_params.contains(*param))
    {
        return Ok(Level::param(param.clone()));
    }
    Ok(recursor_universe_params
        .last()
        .map(|param| Level::param(param.clone()))
        .unwrap_or(inductive_sort))
}

fn inductive_target_expr(
    inductive_name: &str,
    universe_params: &[String],
    ctx_len: usize,
    param_count: usize,
    index_abs_start: usize,
    index_count: usize,
) -> Result<Expr> {
    let levels = universe_params
        .iter()
        .map(|param| Level::param(param.clone()))
        .collect();
    let args = (0..param_count)
        .map(|param_abs| bvar_for_abs(ctx_len, param_abs))
        .chain((0..index_count).map(|index| bvar_for_abs(ctx_len, index_abs_start + index)))
        .collect::<Result<Vec<_>>>()?;
    Ok(Expr::apps(
        Expr::konst(inductive_name.to_owned(), levels),
        args,
    ))
}

fn motive_domain_expr(
    inductive_name: &str,
    universe_params: &[String],
    param_count: usize,
    indices: &[Expr],
    motive_level: Level,
) -> Result<Expr> {
    let mut domains = Vec::new();
    let mut source_to_target = (0..param_count).collect::<Vec<_>>();
    for (index, ty) in indices.iter().enumerate() {
        let source_ctx_len = param_count + index;
        let target_ctx_len = param_count + index;
        domains.push(remap_bvars(
            ty,
            source_ctx_len,
            target_ctx_len,
            &source_to_target,
        )?);
        source_to_target.push(target_ctx_len);
    }
    let target = inductive_target_expr(
        inductive_name,
        universe_params,
        param_count + indices.len(),
        param_count,
        param_count,
        indices.len(),
    )?;
    let body = Expr::pi("_", target, Expr::sort(motive_level));
    Ok(mk_pi_from_domains(domains, body))
}

fn append_index_domains(
    param_count: usize,
    index_domains: &[Expr],
    domains: &mut Vec<Expr>,
) -> Result<()> {
    let mut source_to_target = (0..param_count).collect::<Vec<_>>();
    for (index, ty) in index_domains.iter().enumerate() {
        let source_ctx_len = param_count + index;
        let target_ctx_len = domains.len();
        domains.push(remap_bvars(
            ty,
            source_ctx_len,
            target_ctx_len,
            &source_to_target,
        )?);
        source_to_target.push(target_ctx_len);
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn expected_minor_type_expr(
    cert: &ModuleCert,
    terms: &KernelTermConversion<'_, ModuleCert>,
    observation: Option<&mut CertificateTermMaterializationObservation>,
    inductive_name: &str,
    universe_params: &[String],
    param_count: usize,
    index_count: usize,
    constructor: &ConstructorSpec,
    constructor_index: usize,
) -> Result<Expr> {
    let constructor_name = name_to_string(cert, constructor.name)?;
    let constructor_ty = terms.root_expr(constructor.ty, observation)?;
    let (constructor_domains, constructor_result) = peel_pi_domains(&constructor_ty);
    if constructor_domains.len() < param_count {
        return Err(CertError::InductiveGeneratedArtifactMismatch {
            name: Name::from_dotted(inductive_name),
        });
    }
    let constructor_result_indices = constructor_result_index_args(
        inductive_name,
        universe_params,
        param_count,
        index_count,
        &constructor_result,
    )?;

    let prefix_len = param_count + 1 + constructor_index;
    let motive_abs = param_count;
    let mut source_to_target: Vec<usize> = (0..param_count).collect();
    let mut target_ctx_len = prefix_len;
    let mut expected_domains = Vec::new();
    let mut field_abs = Vec::new();

    for (field_index, field_domain) in constructor_domains[param_count..].iter().enumerate() {
        let source_ctx_len = param_count + field_index;
        expected_domains.push(remap_bvars(
            field_domain,
            source_ctx_len,
            target_ctx_len,
            &source_to_target,
        )?);

        source_to_target.push(target_ctx_len);
        field_abs.push(target_ctx_len);
        target_ctx_len += 1;

        if is_direct_recursive_domain(
            inductive_name,
            universe_params,
            param_count,
            index_count,
            field_domain,
            source_ctx_len,
        )? {
            let index_args = direct_recursive_index_args(
                inductive_name,
                universe_params,
                param_count,
                index_count,
                field_domain,
                source_ctx_len,
            )?
            .into_iter()
            .map(|arg| remap_bvars(&arg, source_ctx_len, target_ctx_len, &source_to_target))
            .collect::<Result<Vec<_>>>()?;
            expected_domains.push(motive_app(
                target_ctx_len,
                motive_abs,
                index_args,
                Expr::bvar(0),
            )?);
            target_ctx_len += 1;
        }
    }

    let mut constructor_args = Vec::with_capacity(param_count + field_abs.len());
    for param_abs in 0..param_count {
        constructor_args.push(bvar_for_abs(target_ctx_len, param_abs)?);
    }
    for field_abs in field_abs {
        constructor_args.push(bvar_for_abs(target_ctx_len, field_abs)?);
    }

    let levels = universe_params
        .iter()
        .map(|param| Level::param(param.clone()))
        .collect();
    let constructor_value = Expr::apps(Expr::konst(constructor_name, levels), constructor_args);
    let result_index_args = constructor_result_indices
        .iter()
        .map(|arg| {
            remap_bvars(
                arg,
                constructor_domains.len(),
                target_ctx_len,
                &source_to_target,
            )
        })
        .collect::<Result<Vec<_>>>()?;
    let result = motive_app(
        target_ctx_len,
        motive_abs,
        result_index_args,
        constructor_value,
    )?;

    Ok(mk_pi_from_domains(expected_domains, result))
}

fn peel_pi_domains(ty: &Expr) -> (Vec<Expr>, Expr) {
    let mut domains = Vec::new();
    let mut current = ty;
    while let Expr::Pi { ty, body, .. } = current {
        domains.push((**ty).clone());
        current = body;
    }
    (domains, current.clone())
}

fn motive_app(
    ctx_len: usize,
    motive_abs: usize,
    index_args: Vec<Expr>,
    target: Expr,
) -> Result<Expr> {
    let mut args = index_args;
    args.push(target);
    Ok(Expr::apps(bvar_for_abs(ctx_len, motive_abs)?, args))
}

fn bvar_for_abs(ctx_len: usize, abs: usize) -> Result<Expr> {
    if abs >= ctx_len {
        return Err(CertError::InvalidBVar { index: abs as u32 });
    }
    Ok(Expr::bvar((ctx_len - 1 - abs) as u32))
}

fn mk_pi_from_domains(domains: Vec<Expr>, body: Expr) -> Expr {
    domains
        .into_iter()
        .rev()
        .fold(body, |body, domain| Expr::pi("_", domain, body))
}

fn remap_bvars(
    expr: &Expr,
    source_ctx_len: usize,
    target_ctx_len: usize,
    source_to_target: &[usize],
) -> Result<Expr> {
    enum Frame<'a> {
        Visit {
            expr: &'a Expr,
            source_ctx_len: usize,
            target_ctx_len: usize,
        },
        BuildApp,
        BuildLam(String),
        BuildPi(String),
    }

    let mut pending = vec![Frame::Visit {
        expr,
        source_ctx_len,
        target_ctx_len,
    }];
    let initial_source_ctx_len = source_ctx_len;
    let initial_map_len = source_to_target.len();
    let initial_target_ctx_len = target_ctx_len;
    let mut mapped = Vec::new();
    while let Some(frame) = pending.pop() {
        match frame {
            Frame::Visit {
                expr,
                source_ctx_len,
                target_ctx_len,
            } => match expr {
                Expr::Sort(level) => mapped.push(Expr::sort(level.clone())),
                Expr::BVar(index) => {
                    let index = *index as usize;
                    if index >= source_ctx_len {
                        return Err(CertError::InvalidBVar {
                            index: index as u32,
                        });
                    }
                    let source_abs = source_ctx_len - 1 - index;
                    let target_abs = if source_abs < initial_map_len {
                        source_to_target
                            .get(source_abs)
                            .copied()
                            .ok_or(CertError::InvalidBVar {
                                index: index as u32,
                            })?
                    } else {
                        let binder_offset = source_abs - initial_map_len;
                        let binder_depth = source_ctx_len
                            .checked_sub(initial_source_ctx_len)
                            .ok_or(CertError::InvalidBVar {
                                index: index as u32,
                            })?;
                        if binder_offset >= binder_depth {
                            return Err(CertError::InvalidBVar {
                                index: index as u32,
                            });
                        }
                        initial_target_ctx_len
                            .checked_add(binder_offset)
                            .ok_or(CertError::DecodeError)?
                    };
                    mapped.push(bvar_for_abs(target_ctx_len, target_abs)?);
                }
                Expr::Const { name, levels } => {
                    mapped.push(Expr::konst(name.clone(), levels.clone()));
                }
                Expr::App(fun, arg) => {
                    pending.push(Frame::BuildApp);
                    pending.push(Frame::Visit {
                        expr: arg,
                        source_ctx_len,
                        target_ctx_len,
                    });
                    pending.push(Frame::Visit {
                        expr: fun,
                        source_ctx_len,
                        target_ctx_len,
                    });
                }
                Expr::Lam { binder, ty, body } => {
                    pending.push(Frame::BuildLam(binder.clone()));
                    pending.push(Frame::Visit {
                        expr: body,
                        source_ctx_len: source_ctx_len + 1,
                        target_ctx_len: target_ctx_len + 1,
                    });
                    pending.push(Frame::Visit {
                        expr: ty,
                        source_ctx_len,
                        target_ctx_len,
                    });
                }
                Expr::Pi { binder, ty, body } => {
                    pending.push(Frame::BuildPi(binder.clone()));
                    pending.push(Frame::Visit {
                        expr: body,
                        source_ctx_len: source_ctx_len + 1,
                        target_ctx_len: target_ctx_len + 1,
                    });
                    pending.push(Frame::Visit {
                        expr: ty,
                        source_ctx_len,
                        target_ctx_len,
                    });
                }
            },
            Frame::BuildApp => {
                let arg = mapped.pop().ok_or(CertError::DecodeError)?;
                let fun = mapped.pop().ok_or(CertError::DecodeError)?;
                mapped.push(Expr::app(fun, arg));
            }
            Frame::BuildLam(binder) => {
                let body = mapped.pop().ok_or(CertError::DecodeError)?;
                let ty = mapped.pop().ok_or(CertError::DecodeError)?;
                mapped.push(Expr::lam(binder, ty, body));
            }
            Frame::BuildPi(binder) => {
                let body = mapped.pop().ok_or(CertError::DecodeError)?;
                let ty = mapped.pop().ok_or(CertError::DecodeError)?;
                mapped.push(Expr::pi(binder, ty, body));
            }
        }
    }
    let result = mapped.pop().ok_or(CertError::DecodeError)?;
    if mapped.is_empty() {
        Ok(result)
    } else {
        Err(CertError::DecodeError)
    }
}

fn is_direct_recursive_domain(
    inductive_name: &str,
    universe_params: &[String],
    param_count: usize,
    index_count: usize,
    domain: &Expr,
    ctx_len: usize,
) -> Result<bool> {
    Ok(direct_recursive_index_args(
        inductive_name,
        universe_params,
        param_count,
        index_count,
        domain,
        ctx_len,
    )
    .is_ok())
}

fn direct_recursive_index_args(
    inductive_name: &str,
    universe_params: &[String],
    param_count: usize,
    index_count: usize,
    domain: &Expr,
    ctx_len: usize,
) -> Result<Vec<Expr>> {
    let (head, args) = collect_apps(domain);
    let levels = match head {
        Expr::Const { name, levels } if name == inductive_name => levels,
        _ => {
            return Err(CertError::InductiveGeneratedArtifactMismatch {
                name: Name::from_dotted(inductive_name),
            });
        }
    };

    let expected_levels: Vec<_> = universe_params
        .iter()
        .map(|param| Level::param(param.clone()))
        .collect();
    if !levels_eq(&levels, &expected_levels) || args.len() != param_count + index_count {
        return Err(CertError::InductiveGeneratedArtifactMismatch {
            name: Name::from_dotted(inductive_name),
        });
    }

    for (param_index, arg) in args.iter().take(param_count).enumerate() {
        let expected = bvar_for_abs(ctx_len, param_index)?;
        if arg != &expected {
            return Err(CertError::InductiveGeneratedArtifactMismatch {
                name: Name::from_dotted(inductive_name),
            });
        }
    }

    if args.iter().all(|arg| !contains_const(arg, inductive_name)) {
        Ok(args[param_count..].to_vec())
    } else {
        Err(CertError::InductiveGeneratedArtifactMismatch {
            name: Name::from_dotted(inductive_name),
        })
    }
}

fn constructor_result_index_args(
    inductive_name: &str,
    universe_params: &[String],
    param_count: usize,
    index_count: usize,
    result: &Expr,
) -> Result<Vec<Expr>> {
    let (head, args) = collect_apps(result);
    let levels = match head {
        Expr::Const { name, levels } if name == inductive_name => levels,
        _ => {
            return Err(CertError::InductiveGeneratedArtifactMismatch {
                name: Name::from_dotted(inductive_name),
            });
        }
    };
    let expected_levels: Vec<_> = universe_params
        .iter()
        .map(|param| Level::param(param.clone()))
        .collect();
    if !levels_eq(&levels, &expected_levels) || args.len() != param_count + index_count {
        return Err(CertError::InductiveGeneratedArtifactMismatch {
            name: Name::from_dotted(inductive_name),
        });
    }
    Ok(args[param_count..].to_vec())
}

fn contains_const(expr: &Expr, needle: &str) -> bool {
    let mut pending = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            Expr::Sort(_) | Expr::BVar(_) => {}
            Expr::Const { name, .. } => {
                if name == needle {
                    return true;
                }
            }
            Expr::App(fun, arg) => {
                pending.push(arg);
                pending.push(fun);
            }
            Expr::Lam { ty, body, .. } | Expr::Pi { ty, body, .. } => {
                pending.push(body);
                pending.push(ty);
            }
        }
    }
    false
}

#[cfg(test)]
pub(crate) fn expected_dependencies_for_decl(
    cert: &ModuleCert,
    imports: &[&dyn CertificateImportView],
    decl_index: usize,
    decl: &DeclPayload,
) -> Result<Vec<DependencyEntry>> {
    let version = certificate_format_version(cert.header())?;
    expected_dependencies_for_decl_with_budget(
        cert,
        imports,
        decl_index,
        decl,
        version,
        &mut LocalTransparencyBudget::default(),
    )
}

fn expected_dependencies_for_decl_with_budget(
    cert: &ModuleCert,
    imports: &[&dyn CertificateImportView],
    decl_index: usize,
    decl: &DeclPayload,
    version: CertificateFormatVersion,
    budget: &mut LocalTransparencyBudget,
) -> Result<Vec<DependencyEntry>> {
    let actual_implementation_indices = validate_local_implementation_entries(
        decl_index,
        &cert
            .declarations()
            .get(decl_index)
            .ok_or(CertError::DecodeError)?
            .dependencies,
        cert.declarations(),
    )?;
    let closure = local_transparency_dependencies(
        version,
        decl_index,
        decl,
        cert.declarations(),
        cert.term_table(),
        budget,
    )?;
    validate_local_implementation_closure(
        decl_index,
        &actual_implementation_indices,
        &closure.opaque_definition_indices,
    )?;
    for dependency in &closure.interface_dependencies {
        let expected_hash =
            interface_hash_for_global_ref(cert, imports, decl_index, dependency.global_ref())?;
        if dependency.decl_interface_hash() != expected_hash {
            return Err(CertError::HashMismatch {
                object: HashObject::DeclInterface,
                expected: dependency.decl_interface_hash(),
                actual: expected_hash,
            });
        }
    }
    complete_local_transparency_dependencies(&closure, decl_index, cert.declarations())
}

pub(crate) fn expected_axioms_for_decl(
    cert: &ModuleCert,
    imports: &[&dyn CertificateImportView],
    decl_index: usize,
    decl: &DeclPayload,
    dependencies: &[DependencyEntry],
    previous_axioms: &[Vec<AxiomRef>],
) -> Result<(Vec<AxiomRef>, Vec<AxiomRef>)> {
    let mut direct = BTreeSet::new();
    let mut transitive = BTreeSet::new();
    for dependency in dependencies {
        match dependency.global_ref() {
            GlobalRef::Builtin {
                name,
                decl_interface_hash,
            } => {
                let name_value = cert.name_table().get(*name).ok_or(CertError::DecodeError)?;
                if builtin_is_axiom(name_value) {
                    let axiom = AxiomRef {
                        global_ref: dependency.global_ref().clone(),
                        name: *name,
                        decl_interface_hash: *decl_interface_hash,
                    };
                    direct.insert(axiom.clone());
                    transitive.insert(axiom);
                }
            }
            GlobalRef::Local { decl_index } => {
                if let Some(dep_axioms) = previous_axioms.get(*decl_index) {
                    if let Some(axiom) = local_axiom_ref_for_decl(*decl_index, dep_axioms) {
                        direct.insert(axiom);
                    }
                    transitive.extend(dep_axioms.iter().cloned());
                }
            }
            GlobalRef::LocalGenerated { decl_index, .. } => {
                if let Some(dep_axioms) = previous_axioms.get(*decl_index) {
                    transitive.extend(dep_axioms.iter().cloned());
                }
            }
            GlobalRef::Imported {
                import_index,
                name,
                decl_interface_hash,
            } => {
                let entry = imported_export_entry_for_global_ref(
                    cert.name_table(),
                    imports,
                    dependency.global_ref(),
                )?;
                if entry.kind == ExportKind::Axiom {
                    direct.insert(AxiomRef {
                        global_ref: dependency.global_ref().clone(),
                        name: *name,
                        decl_interface_hash: *decl_interface_hash,
                    });
                }
                let import = imports.get(*import_index).ok_or(CertError::DecodeError)?;
                for axiom in &entry.axiom_dependencies {
                    transitive.insert(remap_axiom_ref_from_cert_import(
                        cert, imports, *import, axiom,
                    )?);
                }
            }
        }
    }
    if let DeclPayload::Axiom { name, .. } | DeclPayload::AxiomConstrained { name, .. } = decl {
        let self_ref = AxiomRef {
            global_ref: GlobalRef::Local { decl_index },
            name: *name,
            decl_interface_hash: cert
                .declarations()
                .get(decl_index)
                .ok_or(CertError::DecodeError)?
                .hashes
                .decl_interface_hash,
        };
        direct.insert(self_ref.clone());
        transitive.insert(self_ref);
    }
    Ok((
        direct.into_iter().collect(),
        transitive.into_iter().collect(),
    ))
}

fn remap_axiom_ref_from_cert_import(
    cert: &ModuleCert,
    imports: &[&dyn CertificateImportView],
    import: &dyn CertificateImportView,
    axiom: &AxiomRef,
) -> Result<AxiomRef> {
    let axiom_name = import
        .name_table()
        .get(axiom.name)
        .ok_or(CertError::DecodeError)?;
    let name = cert
        .name_table()
        .iter()
        .position(|candidate| candidate == axiom_name)
        .ok_or(CertError::DecodeError)?;
    if let GlobalRef::Builtin {
        decl_interface_hash,
        ..
    } = &axiom.global_ref
    {
        if builtin_decl_interface_hash(axiom_name) != Some(*decl_interface_hash) {
            return Err(CertError::UnknownDependency {
                name: axiom_name.clone(),
            });
        }
        return Ok(AxiomRef {
            global_ref: GlobalRef::Builtin {
                name,
                decl_interface_hash: *decl_interface_hash,
            },
            name,
            decl_interface_hash: *decl_interface_hash,
        });
    }
    let import_index =
        import_index_exporting_axiom(imports, axiom_name, axiom.decl_interface_hash)?;
    Ok(AxiomRef {
        global_ref: GlobalRef::Imported {
            import_index,
            name,
            decl_interface_hash: axiom.decl_interface_hash,
        },
        name,
        decl_interface_hash: axiom.decl_interface_hash,
    })
}

fn import_index_exporting_axiom(
    imports: &[&dyn CertificateImportView],
    axiom_name: &Name,
    decl_interface_hash: Hash,
) -> Result<usize> {
    imports
        .iter()
        .enumerate()
        .find_map(|(import_index, import)| {
            import
                .export_block()
                .iter()
                .any(|entry| {
                    entry.kind == ExportKind::Axiom
                        && entry.decl_interface_hash == decl_interface_hash
                        && import
                            .name_table()
                            .get(entry.name)
                            .is_some_and(|name| name == axiom_name)
                })
                .then_some(import_index)
        })
        .ok_or_else(|| CertError::UnknownDependency {
            name: axiom_name.clone(),
        })
}

fn local_axiom_ref_for_decl(decl_index: usize, dep_axioms: &[AxiomRef]) -> Option<AxiomRef> {
    dep_axioms
        .iter()
        .find(|axiom| {
            matches!(
                axiom.global_ref,
                GlobalRef::Local { decl_index: axiom_index } if axiom_index == decl_index
            )
        })
        .cloned()
}

fn decl_term_ids(decl: &DeclPayload) -> Vec<TermId> {
    match decl {
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
            .map(|param| param.ty)
            .chain(indices.iter().map(|index| index.ty))
            .chain(constructors.iter().map(|constructor| constructor.ty))
            .chain(recursor.iter().map(|recursor| recursor.ty))
            .collect(),
        DeclPayload::MutualInductiveBlock { inductives, .. } => inductives
            .iter()
            .flat_map(|inductive| {
                inductive
                    .params
                    .iter()
                    .map(|param| param.ty)
                    .chain(inductive.indices.iter().map(|index| index.ty))
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

fn decl_universe_params(decl: &DeclPayload) -> &[NameId] {
    match decl {
        DeclPayload::Axiom {
            universe_params, ..
        }
        | DeclPayload::AxiomConstrained {
            universe_params, ..
        }
        | DeclPayload::Def {
            universe_params, ..
        }
        | DeclPayload::DefConstrained {
            universe_params, ..
        }
        | DeclPayload::Theorem {
            universe_params, ..
        }
        | DeclPayload::TheoremConstrained {
            universe_params, ..
        }
        | DeclPayload::Inductive {
            universe_params, ..
        }
        | DeclPayload::InductiveConstrained {
            universe_params, ..
        }
        | DeclPayload::MutualInductiveBlock {
            universe_params, ..
        } => universe_params,
    }
}

fn decl_universe_constraints(decl: &DeclPayload) -> &[UniverseConstraintSpec] {
    match decl {
        DeclPayload::AxiomConstrained {
            universe_constraints,
            ..
        }
        | DeclPayload::DefConstrained {
            universe_constraints,
            ..
        }
        | DeclPayload::TheoremConstrained {
            universe_constraints,
            ..
        }
        | DeclPayload::InductiveConstrained {
            universe_constraints,
            ..
        }
        | DeclPayload::MutualInductiveBlock {
            universe_constraints,
            ..
        } => universe_constraints,
        DeclPayload::Axiom { .. }
        | DeclPayload::Def { .. }
        | DeclPayload::Theorem { .. }
        | DeclPayload::Inductive { .. } => &[],
    }
}

fn collect_global_refs_from_term_table(
    term_table: &[TermNode],
    term: TermId,
    refs: &mut BTreeSet<GlobalRef>,
) -> Result<()> {
    visit_reachable_terms(term_table, term, |node| {
        if let TermNode::Const { global_ref, .. } = node {
            refs.insert(global_ref.clone());
        }
        Ok(())
    })
}

fn visit_reachable_terms(
    term_table: &[TermNode],
    root: TermId,
    mut visit: impl FnMut(&TermNode) -> Result<()>,
) -> Result<()> {
    if root >= term_table.len() {
        return Err(CertError::DecodeError);
    }

    let mut visited = BTreeSet::new();
    let mut pending = Vec::new();
    pending
        .try_reserve(term_table.len().min(1_024))
        .map_err(|_| CertError::DecodeError)?;
    pending.push(root);

    while let Some(term) = pending.pop() {
        if !visited.insert(term) {
            continue;
        }
        let node = term_table.get(term).ok_or(CertError::DecodeError)?;
        visit(node)?;
        let child_count = match node {
            TermNode::Sort(_) | TermNode::BVar(_) | TermNode::Const { .. } => 0,
            TermNode::App(_, _) | TermNode::Lam { .. } | TermNode::Pi { .. } => 2,
        };
        pending
            .try_reserve(child_count)
            .map_err(|_| CertError::DecodeError)?;
        match node {
            TermNode::Sort(_) | TermNode::BVar(_) | TermNode::Const { .. } => {}
            TermNode::App(fun, arg) => {
                pending.push(*arg);
                pending.push(*fun);
            }
            TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => {
                pending.push(*body);
                pending.push(*ty);
            }
        }
    }

    Ok(())
}

fn referenced_builtins_from_cert(cert: &ModuleCert) -> Result<BTreeSet<Name>> {
    let mut names = BTreeSet::new();
    for term in cert.term_table() {
        if let TermNode::Const {
            global_ref:
                GlobalRef::Builtin {
                    name,
                    decl_interface_hash,
                },
            ..
        } = term
        {
            let name_value = cert.name_table().get(*name).ok_or(CertError::DecodeError)?;
            if builtin_decl_interface_hash(name_value) != Some(*decl_interface_hash) {
                return Err(CertError::UnknownDependency {
                    name: name_value.clone(),
                });
            }
            names.insert(name_value.clone());
        }
    }
    Ok(names)
}

fn interface_hash_for_global_ref(
    cert: &ModuleCert,
    imports: &[&dyn CertificateImportView],
    current_decl_index: usize,
    global_ref: &GlobalRef,
) -> Result<Hash> {
    match global_ref {
        GlobalRef::Builtin {
            name,
            decl_interface_hash,
        } => {
            let name = cert.name_table().get(*name).ok_or(CertError::DecodeError)?;
            if builtin_decl_interface_hash(name) != Some(*decl_interface_hash) {
                return Err(CertError::UnknownDependency { name: name.clone() });
            }
            Ok(*decl_interface_hash)
        }
        GlobalRef::Local { decl_index } => {
            if *decl_index >= current_decl_index {
                return Err(CertError::DependencyCycle {
                    name: Name::from_dotted(format!("local.{decl_index}")),
                });
            }
            Ok(cert
                .declarations()
                .get(*decl_index)
                .ok_or(CertError::DecodeError)?
                .hashes
                .decl_interface_hash)
        }
        GlobalRef::LocalGenerated { decl_index, name } => {
            if *decl_index >= current_decl_index {
                return Err(CertError::DependencyCycle {
                    name: cert
                        .name_table()
                        .get(*name)
                        .cloned()
                        .unwrap_or_else(|| Name::from_dotted(format!("local.{decl_index}"))),
                });
            }
            if !local_generated_entry_exists(cert, *decl_index, *name)? {
                return Err(CertError::UnknownDependency {
                    name: cert
                        .name_table()
                        .get(*name)
                        .cloned()
                        .ok_or(CertError::DecodeError)?,
                });
            }
            Ok(cert
                .declarations()
                .get(*decl_index)
                .ok_or(CertError::DecodeError)?
                .hashes
                .decl_interface_hash)
        }
        GlobalRef::Imported {
            decl_interface_hash,
            ..
        } => {
            let entry =
                imported_export_entry_for_global_ref(cert.name_table(), imports, global_ref)?;
            if entry.decl_interface_hash != *decl_interface_hash {
                return Err(CertError::ImportHashMismatch {
                    module: imported_module_name_for_global_ref(imports, global_ref)?,
                });
            }
            Ok(*decl_interface_hash)
        }
    }
}

fn local_generated_entry_exists(
    cert: &ModuleCert,
    decl_index: usize,
    name: NameId,
) -> Result<bool> {
    let decl = cert
        .declarations()
        .get(decl_index)
        .ok_or(CertError::DecodeError)?;
    Ok(match &decl.decl {
        DeclPayload::Inductive {
            constructors,
            recursor,
            ..
        }
        | DeclPayload::InductiveConstrained {
            constructors,
            recursor,
            ..
        } => {
            constructors
                .iter()
                .any(|constructor| constructor.name == name)
                || recursor
                    .as_ref()
                    .is_some_and(|recursor| recursor.name == name)
        }
        DeclPayload::MutualInductiveBlock { inductives, .. } => {
            inductives.iter().any(|inductive| {
                inductive.name == name
                    || inductive
                        .constructors
                        .iter()
                        .any(|constructor| constructor.name == name)
                    || inductive
                        .recursor
                        .as_ref()
                        .is_some_and(|recursor| recursor.name == name)
            })
        }
        _ => false,
    })
}

fn imported_export_entry_for_global_ref<'a>(
    name_table: &[Name],
    imports: &'a [&'a dyn CertificateImportView],
    global_ref: &GlobalRef,
) -> Result<&'a ExportEntry> {
    let GlobalRef::Imported {
        import_index,
        name,
        decl_interface_hash,
    } = global_ref
    else {
        return Err(CertError::DecodeError);
    };
    let imported = imports.get(*import_index).ok_or(CertError::DecodeError)?;
    let wanted_name = name_table.get(*name).ok_or(CertError::DecodeError)?;
    imported
        .export_block()
        .iter()
        .find(|entry| {
            imported
                .name_table()
                .get(entry.name)
                .is_some_and(|candidate| candidate == wanted_name)
                && entry.decl_interface_hash == *decl_interface_hash
        })
        .ok_or_else(|| CertError::ImportHashMismatch {
            module: imported.module().clone(),
        })
}

fn imported_module_name_for_global_ref(
    imports: &[&dyn CertificateImportView],
    global_ref: &GlobalRef,
) -> Result<ModuleName> {
    let GlobalRef::Imported { import_index, .. } = global_ref else {
        return Err(CertError::DecodeError);
    };
    Ok(imports
        .get(*import_index)
        .ok_or(CertError::DecodeError)?
        .module()
        .clone())
}

fn decl_name_as_name(cert: &ModuleCert, decl_index: usize) -> Result<Name> {
    let decl = cert
        .declarations()
        .get(decl_index)
        .ok_or(CertError::DecodeError)?;
    let name = match &decl.decl {
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
    cert.name_table()
        .get(name)
        .cloned()
        .ok_or(CertError::DecodeError)
}

fn enforce_axiom_policy(cert: &ModuleCert, policy: &AxiomPolicy) -> Result<()> {
    enforce_axiom_policy_for_report(cert.name_table(), cert.axiom_report(), policy)
}

fn enforce_import_axiom_policy(
    imports: &[&dyn CertificateImportView],
    policy: &AxiomPolicy,
) -> Result<()> {
    for import in imports {
        enforce_core_feature_policy(import.axiom_report(), policy)?;
        enforce_axiom_policy_for_report(import.name_table(), import.axiom_report(), policy)?;
    }
    Ok(())
}

fn enforce_core_feature_policy(axiom_report: &AxiomReport, policy: &AxiomPolicy) -> Result<()> {
    for feature in &axiom_report.core_features {
        if !policy.supported_core_features.contains(feature) {
            return Err(CertError::UnsupportedCoreFeature {
                feature: feature.as_str().to_owned(),
            });
        }
    }
    Ok(())
}

fn enforce_axiom_policy_for_report(
    name_table: &[Name],
    axiom_report: &AxiomReport,
    policy: &AxiomPolicy,
) -> Result<()> {
    for axiom in &axiom_report.module_axioms {
        let name = name_table.get(axiom.name).ok_or(CertError::DecodeError)?;
        let dotted = name.as_dotted();
        if policy.deny_sorry && dotted.contains("sorry") {
            return Err(CertError::SorryDenied {
                axiom: name.clone(),
            });
        }
        let require_allowlist =
            policy.mode == TrustMode::HighTrust || !policy.allowlisted_axioms.is_empty();
        if require_allowlist && !policy.allowlisted_axioms.contains(name) {
            return Err(CertError::ForbiddenAxiom {
                axiom: name.clone(),
            });
        }
    }
    Ok(())
}

#[cfg(test)]
#[path = "../../npa-api/examples/support/closed_private_tree.rs"]
mod validation_reuse_closed_private_tree;

#[cfg(test)]
#[path = "../../npa-api/examples/support/runtime_source_set.rs"]
mod validation_reuse_runtime_source_set;

#[cfg(test)]
pub(crate) mod validation_reuse_benchmark_tests {
    use super::validation_reuse_closed_private_tree::{
        create_new_absolute_file, read_absolute_regular_file, AttachedExecutable,
        ClosedPrivateDirectory,
    };
    use super::validation_reuse_runtime_source_set::validate_runtime_source_set;
    use super::*;
    use npa_kernel::Decl;
    use sha2::{Digest, Sha256};
    use std::env;
    use std::fs;
    use std::io::Write;
    use std::path::{Path, PathBuf};
    use std::process::Command;
    use std::time::Instant;

    const CATALOG_SCHEMA: &str = "npa.certificate-validation-pass-reuse.scenarios.v0.1";
    const CHILD_SCHEMA: &str = "npa.certificate-validation-pass-reuse.child.v0.1";
    const RUN_SCHEMA: &str = "npa.certificate-validation-pass-reuse.run.v0.2";
    const TEST_NAME: &str =
        "verify::validation_reuse_benchmark_tests::validation_reuse_release_benchmark";
    const MAX_CVR_REPORT_BYTES: u64 = 64 * 1024 * 1024;
    const MAX_CVR_EXECUTABLE_BYTES: u64 = 512 * 1024 * 1024;
    const MAX_CARGO_LOCK_BYTES: u64 = 32 * 1024 * 1024;

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum ExpectedStage {
        Accepted,
        LevelReference,
        TermOrder,
        CertificateHash,
    }

    impl ExpectedStage {
        fn outcome(self) -> &'static str {
            match self {
                Self::Accepted => "accepted",
                Self::LevelReference | Self::TermOrder | Self::CertificateHash => "expected-error",
            }
        }

        fn json_stage(self) -> &'static str {
            match self {
                Self::Accepted => "null",
                Self::LevelReference => "\"level-reference\"",
                Self::TermOrder => "\"term-order\"",
                Self::CertificateHash => "\"certificate-hash\"",
            }
        }
    }

    #[derive(Clone, Copy)]
    struct Scenario {
        id: &'static str,
        expected: ExpectedStage,
        input_bytes: u64,
        input_sha256: &'static str,
    }

    const SCENARIOS: [Scenario; 9] = [
        Scenario {
            id: "cvr-valid-1k",
            expected: ExpectedStage::Accepted,
            input_bytes: 1_024,
            input_sha256: "37bb8c5ffab5a0bdc67f456dd07d82253b1c3ac2f57a774379f78d8e784d22f6",
        },
        Scenario {
            id: "cvr-valid-1m",
            expected: ExpectedStage::Accepted,
            input_bytes: 1_048_576,
            input_sha256: "aff973abaf0e008e655b513f2e786833e36f589623690a10b7b03ef9f271fe7f",
        },
        Scenario {
            id: "cvr-valid-near-byte-limit",
            expected: ExpectedStage::Accepted,
            input_bytes: 67_104_768,
            input_sha256: "2b4f562ae79f3106d20de189c0aca3eff3b1e7a99ad96b8a9973b77d0355580c",
        },
        Scenario {
            id: "cvr-valid-wide-levels",
            expected: ExpectedStage::Accepted,
            input_bytes: 338_229,
            input_sha256: "2715bdbf58954b2eb29aca112fc3f86659651eaec912f684dc7234f0163ebfb0",
        },
        Scenario {
            id: "cvr-valid-deep-term-dag",
            expected: ExpectedStage::Accepted,
            input_bytes: 33_159,
            input_sha256: "f87620b08d912f14bd4cc6798c430ea372311f0c5315f6ae127a9514945ace73",
        },
        Scenario {
            id: "cvr-valid-wide-term-dag",
            expected: ExpectedStage::Accepted,
            input_bytes: 25_229_633,
            input_sha256: "9b7eb68a02918cd884f6062f79c83553898822aeb26c390b704a0c912ce709d4",
        },
        Scenario {
            id: "cvr-malformed-early-level-reference",
            expected: ExpectedStage::LevelReference,
            input_bytes: 1_024,
            input_sha256: "01400e05578ab55bef0b2421fc134c841ae44c8a3e3aee80a66fb493a6154168",
        },
        Scenario {
            id: "cvr-malformed-middle-term-order",
            expected: ExpectedStage::TermOrder,
            input_bytes: 1_048_576,
            input_sha256: "0e695e2b8af02469ad9bd15f4fae46bd57430842ed5cf69ed5a972a61df8d6c1",
        },
        Scenario {
            id: "cvr-malformed-late-certificate-hash",
            expected: ExpectedStage::CertificateHash,
            input_bytes: 67_104_768,
            input_sha256: "76a0a53ea9024d548b363d956569bb2b12d99a21e16e25e4dff5bce361124bc4",
        },
    ];

    fn json_string(value: &str) -> String {
        let mut output = String::with_capacity(value.len() + 2);
        output.push('"');
        for character in value.chars() {
            match character {
                '"' => output.push_str("\\\""),
                '\\' => output.push_str("\\\\"),
                '\n' => output.push_str("\\n"),
                '\r' => output.push_str("\\r"),
                '\t' => output.push_str("\\t"),
                character if character.is_control() => {
                    use std::fmt::Write as _;
                    let _ = write!(output, "\\u{:04x}", character as u32);
                }
                character => output.push(character),
            }
        }
        output.push('"');
        output
    }

    fn sha256_hex(bytes: &[u8]) -> String {
        let digest = Sha256::digest(bytes);
        digest.iter().map(|byte| format!("{byte:02x}")).collect()
    }

    fn exact_size_module(short_suffix_len: usize, long_suffix_len: usize) -> CoreModule {
        let u = Level::succ(Level::zero());
        let id_ty = Expr::pi(
            "_",
            Expr::sort(u.clone()),
            Expr::pi("_", Expr::bvar(0), Expr::bvar(1)),
        );
        let id_value = Expr::lam(
            "_",
            Expr::sort(u),
            Expr::lam("_", Expr::bvar(0), Expr::bvar(0)),
        );
        CoreModule {
            name: Name::from_dotted("Bench.Cvr.ExactSize"),
            declarations: vec![
                Decl::Def {
                    name: format!("Bench.CvrPadA.P{}", "a".repeat(short_suffix_len)),
                    universe_params: Vec::new(),
                    ty: id_ty.clone(),
                    value: id_value.clone(),
                    reducibility: npa_kernel::Reducibility::Reducible,
                },
                Decl::Def {
                    name: format!("Bench.CvrPadB.Q{}", "b".repeat(long_suffix_len)),
                    universe_params: Vec::new(),
                    ty: id_ty,
                    value: id_value,
                    reducibility: npa_kernel::Reducibility::Reducible,
                },
            ],
        }
    }

    fn build_exact_size(target: usize) -> Result<Vec<u8>> {
        for short_suffix_len in 0..=127 {
            let base = encode_module_cert(&build_module_cert(
                exact_size_module(short_suffix_len, 0),
                &[],
            )?)?;
            if base.len() > target {
                continue;
            }
            let mut candidate = target - base.len();
            for _ in 0..8 {
                let cert = build_module_cert(exact_size_module(short_suffix_len, candidate), &[])?;
                let bytes = encode_module_cert(&cert)?;
                match bytes.len().cmp(&target) {
                    std::cmp::Ordering::Equal => {
                        let decoded = decode_module_cert(&bytes)?;
                        if encode_module_cert(&decoded)? != bytes {
                            return Err(CertError::NonCanonicalEncoding {
                                object: "CVR exact-size fixture",
                            });
                        }
                        return Ok(bytes);
                    }
                    std::cmp::Ordering::Less => {
                        candidate = candidate.saturating_add(target - bytes.len())
                    }
                    std::cmp::Ordering::Greater => {
                        candidate = candidate.saturating_sub(bytes.len() - target)
                    }
                }
            }
        }
        Err(CertError::NonCanonicalEncoding {
            object: "CVR exact-size fixture",
        })
    }

    fn benchmark_level_candidates() -> (Vec<String>, Vec<Level>) {
        // Declaration universe contexts accept at most 64 parameters. Build a
        // broad, shallow DAG from those parameters instead of treating the
        // table-node target as a parameter-count target.
        let params = (0..64)
            .map(|index| format!("u{index:02}"))
            .collect::<Vec<_>>();
        let bases = params.iter().cloned().map(Level::param).collect::<Vec<_>>();
        let intermediates = (0..4_095)
            .map(|index| Level::imax(bases[index / 64].clone(), bases[index % 64].clone()))
            .collect::<Vec<_>>();
        let candidates = (0..32_768)
            .map(|index| {
                Level::imax(
                    intermediates[index % intermediates.len()].clone(),
                    bases[(index / intermediates.len()) % bases.len()].clone(),
                )
            })
            .collect::<Vec<_>>();
        (params, candidates)
    }

    fn balanced_level(levels: &[Level]) -> Level {
        if levels.len() == 1 {
            return levels[0].clone();
        }
        let middle = levels.len() / 2;
        Level::imax(
            balanced_level(&levels[..middle]),
            balanced_level(&levels[middle..]),
        )
    }

    fn build_wide_levels() -> Result<Vec<u8>> {
        let (params, candidates) = benchmark_level_candidates();
        // 64 parameter nodes + 4,095 intermediate nodes + 30,689 candidate
        // nodes + 30,688 aggregation nodes = 65,536 level-table nodes.
        let root = balanced_level(&candidates[..30_689]);
        let cert = build_module_cert(
            CoreModule {
                name: Name::from_dotted("Bench.Cvr.WideLevels"),
                declarations: vec![Decl::Axiom {
                    name: "Bench.Cvr.WideLevels.root".to_owned(),
                    universe_params: params,
                    ty: Expr::sort(root),
                }],
            },
            &[],
        )?;
        if cert.level_table().len() != 65_536 {
            return Err(CertError::NonCanonicalEncoding {
                object: "CVR wide-level fixture identity",
            });
        }
        encode_module_cert(&cert)
    }

    fn build_deep_term_dag() -> Result<Vec<u8>> {
        // The producer recursively canonicalizes the source expression. Keep
        // that public producer path, but construct this exact boundary fixture
        // on a fixed large stack outside the measured validation interval.
        std::thread::Builder::new()
            .name("cvr-deep-term-fixture".to_owned())
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let leaf = Expr::sort(Level::zero());
                let mut root = leaf.clone();
                for _ in 0..8_190 {
                    root = Expr::pi("_", leaf.clone(), root);
                }
                let cert = build_module_cert(
                    CoreModule {
                        name: Name::from_dotted("Bench.Cvr.DeepTerm"),
                        declarations: vec![Decl::Axiom {
                            name: "Bench.Cvr.DeepTerm.root".to_owned(),
                            universe_params: Vec::new(),
                            ty: root,
                        }],
                    },
                    &[],
                )?;
                if cert.term_table().len() != 8_191 {
                    return Err(CertError::NonCanonicalEncoding {
                        object: "CVR deep-term fixture identity",
                    });
                }
                encode_module_cert(&cert)
            })
            .map_err(|_| CertError::DecodeError)?
            .join()
            .map_err(|_| CertError::DecodeError)?
    }

    fn balanced_term(leaves: &[Expr]) -> Expr {
        if leaves.len() == 1 {
            return leaves[0].clone();
        }
        let middle = leaves.len() / 2;
        Expr::pi(
            "_",
            balanced_term(&leaves[..middle]),
            balanced_term(&leaves[middle..]),
        )
    }

    fn build_wide_term_dag() -> Result<Vec<u8>> {
        let (params, levels) = benchmark_level_candidates();
        let leaves = levels.iter().cloned().map(Expr::sort).collect::<Vec<_>>();
        let root = balanced_term(&leaves);
        let mut declarations = Vec::with_capacity(32_768);
        declarations.push(Decl::Axiom {
            name: "Bench.Cvr.WideTerm.d00000".to_owned(),
            universe_params: params.clone(),
            ty: root,
        });
        declarations.extend((1..32_768).map(|index| Decl::Axiom {
            name: format!("Bench.Cvr.WideTerm.d{index:05}"),
            universe_params: params.clone(),
            ty: leaves[index].clone(),
        }));
        let cert = build_module_cert(
            CoreModule {
                name: Name::from_dotted("Bench.Cvr.WideTerm"),
                declarations,
            },
            &[],
        )?;
        if cert.term_table().len() != 65_535 {
            return Err(CertError::NonCanonicalEncoding {
                object: "CVR wide-term fixture identity",
            });
        }
        encode_module_cert(&cert)
    }

    fn malformed_early_level_reference() -> Result<Vec<u8>> {
        let bytes = build_exact_size(1_024)?;
        let mut cert = decode_module_cert(&bytes)?;
        let table_len = cert.level_table().len();
        let mut mutated = false;
        cert.mutate_parts_for_test(|parts| {
            if let Some(node) = parts
                .level_table
                .iter_mut()
                .find(|node| matches!(node, LevelNode::Succ(_)))
            {
                *node = LevelNode::Succ(table_len);
                mutated = true;
            }
        });
        if !mutated {
            return Err(CertError::NonCanonicalEncoding {
                object: "CVR malformed-level fixture lacks successor node",
            });
        }
        encode_module_cert(&cert)
    }

    fn malformed_middle_term_order() -> Result<Vec<u8>> {
        let bytes = build_exact_size(1_048_576)?;
        let mut cert = decode_module_cert(&bytes)?;
        let zero = cert
            .term_table()
            .iter()
            .position(|node| matches!(node, TermNode::BVar(0)))
            .ok_or(CertError::DecodeError)?;
        let one = cert
            .term_table()
            .iter()
            .position(|node| matches!(node, TermNode::BVar(1)))
            .ok_or(CertError::DecodeError)?;
        cert.mutate_parts_for_test(|parts| parts.term_table.swap(zero, one));
        encode_module_cert(&cert)
    }

    fn malformed_late_certificate_hash() -> Result<Vec<u8>> {
        let mut bytes = build_exact_size(MAX_CERTIFICATE_BYTES - 4_096)?;
        let hash_offset = bytes.len().checked_sub(32).ok_or(CertError::DecodeError)?;
        bytes[hash_offset] ^= 0x01;
        let decoded = decode_module_cert(&bytes)?;
        if encode_module_cert(&decoded)? != bytes {
            return Err(CertError::NonCanonicalEncoding {
                object: "CVR late-hash mutation",
            });
        }
        Ok(bytes)
    }

    fn fixture(scenario: Scenario) -> Result<Vec<u8>> {
        match scenario.id {
            "cvr-valid-1k" => build_exact_size(1_024),
            "cvr-valid-1m" => build_exact_size(1_048_576),
            "cvr-valid-near-byte-limit" => build_exact_size(MAX_CERTIFICATE_BYTES - 4_096),
            "cvr-valid-wide-levels" => build_wide_levels(),
            "cvr-valid-deep-term-dag" => build_deep_term_dag(),
            "cvr-valid-wide-term-dag" => build_wide_term_dag(),
            "cvr-malformed-early-level-reference" => malformed_early_level_reference(),
            "cvr-malformed-middle-term-order" => malformed_middle_term_order(),
            "cvr-malformed-late-certificate-hash" => malformed_late_certificate_hash(),
            _ => Err(CertError::DecodeError),
        }
    }

    fn scenario_by_id(id: &str) -> Result<Scenario> {
        SCENARIOS
            .iter()
            .copied()
            .find(|scenario| scenario.id == id)
            .ok_or(CertError::DecodeError)
    }

    fn counter_json(counter: ValidationReuseWorkCounter) -> String {
        format!(
            "{{\"level_key_encodings\":{},\"term_key_encodings\":{},\"level_hash_passes\":{},\"term_hash_passes\":{},\"canonical_full_encodings\":{},\"authoritative_prefix_uses\":{},\"streamed_prehash_uses\":{},\"lazy_built_materializations\":{},\"canonical_encoding_allocated_bytes\":{},\"key_scratch_allocated_bytes\":{}}}",
            counter.level_key_encodings,
            counter.term_key_encodings,
            counter.level_hash_passes,
            counter.term_hash_passes,
            counter.canonical_full_encodings,
            counter.authoritative_prefix_uses,
            counter.streamed_prehash_uses,
            counter.lazy_built_materializations,
            counter.canonical_encoding_allocated_bytes,
            counter.key_scratch_allocated_bytes,
        )
    }

    fn child_json(
        scenario: Scenario,
        sample_index: usize,
        input: &[u8],
        elapsed_ns: u128,
        allocation_events: u64,
        allocated_bytes: u64,
        counter: ValidationReuseWorkCounter,
    ) -> String {
        format!(
            "{{\"schema\":\"{CHILD_SCHEMA}\",\"scenario_id\":\"{}\",\"sample_index\":{},\"input_bytes\":{},\"input_sha256\":\"{}\",\"outcome\":\"{}\",\"error_stage\":{},\"validation_elapsed_ns\":{},\"allocation_events\":{},\"allocated_bytes\":{},\"work_counters\":{}}}",
            scenario.id,
            sample_index,
            input.len(),
            sha256_hex(input),
            scenario.expected.outcome(),
            scenario.expected.json_stage(),
            elapsed_ns,
            allocation_events,
            allocated_bytes,
            counter_json(counter),
        )
    }

    fn validate_expected_result(
        scenario: Scenario,
        result: &Result<ModuleCert>,
    ) -> std::result::Result<(), String> {
        match (scenario.expected, result) {
            (ExpectedStage::Accepted, Ok(_)) => Ok(()),
            (ExpectedStage::Accepted, Err(error)) => Err(format!("unexpected error: {error:?}")),
            (ExpectedStage::LevelReference, Err(CertError::DecodeError)) => Ok(()),
            (ExpectedStage::TermOrder, Err(CertError::NonCanonicalEncoding { object }))
                if *object == "TermTable" =>
            {
                Ok(())
            }
            (
                ExpectedStage::CertificateHash,
                Err(CertError::HashMismatch {
                    object: HashObject::ModuleCertificate,
                    ..
                }),
            ) => Ok(()),
            (_, result) => Err(format!("unexpected result: {result:?}")),
        }
    }

    fn required_absolute_path(name: &str) -> std::result::Result<PathBuf, String> {
        let value = env::var_os(name).ok_or_else(|| format!("missing {name}"))?;
        let path = PathBuf::from(value);
        if !path.is_absolute() {
            return Err(format!("{name} must be absolute"));
        }
        Ok(path)
    }

    fn required_canonical_regular_file(name: &str) -> std::result::Result<PathBuf, String> {
        let path = required_absolute_path(name)?;
        validate_canonical_regular_file(&path, name)?;
        Ok(path)
    }

    fn validate_canonical_regular_file(
        path: &Path,
        label: &str,
    ) -> std::result::Result<(), String> {
        if !path.is_absolute() {
            return Err(format!("{label} must be absolute"));
        }
        let mut cursor = PathBuf::new();
        for component in path.components() {
            cursor.push(component.as_os_str());
            let metadata = fs::symlink_metadata(&cursor)
                .map_err(|error| format!("inspect {label} {}: {error}", cursor.display()))?;
            if metadata.file_type().is_symlink() {
                return Err(format!("{label} path must not contain symbolic links"));
            }
        }
        let metadata = fs::symlink_metadata(path)
            .map_err(|error| format!("inspect {label} {}: {error}", path.display()))?;
        if metadata.file_type().is_symlink() || !metadata.is_file() {
            return Err(format!("{label} must be a regular non-symlink file"));
        }
        let canonical = fs::canonicalize(path)
            .map_err(|error| format!("canonicalize {label} {}: {error}", path.display()))?;
        if canonical != path {
            return Err(format!("{label} must already be canonical"));
        }
        Ok(())
    }

    fn valid_output_basename(name: &str) -> bool {
        let mut bytes = name.bytes();
        bytes
            .next()
            .is_some_and(|byte| byte.is_ascii_alphanumeric())
            && bytes.all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'.' | b'_' | b'-'))
    }

    fn validate_new_output_path(path: &Path, label: &str) -> std::result::Result<(), String> {
        if !path.is_absolute() {
            return Err(format!("{label} must be absolute"));
        }
        match fs::symlink_metadata(path) {
            Ok(_) => return Err(format!("{label} already exists")),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => return Err(format!("inspect {label}: {error}")),
        }
        let parent = path
            .parent()
            .filter(|parent| !parent.as_os_str().is_empty())
            .ok_or_else(|| format!("{label} has no parent"))?;
        let mut cursor = PathBuf::new();
        for component in parent.components() {
            cursor.push(component.as_os_str());
            let metadata = fs::symlink_metadata(&cursor)
                .map_err(|error| format!("inspect {label} parent {}: {error}", cursor.display()))?;
            if metadata.file_type().is_symlink() {
                return Err(format!("{label} parent must not contain symbolic links"));
            }
        }
        let metadata = fs::symlink_metadata(parent)
            .map_err(|error| format!("inspect {label} parent: {error}"))?;
        if metadata.file_type().is_symlink() || !metadata.is_dir() {
            return Err(format!("{label} parent must be a non-symlink directory"));
        }
        let canonical_parent = fs::canonicalize(parent)
            .map_err(|error| format!("canonicalize {label} parent: {error}"))?;
        if canonical_parent != parent {
            return Err(format!("{label} parent must already be canonical"));
        }
        let file_name = path
            .file_name()
            .and_then(|name| name.to_str())
            .ok_or_else(|| format!("{label} basename must be UTF-8"))?;
        if !valid_output_basename(file_name) {
            return Err(format!("{label} has an invalid basename"));
        }
        if canonical_parent.join(file_name) != path {
            return Err(format!(
                "{label} must already be a normalized canonical path"
            ));
        }
        Ok(())
    }

    fn required_new_output_path(name: &str) -> std::result::Result<PathBuf, String> {
        let path = required_absolute_path(name)?;
        validate_new_output_path(&path, name)?;
        Ok(path)
    }

    fn open_private_work_dir(
        require_empty: bool,
    ) -> std::result::Result<ClosedPrivateDirectory, String> {
        let path = required_absolute_path("NPA_CVR_BENCH_WORK_DIR")?;
        let directory = ClosedPrivateDirectory::open_existing(&path, "npa-cvr-benchmark")?;
        if require_empty {
            let (files, directories) = directory.catalog_root_paths()?;
            if !files.is_empty() || !directories.is_empty() {
                return Err("NPA_CVR_BENCH_WORK_DIR must start empty".to_owned());
            }
        }
        Ok(directory)
    }

    struct ControllerWorkDirectory(Option<ClosedPrivateDirectory>);

    impl ControllerWorkDirectory {
        fn open() -> std::result::Result<Self, String> {
            open_private_work_dir(true).map(|directory| Self(Some(directory)))
        }

        fn directory(&self) -> std::result::Result<&ClosedPrivateDirectory, String> {
            self.0
                .as_ref()
                .ok_or("CVR controller work directory was already cleaned".to_owned())
        }

        fn path(&self) -> std::result::Result<&Path, String> {
            Ok(self.directory()?.path())
        }

        fn create_executable_snapshot(
            &self,
            relative: &Path,
            source: &Path,
            maximum_bytes: u64,
            label: &str,
        ) -> std::result::Result<AttachedExecutable, String> {
            self.directory()?
                .create_executable_snapshot(relative, source, maximum_bytes, label)
        }

        fn read_regular_file(
            &self,
            relative: &Path,
            maximum_bytes: u64,
        ) -> std::result::Result<Vec<u8>, String> {
            self.directory()?.read_regular_file(relative, maximum_bytes)
        }

        fn cleanup_exact(mut self) -> std::result::Result<(), String> {
            self.0
                .take()
                .ok_or("CVR controller work directory was already cleaned".to_owned())?
                .remove_exact_root(&cvr_work_catalog())
        }
    }

    impl Drop for ControllerWorkDirectory {
        fn drop(&mut self) {
            if let Some(directory) = self.0.take() {
                let _ = directory.remove_allowed_root(&cvr_work_catalog());
            }
        }
    }

    fn cvr_work_catalog() -> BTreeSet<PathBuf> {
        let mut files = BTreeSet::new();
        files.insert(PathBuf::from("test-executable"));
        files.insert(PathBuf::from("measure-process"));
        for sample in 0..9 {
            for scenario in SCENARIOS {
                let stem = format!("{}-{sample}", scenario.id);
                for suffix in ["json", "stdout", "stderr"] {
                    files.insert(PathBuf::from(format!("{stem}.{suffix}")));
                }
            }
        }
        files
    }

    fn validate_direct_work_file(
        work_dir: &Path,
        path: &Path,
        expected_name: &str,
    ) -> std::result::Result<(), String> {
        if path != work_dir.join(expected_name)
            || path.parent() != Some(work_dir)
            || path.file_name().and_then(|name| name.to_str()) != Some(expected_name)
        {
            return Err("CVR child path escaped its private work directory".to_owned());
        }
        Ok(())
    }

    fn validate_closed_environment(mode: &str) -> std::result::Result<(), String> {
        for (name, _) in env::vars_os() {
            let name = name
                .to_str()
                .ok_or_else(|| "non-UTF-8 environment name".to_owned())?;
            if name.starts_with("NPA_CVR_BENCH_")
                && !matches!(
                    name,
                    "NPA_CVR_BENCH_MODE"
                        | "NPA_CVR_BENCH_SCENARIO_ID"
                        | "NPA_CVR_BENCH_SAMPLE_INDEX"
                        | "NPA_CVR_BENCH_CHILD_JSON"
                        | "NPA_CVR_BENCH_RUN_JSON"
                        | "NPA_CVR_BENCH_WORK_DIR"
                )
            {
                return Err(format!("unknown benchmark variable {name}"));
            }
        }
        match mode {
            "child" => {
                if env::var_os("NPA_CVR_BENCH_RUN_JSON").is_some() {
                    return Err("controller result path leaked into child".to_owned());
                }
            }
            "controller" => {
                if env::var_os("NPA_CVR_BENCH_SCENARIO_ID").is_some()
                    || env::var_os("NPA_CVR_BENCH_SAMPLE_INDEX").is_some()
                    || env::var_os("NPA_CVR_BENCH_CHILD_JSON").is_some()
                {
                    return Err("child variables leaked into controller".to_owned());
                }
            }
            "validator" => {
                if env::var_os("NPA_CVR_BENCH_SCENARIO_ID").is_some()
                    || env::var_os("NPA_CVR_BENCH_SAMPLE_INDEX").is_some()
                    || env::var_os("NPA_CVR_BENCH_CHILD_JSON").is_some()
                    || env::var_os("NPA_CVR_BENCH_WORK_DIR").is_some()
                {
                    return Err("controller/child variables leaked into validator".to_owned());
                }
            }
            _ => return Err("invalid benchmark mode".to_owned()),
        }
        Ok(())
    }

    fn run_child() -> std::result::Result<(), String> {
        let scenario_id =
            env::var("NPA_CVR_BENCH_SCENARIO_ID").map_err(|_| "missing scenario".to_owned())?;
        if scenario_id == "cvr-valid-deep-term-dag" {
            return std::thread::Builder::new()
                .name("npa-cvr-deep-child".to_owned())
                .stack_size(64 * 1024 * 1024)
                .spawn(run_child_inner)
                .map_err(|error| format!("spawn deep benchmark child: {error}"))?
                .join()
                .map_err(|_| "deep benchmark child thread panicked".to_owned())?;
        }
        run_child_inner()
    }

    fn run_child_inner() -> std::result::Result<(), String> {
        validate_closed_environment("child")?;
        let scenario_id =
            env::var("NPA_CVR_BENCH_SCENARIO_ID").map_err(|_| "missing scenario".to_owned())?;
        let scenario = scenario_by_id(&scenario_id).map_err(|error| format!("{error:?}"))?;
        let sample_index = env::var("NPA_CVR_BENCH_SAMPLE_INDEX")
            .map_err(|_| "missing sample".to_owned())?
            .parse::<usize>()
            .map_err(|_| "invalid sample".to_owned())?;
        if sample_index > 8 {
            return Err("sample must be 0..8".to_owned());
        }
        let work = open_private_work_dir(false)?;
        let work_dir = work.path().to_owned();
        let result_path = required_absolute_path("NPA_CVR_BENCH_CHILD_JSON")?;
        validate_direct_work_file(
            &work_dir,
            &result_path,
            &format!("{}-{sample_index}.json", scenario.id),
        )?;
        let input = fixture(scenario).map_err(|error| format!("fixture: {error:?}"))?;

        let warmup = verify_module_cert_hashes(&input);
        validate_expected_result(scenario, &warmup)?;
        crate::validation_reuse_allocation_meter::reset_and_start();
        let started = Instant::now();
        let measured = verify_module_cert_hashes(&input);
        let elapsed_ns = started.elapsed().as_nanos();
        let allocations = crate::validation_reuse_allocation_meter::stop();
        let mut counter = ValidationReuseWorkCounter::default();
        let observed =
            verify_module_cert_hashes_impl_with_validation_reuse_counter(&input, &mut counter);
        if warmup != measured || measured != observed {
            return Err("warmup/measured/observation results differ".to_owned());
        }
        validate_expected_result(scenario, &measured)?;

        let row = child_json(
            scenario,
            sample_index,
            &input,
            elapsed_ns,
            allocations.allocation_events,
            allocations.allocated_bytes,
            counter,
        );
        work.create_new_file(
            Path::new(
                result_path
                    .file_name()
                    .ok_or("child result path has no basename")?,
            ),
            format!("{row}\n").as_bytes(),
        )
    }

    fn parse_wrapper_tsv(value: &str) -> std::result::Result<(&str, u64, i32), String> {
        let row = value
            .strip_suffix('\n')
            .ok_or_else(|| "measure_process TSV needs one newline".to_owned())?;
        if row.contains('\n') || row.contains('\r') {
            return Err("invalid measure_process TSV".to_owned());
        }
        let fields = row.split('\t').collect::<Vec<_>>();
        let elapsed_ok = fields.first().is_some_and(|elapsed| {
            elapsed.split_once('.').is_some_and(|(whole, fraction)| {
                !whole.is_empty()
                    && whole.bytes().all(|byte| byte.is_ascii_digit())
                    && fraction.len() == 9
                    && fraction.bytes().all(|byte| byte.is_ascii_digit())
            })
        });
        if fields.len() != 3 || !elapsed_ok {
            return Err("invalid measure_process TSV".to_owned());
        }
        Ok((
            fields[0],
            fields[1].parse().map_err(|_| "invalid RSS".to_owned())?,
            fields[2].parse().map_err(|_| "invalid exit".to_owned())?,
        ))
    }

    fn append_process_fields(
        child: &str,
        elapsed: &str,
        peak_rss_kib: u64,
        exit_code: i32,
    ) -> std::result::Result<String, String> {
        let trimmed = child.trim_end();
        let prefix = trimmed
            .strip_suffix('}')
            .ok_or_else(|| "invalid child JSON".to_owned())?;
        if !prefix.starts_with(&format!("{{\"schema\":\"{CHILD_SCHEMA}\"")) {
            return Err("child schema mismatch".to_owned());
        }
        Ok(format!(
            "{prefix},\"process_elapsed_seconds\":\"{elapsed}\",\"peak_rss_kib\":{peak_rss_kib},\"exit_code\":{exit_code}}}"
        ))
    }

    #[derive(Clone)]
    struct SummaryObservation {
        scenario_id: String,
        validation_elapsed_ns: u64,
        allocation_events: u64,
        allocated_bytes: u64,
        process_peak_rss_kib: u64,
    }

    struct ParsedChildRow {
        validation_elapsed_ns: u64,
        allocation_events: u64,
        allocated_bytes: u64,
    }

    fn consume_prefix(input: &mut &str, expected: &str) -> std::result::Result<(), String> {
        *input = input
            .strip_prefix(expected)
            .ok_or_else(|| format!("expected child JSON fragment {expected:?}"))?;
        Ok(())
    }

    fn parse_canonical_unsigned(input: &mut &str) -> std::result::Result<u64, String> {
        let digits = input.bytes().take_while(u8::is_ascii_digit).count();
        if digits == 0 || (digits > 1 && input.as_bytes()[0] == b'0') {
            return Err("invalid canonical unsigned integer".to_owned());
        }
        let (number, remainder) = input.split_at(digits);
        *input = remainder;
        number
            .parse()
            .map_err(|_| "unsigned integer overflow".to_owned())
    }

    fn parse_child_row(
        value: &str,
        scenario: Scenario,
        sample_index: usize,
    ) -> std::result::Result<ParsedChildRow, String> {
        if sample_index > 8 {
            return Err("sample must be 0..8".to_owned());
        }
        let mut input = value;
        consume_prefix(
            &mut input,
            &format!(
                "{{\"schema\":\"{CHILD_SCHEMA}\",\"scenario_id\":\"{}\",\"sample_index\":{sample_index},\"input_bytes\":",
                scenario.id
            ),
        )?;
        let input_bytes = parse_canonical_unsigned(&mut input)?;
        if input_bytes != scenario.input_bytes {
            return Err("child input byte identity mismatch".to_owned());
        }
        consume_prefix(&mut input, ",\"input_sha256\":\"")?;
        if input.len() < 64 {
            return Err("truncated child input SHA-256".to_owned());
        }
        let (input_sha256, remainder) = input.split_at(64);
        if input_sha256 != scenario.input_sha256 {
            return Err("child input SHA-256 identity mismatch".to_owned());
        }
        input = remainder;
        consume_prefix(
            &mut input,
            &format!(
                "\",\"outcome\":\"{}\",\"error_stage\":{},\"validation_elapsed_ns\":",
                scenario.expected.outcome(),
                scenario.expected.json_stage(),
            ),
        )?;
        let validation_elapsed_ns = parse_canonical_unsigned(&mut input)?;
        consume_prefix(&mut input, ",\"allocation_events\":")?;
        let allocation_events = parse_canonical_unsigned(&mut input)?;
        consume_prefix(&mut input, ",\"allocated_bytes\":")?;
        let allocated_bytes = parse_canonical_unsigned(&mut input)?;
        consume_prefix(&mut input, ",\"work_counters\":{")?;
        let counter_fields = [
            "level_key_encodings",
            "term_key_encodings",
            "level_hash_passes",
            "term_hash_passes",
            "canonical_full_encodings",
            "authoritative_prefix_uses",
            "streamed_prehash_uses",
            "lazy_built_materializations",
            "canonical_encoding_allocated_bytes",
            "key_scratch_allocated_bytes",
        ];
        for (index, field) in counter_fields.into_iter().enumerate() {
            consume_prefix(
                &mut input,
                &format!("{}\"{field}\":", if index == 0 { "" } else { "," }),
            )?;
            let _ = parse_canonical_unsigned(&mut input)?;
        }
        consume_prefix(&mut input, "}}\n")?;
        if !input.is_empty() {
            return Err("trailing child JSON data".to_owned());
        }
        Ok(ParsedChildRow {
            validation_elapsed_ns,
            allocation_events,
            allocated_bytes,
        })
    }

    fn metric_summary(values: &[u64]) -> std::result::Result<String, String> {
        if values.len() != 9 {
            return Err(format!("expected nine samples, got {}", values.len()));
        }
        let mut sorted = values.to_vec();
        sorted.sort_unstable();
        let median = sorted[4];
        let mut deviations = values
            .iter()
            .map(|value| value.abs_diff(median))
            .collect::<Vec<_>>();
        deviations.sort_unstable();
        let raw = values
            .iter()
            .map(u64::to_string)
            .collect::<Vec<_>>()
            .join(",");
        Ok(format!(
            "{{\"raw\":[{raw}],\"median\":{median},\"mad\":{},\"min\":{},\"max\":{}}}",
            deviations[4], sorted[0], sorted[8]
        ))
    }

    fn scenario_summary(
        scenario: Scenario,
        observations: &[SummaryObservation],
    ) -> std::result::Result<String, String> {
        let selected = observations
            .iter()
            .filter(|observation| observation.scenario_id == scenario.id)
            .collect::<Vec<_>>();
        let validation_elapsed_ns = selected
            .iter()
            .map(|row| row.validation_elapsed_ns)
            .collect::<Vec<_>>();
        let allocation_events = selected
            .iter()
            .map(|row| row.allocation_events)
            .collect::<Vec<_>>();
        let allocated_bytes = selected
            .iter()
            .map(|row| row.allocated_bytes)
            .collect::<Vec<_>>();
        let process_peak_rss_kib = selected
            .iter()
            .map(|row| row.process_peak_rss_kib)
            .collect::<Vec<_>>();
        Ok(format!(
            "{{\"scenario_id\":\"{}\",\"validation_elapsed_ns\":{},\"allocation_events\":{},\"allocated_bytes\":{},\"process_peak_rss_kib\":{}}}",
            scenario.id,
            metric_summary(&validation_elapsed_ns)?,
            metric_summary(&allocation_events)?,
            metric_summary(&allocated_bytes)?,
            metric_summary(&process_peak_rss_kib)?,
        ))
    }

    fn file_sha256(path: &Path, maximum_bytes: u64) -> std::result::Result<String, String> {
        read_absolute_regular_file(path, maximum_bytes, "CVR hashed input")
            .map(|bytes| sha256_hex(&bytes))
    }

    fn runtime_cvr_source_set_sha256() -> std::result::Result<String, String> {
        let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let canonical_workspace = fs::canonicalize(&workspace)
            .map_err(|error| format!("canonicalize CVR workspace: {error}"))?;
        validate_runtime_source_set(
            &canonical_workspace,
            env!("NPA_BUILD_CVR_SOURCE_SET_PATHS"),
            b"npa-cvr-source-set-v2\0",
            env!("NPA_BUILD_CVR_SOURCE_SET_SHA256"),
            "CVR",
        )?
        .strip_prefix("sha256:")
        .map(str::to_owned)
        .ok_or_else(|| "CVR source-set identity prefix mismatch".to_owned())
    }

    fn valid_source_identity(value: &str) -> bool {
        let oid = value.strip_suffix("-dirty").unwrap_or(value);
        oid.len() == 40
            && oid
                .bytes()
                .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
    }

    fn command_stdout(
        executable: &str,
        arguments: &[&str],
        current_dir: &Path,
    ) -> std::result::Result<String, String> {
        let output = Command::new(executable)
            .args(arguments)
            .current_dir(current_dir)
            .output()
            .map_err(|error| format!("run {executable}: {error}"))?;
        if !output.status.success() || !output.stderr.is_empty() {
            return Err(format!("{executable} failed or wrote stderr"));
        }
        let value = String::from_utf8(output.stdout)
            .map_err(|_| format!("{executable} output is not UTF-8"))?;
        value
            .strip_suffix('\n')
            .filter(|line| !line.contains(['\n', '\r']))
            .map(str::to_owned)
            .ok_or_else(|| format!("{executable} output must be exactly one line"))
    }

    fn runtime_source_identity() -> std::result::Result<String, String> {
        let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let oid = command_stdout("/usr/bin/git", &["rev-parse", "HEAD"], &workspace)?;
        if !valid_source_identity(&oid) || oid.ends_with("-dirty") {
            return Err("runtime Git HEAD is not a lowercase 40-digit OID".to_owned());
        }
        let status = Command::new("/usr/bin/git")
            .args(["status", "--porcelain", "--untracked-files=normal"])
            .current_dir(&workspace)
            .output()
            .map_err(|error| format!("run Git status: {error}"))?;
        if !status.status.success() || !status.stderr.is_empty() {
            return Err("Git status failed or wrote stderr".to_owned());
        }
        Ok(if status.stdout.is_empty() {
            oid
        } else {
            format!("{oid}-dirty")
        })
    }

    fn validate_runtime_build_inputs() -> std::result::Result<(), String> {
        let cargo_lock = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .canonicalize()
            .map_err(|error| format!("canonicalize CVR workspace: {error}"))?
            .join("Cargo.lock");
        if file_sha256(&cargo_lock, MAX_CARGO_LOCK_BYTES)? != env!("NPA_BUILD_CARGO_LOCK_SHA256") {
            return Err(
                "runtime Cargo.lock differs from the lock used to build the test".to_owned(),
            );
        }
        if runtime_cvr_source_set_sha256()? != env!("NPA_BUILD_CVR_SOURCE_SET_SHA256") {
            return Err(
                "runtime CVR source set differs from bytes used to build the test".to_owned(),
            );
        }
        let embedded = env!("NPA_BUILD_SOURCE_IDENTITY");
        if embedded == "unbound" || !valid_source_identity(embedded) {
            return Err("benchmark binary has no valid build-bound source identity".to_owned());
        }
        if runtime_source_identity()? != embedded {
            return Err("runtime Git source identity differs from the benchmark build".to_owned());
        }
        Ok(())
    }

    fn decode_build_hex(encoded: &str) -> std::result::Result<String, String> {
        if !encoded.len().is_multiple_of(2) {
            return Err("embedded build hex has odd length".to_owned());
        }
        let mut bytes = Vec::with_capacity(encoded.len() / 2);
        for pair in encoded.as_bytes().as_chunks::<2>().0 {
            let high = hex_nibble(pair[0]).ok_or("embedded build hex contains a non-hex digit")?;
            let low = hex_nibble(pair[1]).ok_or("embedded build hex contains a non-hex digit")?;
            bytes.push((high << 4) | low);
        }
        String::from_utf8(bytes).map_err(|_| "embedded build value is not UTF-8".to_owned())
    }

    fn hex_nibble(byte: u8) -> Option<u8> {
        match byte {
            b'0'..=b'9' => Some(byte - b'0'),
            b'a'..=b'f' => Some(byte - b'a' + 10),
            _ => None,
        }
    }

    fn embedded_build_features_json() -> String {
        env!("NPA_BUILD_CARGO_FEATURES")
            .split(',')
            .filter(|feature| !feature.is_empty())
            .map(json_string)
            .collect::<Vec<_>>()
            .join(",")
    }

    fn run_report_prefix_from_hashes(
        executable_sha256: &str,
        wrapper_sha256: &str,
    ) -> std::result::Result<String, String> {
        let rustc_vv = decode_build_hex(env!("NPA_BUILD_RUSTC_VV_HEX"))?;
        let features = embedded_build_features_json();
        let rustflags = decode_build_hex(env!("NPA_BUILD_RUSTFLAGS_HEX"))?;
        Ok(format!(
            "{{\"schema\":\"{RUN_SCHEMA}\",\"catalog_schema\":\"{CATALOG_SCHEMA}\",\"warmup_per_child\":1,\"samples_per_scenario\":9,\"interleave\":\"sample-major-catalog-order\",\"build_identity\":{{\"source_identity\":\"{}\",\"cargo_lock_sha256\":\"{}\",\"rustc_vv\":{},\"target\":\"{}\",\"profile\":{},\"features\":[{}],\"rustflags\":{},\"cvr_source_set_sha256\":\"{}\",\"test_executable_sha256\":\"{}\",\"measure_process_sha256\":\"{}\"}},\"rows\":[",
            env!("NPA_BUILD_SOURCE_IDENTITY"),
            env!("NPA_BUILD_CARGO_LOCK_SHA256"),
            json_string(&rustc_vv),
            env!("NPA_BUILD_TARGET"),
            json_string(env!("NPA_BUILD_CARGO_PROFILE")),
            features,
            json_string(&rustflags),
            env!("NPA_BUILD_CVR_SOURCE_SET_SHA256"),
            executable_sha256,
            wrapper_sha256,
        ))
    }

    fn run_report_prefix(executable: &Path, wrapper: &Path) -> std::result::Result<String, String> {
        run_report_prefix_from_hashes(
            &file_sha256(executable, MAX_CVR_EXECUTABLE_BYTES)?,
            &file_sha256(wrapper, MAX_CVR_EXECUTABLE_BYTES)?,
        )
    }

    fn split_closed_array(input: &str) -> std::result::Result<(&str, &str), String> {
        let mut in_string = false;
        let mut escaped = false;
        let mut object_depth = 0_usize;
        let mut array_depth = 0_usize;
        for (index, byte) in input.bytes().enumerate() {
            if in_string {
                if escaped {
                    escaped = false;
                } else if byte == b'\\' {
                    escaped = true;
                } else if byte == b'"' {
                    in_string = false;
                }
                continue;
            }
            match byte {
                b'"' => in_string = true,
                b'{' => object_depth += 1,
                b'}' => object_depth = object_depth.checked_sub(1).ok_or("unbalanced object")?,
                b'[' => array_depth += 1,
                b']' if object_depth == 0 && array_depth == 0 => {
                    return Ok((&input[..index], &input[index + 1..]));
                }
                b']' => array_depth = array_depth.checked_sub(1).ok_or("unbalanced array")?,
                _ => {}
            }
        }
        Err("unterminated array".to_owned())
    }

    fn split_top_level_objects(input: &str) -> std::result::Result<Vec<&str>, String> {
        if input.is_empty() {
            return Ok(Vec::new());
        }
        let mut values = Vec::new();
        let mut start = 0_usize;
        let mut depth = 0_usize;
        let mut in_string = false;
        let mut escaped = false;
        for (index, byte) in input.bytes().enumerate() {
            if in_string {
                if escaped {
                    escaped = false;
                } else if byte == b'\\' {
                    escaped = true;
                } else if byte == b'"' {
                    in_string = false;
                }
                continue;
            }
            match byte {
                b'"' => in_string = true,
                b'{' => {
                    if depth == 0 && index != start {
                        return Err("array object has an invalid prefix".to_owned());
                    }
                    depth += 1;
                }
                b'}' => {
                    depth = depth.checked_sub(1).ok_or("unbalanced object")?;
                    if depth == 0 {
                        values.push(&input[start..=index]);
                        if index + 1 == input.len() {
                            start = input.len();
                        } else if input.as_bytes().get(index + 1) == Some(&b',') {
                            start = index + 2;
                        } else {
                            return Err("array objects must use one comma".to_owned());
                        }
                    }
                }
                _ if depth == 0 => {}
                _ => {}
            }
        }
        if depth != 0 || in_string || start != input.len() {
            return Err("unterminated array object".to_owned());
        }
        Ok(values)
    }

    fn parse_process_row(
        row: &str,
        scenario: Scenario,
        sample_index: usize,
    ) -> std::result::Result<SummaryObservation, String> {
        let marker = ",\"process_elapsed_seconds\":\"";
        let (child_prefix, process) = row.rsplit_once(marker).ok_or("missing process fields")?;
        let child = format!("{child_prefix}}}\n");
        let parsed = parse_child_row(&child, scenario, sample_index)?;
        let (elapsed, process) = process
            .split_once("\",\"peak_rss_kib\":")
            .ok_or("missing process RSS")?;
        if !elapsed.split_once('.').is_some_and(|(whole, fraction)| {
            !whole.is_empty()
                && whole.bytes().all(|byte| byte.is_ascii_digit())
                && fraction.len() == 9
                && fraction.bytes().all(|byte| byte.is_ascii_digit())
        }) {
            return Err("invalid process elapsed value".to_owned());
        }
        let (rss, exit) = process
            .split_once(",\"exit_code\":")
            .ok_or("missing process exit")?;
        let peak_rss_kib = rss.parse().map_err(|_| "invalid process RSS")?;
        if exit != "0}" {
            return Err("process exit must be exact zero".to_owned());
        }
        Ok(SummaryObservation {
            scenario_id: scenario.id.to_owned(),
            validation_elapsed_ns: parsed.validation_elapsed_ns,
            allocation_events: parsed.allocation_events,
            allocated_bytes: parsed.allocated_bytes,
            process_peak_rss_kib: peak_rss_kib,
        })
    }

    fn validate_run_report(
        value: &str,
        executable: &Path,
        wrapper: &Path,
    ) -> std::result::Result<(), String> {
        validate_run_report_with_hashes(
            value,
            &file_sha256(executable, MAX_CVR_EXECUTABLE_BYTES)?,
            &file_sha256(wrapper, MAX_CVR_EXECUTABLE_BYTES)?,
        )
    }

    fn validate_run_report_with_hashes(
        value: &str,
        executable_sha256: &str,
        wrapper_sha256: &str,
    ) -> std::result::Result<(), String> {
        let prefix = run_report_prefix_from_hashes(executable_sha256, wrapper_sha256)?;
        let rows_and_rest = value.strip_prefix(&prefix).ok_or("run prefix mismatch")?;
        let (rows, rest) = split_closed_array(rows_and_rest)?;
        let summaries_and_rest = rest
            .strip_prefix(",\"summaries\":[")
            .ok_or("run summaries key mismatch")?;
        let (summaries, suffix) = split_closed_array(summaries_and_rest)?;
        if suffix != "}\n" {
            return Err("run suffix or unknown root field".to_owned());
        }
        let rows = split_top_level_objects(rows)?;
        if rows.len() != 81 {
            return Err(format!("run must contain 81 rows, got {}", rows.len()));
        }
        let mut observations = Vec::with_capacity(81);
        for (index, row) in rows.into_iter().enumerate() {
            observations.push(parse_process_row(
                row,
                SCENARIOS[index % SCENARIOS.len()],
                index / SCENARIOS.len(),
            )?);
        }
        let summaries = split_top_level_objects(summaries)?;
        if summaries.len() != SCENARIOS.len() {
            return Err("run must contain nine summaries".to_owned());
        }
        for (scenario, summary) in SCENARIOS.into_iter().zip(summaries) {
            if scenario_summary(scenario, &observations)? != summary {
                return Err(format!("summary mismatch for {}", scenario.id));
            }
        }
        Ok(())
    }

    fn run_controller() -> std::result::Result<(), String> {
        validate_closed_environment("controller")?;
        let wrapper = required_canonical_regular_file("NPA_MEASURE_PROCESS")?;
        let run_path = required_new_output_path("NPA_CVR_BENCH_RUN_JSON")?;
        let executable = env::current_exe().map_err(|error| format!("current exe: {error}"))?;
        let executable = fs::canonicalize(&executable)
            .map_err(|error| format!("canonicalize current executable: {error}"))?;
        validate_canonical_regular_file(&executable, "current test executable")?;
        let work = ControllerWorkDirectory::open()?;
        let work_dir = work.path()?.to_owned();
        validate_runtime_build_inputs()?;
        let executable_snapshot = work.create_executable_snapshot(
            Path::new("test-executable"),
            &executable,
            MAX_CVR_EXECUTABLE_BYTES,
            "CVR test executable",
        )?;
        let wrapper_snapshot = work.create_executable_snapshot(
            Path::new("measure-process"),
            &wrapper,
            MAX_CVR_EXECUTABLE_BYTES,
            "CVR measure-process",
        )?;
        verify_cvr_executables(&executable_snapshot, &wrapper_snapshot)?;
        let mut rows = Vec::with_capacity(81);
        let mut observations = Vec::with_capacity(81);
        for sample_index in 0..9 {
            for scenario in SCENARIOS {
                let stem = format!("{}-{sample_index}", scenario.id);
                let child_json_path = work_dir.join(format!("{stem}.json"));
                let child_stdout = work_dir.join(format!("{stem}.stdout"));
                let child_stderr = work_dir.join(format!("{stem}.stderr"));
                for (path, suffix) in [
                    (&child_json_path, "json"),
                    (&child_stdout, "stdout"),
                    (&child_stderr, "stderr"),
                ] {
                    validate_direct_work_file(&work_dir, path, &format!("{stem}.{suffix}"))?;
                    if fs::symlink_metadata(path).is_ok() {
                        return Err(format!(
                            "refusing an existing CVR work file: {}",
                            path.display()
                        ));
                    }
                }
                verify_cvr_executables(&executable_snapshot, &wrapper_snapshot)?;
                let output = Command::new(wrapper_snapshot.path())
                    .arg("--output")
                    .arg(&child_stdout)
                    .arg("--stderr")
                    .arg(&child_stderr)
                    .arg("--")
                    .arg(executable_snapshot.path())
                    .arg(TEST_NAME)
                    .arg("--exact")
                    .arg("--ignored")
                    .env("NPA_CVR_BENCH_MODE", "child")
                    .env("NPA_CVR_BENCH_SCENARIO_ID", scenario.id)
                    .env("NPA_CVR_BENCH_SAMPLE_INDEX", sample_index.to_string())
                    .env("NPA_CVR_BENCH_CHILD_JSON", &child_json_path)
                    .env("NPA_CVR_BENCH_WORK_DIR", &work_dir)
                    .env_remove("NPA_CVR_BENCH_RUN_JSON")
                    .env_remove("NPA_MEASURE_PROCESS")
                    .output()
                    .map_err(|error| format!("launch wrapper: {error}"))?;
                verify_cvr_executables(&executable_snapshot, &wrapper_snapshot)?;
                if !output.status.success() {
                    return Err(format!("wrapper failed for {stem}: {:?}", output.status));
                }
                let wrapper_stdout = String::from_utf8(output.stdout)
                    .map_err(|_| "wrapper stdout is not UTF-8".to_owned())?;
                let (elapsed, peak_rss_kib, exit_code) = parse_wrapper_tsv(&wrapper_stdout)?;
                if exit_code != 0 {
                    return Err(format!("child exit {exit_code} for {stem}"));
                }
                let stderr = work.read_regular_file(
                    Path::new(child_stderr.file_name().ok_or("stderr has no basename")?),
                    1024 * 1024,
                )?;
                if !stderr.is_empty() {
                    return Err(format!("child stderr was not empty for {stem}"));
                }
                let child = String::from_utf8(
                    work.read_regular_file(
                        Path::new(
                            child_json_path
                                .file_name()
                                .ok_or("child JSON has no basename")?,
                        ),
                        16 * 1024 * 1024,
                    )?,
                )
                .map_err(|_| "child result is not UTF-8".to_owned())?;
                let _ = work.read_regular_file(
                    Path::new(child_stdout.file_name().ok_or("stdout has no basename")?),
                    16 * 1024 * 1024,
                )?;
                let parsed = parse_child_row(&child, scenario, sample_index)
                    .map_err(|error| format!("invalid child row for {stem}: {error}"))?;
                observations.push(SummaryObservation {
                    scenario_id: scenario.id.to_owned(),
                    validation_elapsed_ns: parsed.validation_elapsed_ns,
                    allocation_events: parsed.allocation_events,
                    allocated_bytes: parsed.allocated_bytes,
                    process_peak_rss_kib: peak_rss_kib,
                });
                rows.push(append_process_fields(
                    &child,
                    elapsed,
                    peak_rss_kib,
                    exit_code,
                )?);
            }
        }
        if rows.len() != 81 {
            return Err("missing benchmark rows".to_owned());
        }

        let profile = env!("NPA_BUILD_CARGO_PROFILE");
        if profile != "release" {
            return Err(format!(
                "release benchmark controller was built with Cargo profile {profile}"
            ));
        }
        let summaries = SCENARIOS
            .iter()
            .map(|scenario| scenario_summary(*scenario, &observations))
            .collect::<std::result::Result<Vec<_>, _>>()?
            .join(",");
        let report = format!(
            "{}{}],\"summaries\":[{}]}}\n",
            run_report_prefix_from_hashes(executable_snapshot.sha256(), wrapper_snapshot.sha256())?,
            rows.join(","),
            summaries,
        );
        validate_run_report_with_hashes(
            &report,
            executable_snapshot.sha256(),
            wrapper_snapshot.sha256(),
        )?;
        let mut output = create_new_absolute_file(&run_path, "CVR run report")?;
        output
            .write_all(report.as_bytes())
            .map_err(|error| format!("write run report: {error}"))?;
        output
            .sync_all()
            .map_err(|error| format!("sync run report: {error}"))?;
        verify_cvr_executables(&executable_snapshot, &wrapper_snapshot)?;
        drop(executable_snapshot);
        drop(wrapper_snapshot);
        work.cleanup_exact()
    }

    fn verify_cvr_executables(
        executable: &AttachedExecutable,
        wrapper: &AttachedExecutable,
    ) -> std::result::Result<(), String> {
        executable.verify()?;
        wrapper.verify()
    }

    #[test]
    fn validation_reuse_executable_snapshot_rejects_basename_swap() {
        let work = ClosedPrivateDirectory::new("npa-cvr-executable-swap").unwrap();
        let executable = env::current_exe().unwrap();
        let snapshot = work
            .create_executable_snapshot(
                Path::new("test-executable"),
                &executable,
                MAX_CVR_EXECUTABLE_BYTES,
                "CVR swap probe",
            )
            .unwrap();
        let path = snapshot.path().to_owned();
        let relocated = path.with_extension("opened");
        fs::rename(&path, &relocated).unwrap();
        fs::write(&path, b"replacement").unwrap();
        assert!(snapshot.verify().is_err());
        fs::remove_file(&path).unwrap();
        fs::rename(&relocated, &path).unwrap();
        drop(snapshot);
        work.remove_exact_root(&BTreeSet::from([PathBuf::from("test-executable")]))
            .unwrap();
    }

    #[test]
    fn validation_reuse_controller_work_guard_cleans_partial_wrapper_failure() {
        let directory = ClosedPrivateDirectory::new("npa-cvr-partial-wrapper-failure").unwrap();
        let root = directory.path().to_owned();
        let work = ControllerWorkDirectory(Some(directory));
        for relative in [
            "test-executable",
            "measure-process",
            "cvr-valid-1k-0.stdout",
            "cvr-valid-1k-0.stderr",
        ] {
            work.directory()
                .unwrap()
                .create_new_file(Path::new(relative), b"partial")
                .unwrap();
        }

        let wrapper_result: std::result::Result<(), String> =
            Err("simulated wrapper failure".to_owned());
        assert!(wrapper_result.is_err());
        drop(work);
        assert!(!root.exists(), "partial controller work root leaked");
    }

    fn run_validator() -> std::result::Result<(), String> {
        validate_closed_environment("validator")?;
        let wrapper = required_canonical_regular_file("NPA_MEASURE_PROCESS")?;
        let run_path = required_absolute_path("NPA_CVR_BENCH_RUN_JSON")?;
        let executable = env::current_exe().map_err(|error| format!("current exe: {error}"))?;
        let executable = fs::canonicalize(&executable)
            .map_err(|error| format!("canonicalize current executable: {error}"))?;
        validate_canonical_regular_file(&executable, "current test executable")?;
        validate_runtime_build_inputs()?;
        validate_canonical_regular_file(&run_path, "CVR run report")?;
        let report = String::from_utf8(read_absolute_regular_file(
            &run_path,
            MAX_CVR_REPORT_BYTES,
            "CVR run report",
        )?)
        .map_err(|_| "CVR run report is not UTF-8".to_owned())?;
        validate_run_report(&report, &executable, &wrapper)
    }

    #[test]
    fn validation_reuse_benchmark_fixture_catalog() {
        let expected = [
            (
                1_024,
                "37bb8c5ffab5a0bdc67f456dd07d82253b1c3ac2f57a774379f78d8e784d22f6",
                2,
                7,
                2,
                7,
            ),
            (
                1_048_576,
                "aff973abaf0e008e655b513f2e786833e36f589623690a10b7b03ef9f271fe7f",
                2,
                7,
                2,
                7,
            ),
            (
                MAX_CERTIFICATE_BYTES - 4_096,
                "2b4f562ae79f3106d20de189c0aca3eff3b1e7a99ad96b8a9973b77d0355580c",
                2,
                7,
                2,
                7,
            ),
            (
                338_229,
                "2715bdbf58954b2eb29aca112fc3f86659651eaec912f684dc7234f0163ebfb0",
                65_536,
                1,
                65_536,
                1,
            ),
            (
                33_159,
                "f87620b08d912f14bd4cc6798c430ea372311f0c5315f6ae127a9514945ace73",
                1,
                8_191,
                1,
                8_191,
            ),
            (
                25_229_633,
                "9b7eb68a02918cd884f6062f79c83553898822aeb26c390b704a0c912ce709d4",
                36_927,
                65_535,
                36_927,
                65_535,
            ),
            (
                1_024,
                "01400e05578ab55bef0b2421fc134c841ae44c8a3e3aee80a66fb493a6154168",
                2,
                7,
                0,
                0,
            ),
            (
                1_048_576,
                "0e695e2b8af02469ad9bd15f4fae46bd57430842ed5cf69ed5a972a61df8d6c1",
                2,
                7,
                2,
                3,
            ),
            (
                MAX_CERTIFICATE_BYTES - 4_096,
                "76a0a53ea9024d548b363d956569bb2b12d99a21e16e25e4dff5bce361124bc4",
                2,
                7,
                2,
                7,
            ),
        ];
        assert_eq!(SCENARIOS.len(), expected.len());
        for (scenario, (bytes_len, sha256, levels, terms, level_keys, term_keys)) in
            SCENARIOS.into_iter().zip(expected)
        {
            let bytes = fixture(scenario).unwrap();
            assert_eq!(bytes.len(), bytes_len, "{} byte count", scenario.id);
            assert_eq!(sha256_hex(&bytes), sha256, "{} input hash", scenario.id);
            assert_eq!(scenario.input_bytes, u64::try_from(bytes_len).unwrap());
            assert_eq!(scenario.input_sha256, sha256);
            let decoded = decode_module_cert(&bytes).unwrap();
            let roots = decoded
                .declarations()
                .iter()
                .flat_map(|declaration| {
                    let mut roots = Vec::new();
                    collect_decl_payload_term_roots(&declaration.decl, &mut roots);
                    roots
                })
                .collect::<Vec<_>>();
            let structural = structural_preflight(&decoded);
            match scenario.id {
                "cvr-valid-1k"
                | "cvr-valid-1m"
                | "cvr-valid-near-byte-limit"
                | "cvr-malformed-middle-term-order"
                | "cvr-malformed-late-certificate-hash" => {
                    assert_eq!(decoded.header().module.as_dotted(), "Bench.Cvr.ExactSize");
                    assert_eq!(
                        (decoded.name_table().len(), decoded.declarations().len()),
                        (3, 2)
                    );
                    assert_eq!(
                        (decoded.export_block().len(), roots.as_slice()),
                        (2, &[6, 5, 6, 5][..])
                    );
                    assert!(decoded.declarations().iter().all(|declaration| matches!(
                        declaration.decl,
                        DeclPayload::Def {
                            ref universe_params,
                            ty: 6,
                            value: 5,
                            reducibility: crate::types::CertReducibility::Reducible,
                            ..
                        } if universe_params.is_empty()
                    )));
                    assert_eq!(
                        structural,
                        Ok(crate::structural::StructuralCost {
                            max_depth: 4,
                            max_root_expansion: 7,
                            certificate_expansion: 56,
                        })
                    );
                }
                "cvr-valid-wide-levels" => {
                    assert_eq!(decoded.header().module.as_dotted(), "Bench.Cvr.WideLevels");
                    assert_eq!(
                        (decoded.name_table().len(), decoded.declarations().len()),
                        (66, 1)
                    );
                    assert_eq!(
                        (decoded.export_block().len(), roots.as_slice()),
                        (1, &[0][..])
                    );
                    assert!(matches!(
                        &decoded.declarations()[0].decl,
                        DeclPayload::Axiom { universe_params, ty: 0, .. }
                            if universe_params.len() == 64
                    ));
                    assert_eq!(
                        structural,
                        Ok(crate::structural::StructuralCost {
                            max_depth: 19,
                            max_root_expansion: 184_134,
                            certificate_expansion: 368_268,
                        })
                    );
                }
                "cvr-valid-deep-term-dag" => {
                    assert_eq!(decoded.header().module.as_dotted(), "Bench.Cvr.DeepTerm");
                    assert_eq!(
                        (decoded.name_table().len(), decoded.declarations().len()),
                        (2, 1)
                    );
                    assert_eq!(
                        (decoded.export_block().len(), roots.as_slice()),
                        (1, &[8_190][..])
                    );
                    assert!(matches!(
                        &decoded.declarations()[0].decl,
                        DeclPayload::Axiom { universe_params, ty: 8_190, .. }
                            if universe_params.is_empty()
                    ));
                    assert_eq!(
                        structural,
                        Ok(crate::structural::StructuralCost {
                            max_depth: 8_192,
                            max_root_expansion: 24_572,
                            certificate_expansion: 49_144,
                        })
                    );
                }
                "cvr-valid-wide-term-dag" => {
                    assert_eq!(decoded.header().module.as_dotted(), "Bench.Cvr.WideTerm");
                    assert_eq!(
                        (decoded.name_table().len(), decoded.declarations().len()),
                        (32_833, 32_768)
                    );
                    assert_eq!(
                        (decoded.export_block().len(), roots.len()),
                        (32_768, 32_768)
                    );
                    assert_eq!(roots.first(), Some(&65_534));
                    assert_eq!(roots.last(), Some(&6_841));
                    assert!(decoded.declarations().iter().all(|declaration| matches!(
                        &declaration.decl,
                        DeclPayload::Axiom { universe_params, .. }
                            if universe_params.len() == 64
                    )));
                    assert_eq!(
                        structural,
                        Ok(crate::structural::StructuralCost {
                            max_depth: 19,
                            max_root_expansion: 229_375,
                            certificate_expansion: 851_954,
                        })
                    );
                }
                "cvr-malformed-early-level-reference" => {
                    assert_eq!(decoded.header().module.as_dotted(), "Bench.Cvr.ExactSize");
                    assert_eq!(
                        (decoded.name_table().len(), decoded.declarations().len()),
                        (3, 2)
                    );
                    assert_eq!(
                        (decoded.export_block().len(), roots.as_slice()),
                        (2, &[6, 5, 6, 5][..])
                    );
                    assert_eq!(structural, Err(CertError::DecodeError));
                }
                _ => unreachable!(),
            }
            assert_eq!(
                decoded.level_table().len(),
                levels,
                "{} levels",
                scenario.id
            );
            assert_eq!(decoded.term_table().len(), terms, "{} terms", scenario.id);

            let mut counter = ValidationReuseWorkCounter::default();
            let observed =
                verify_module_cert_hashes_impl_with_validation_reuse_counter(&bytes, &mut counter);
            validate_expected_result(scenario, &observed).unwrap();
            assert_eq!(
                counter.level_key_encodings, level_keys,
                "{} level work",
                scenario.id
            );
            assert_eq!(
                counter.term_key_encodings, term_keys,
                "{} term work",
                scenario.id
            );

            let legacy = structural_preflight(&decoded).and_then(|_| {
                validation_reuse_legacy_table_oracle_for_test(&decoded)?;
                validation_reuse_legacy_hash_oracle_for_test(&decoded)
            });
            assert_eq!(
                observed.as_ref().map(|_| ()),
                legacy.as_ref().map(|_| ()),
                "{} frozen legacy parity",
                scenario.id,
            );
        }
    }

    #[test]
    fn validation_reuse_release_benchmark_child_protocol() {
        let bytes = fixture(SCENARIOS[0]).unwrap();
        let mut row = child_json(
            SCENARIOS[0],
            0,
            &bytes,
            1,
            2,
            3,
            ValidationReuseWorkCounter::default(),
        );
        assert!(row.starts_with(&format!("{{\"schema\":\"{CHILD_SCHEMA}\"")));
        assert!(row.ends_with('}'));
        row.push('\n');
        let parsed = parse_child_row(&row, SCENARIOS[0], 0).unwrap();
        assert_eq!(parsed.validation_elapsed_ns, 1);
        assert_eq!(parsed.allocation_events, 2);
        assert_eq!(parsed.allocated_bytes, 3);

        let unknown = row.replacen(
            ",\"work_counters\":{",
            ",\"unknown\":0,\"work_counters\":{",
            1,
        );
        assert!(parse_child_row(&unknown, SCENARIOS[0], 0).is_err());
        let missing = row.replacen("\"allocated_bytes\":3,", "", 1);
        assert!(parse_child_row(&missing, SCENARIOS[0], 0).is_err());
        let trailing = format!("{}x", row);
        assert!(parse_child_row(&trailing, SCENARIOS[0], 0).is_err());
    }

    #[test]
    fn validation_reuse_release_benchmark_controller_protocol() {
        assert_eq!(
            parse_wrapper_tsv("1.000000000\t42\t0\n").unwrap(),
            ("1.000000000", 42, 0)
        );
        assert!(parse_wrapper_tsv("bad").is_err());
        assert!(parse_wrapper_tsv("NaN\t42\t0\n").is_err());
        assert!(parse_wrapper_tsv("1.00000000\t42\t0\n").is_err());
        let child = "{\"schema\":\"npa.certificate-validation-pass-reuse.child.v0.1\"}";
        let joined = append_process_fields(child, "1.000000000", 42, 0).unwrap();
        assert!(joined.contains("\"process_elapsed_seconds\":\"1.000000000\""));
        assert!(joined.contains("\"peak_rss_kib\":42"));
        assert_eq!(
            metric_summary(&[9, 1, 7, 3, 5, 11, 13, 15, 17]).unwrap(),
            "{\"raw\":[9,1,7,3,5,11,13,15,17],\"median\":9,\"mad\":4,\"min\":1,\"max\":17}"
        );
        let rustc_vv = decode_build_hex(env!("NPA_BUILD_RUSTC_VV_HEX")).unwrap();
        assert!(rustc_vv.ends_with('\n'));
        assert!(rustc_vv.lines().any(|line| line.starts_with("host: ")));
        assert!(!env!("NPA_BUILD_TARGET").is_empty());
        assert_eq!(env!("NPA_BUILD_CARGO_LOCK_SHA256").len(), 64);
        assert!(env!("NPA_BUILD_CARGO_LOCK_SHA256")
            .bytes()
            .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f')));
        assert_ne!(env!("NPA_BUILD_CARGO_LOCK_SHA256"), "0".repeat(64));
        assert_eq!(env!("NPA_BUILD_CVR_SOURCE_SET_SHA256").len(), 64);
        assert!(env!("NPA_BUILD_CVR_SOURCE_SET_PATHS").starts_with("Cargo.toml,"));
        assert!(env!("NPA_BUILD_CVR_SOURCE_SET_PATHS").contains("crates/npa-cert/src/producer.rs"));
        assert!(env!("NPA_BUILD_CVR_SOURCE_SET_PATHS").contains("crates/npa-kernel/src/work.rs"));
        assert_eq!(
            runtime_cvr_source_set_sha256().unwrap(),
            env!("NPA_BUILD_CVR_SOURCE_SET_SHA256")
        );
        assert!(
            env!("NPA_BUILD_SOURCE_IDENTITY") == "unbound"
                || valid_source_identity(env!("NPA_BUILD_SOURCE_IDENTITY"))
        );
        assert!(matches!(env!("NPA_BUILD_CARGO_PROFILE"), "dev" | "release"));
        let features = embedded_build_features_json();
        assert!(!features.contains("\"\""));
        assert!(features == "\"default\"" || features.is_empty());
        assert!(!features.contains('_'));
        assert!(decode_build_hex(env!("NPA_BUILD_RUSTFLAGS_HEX")).is_ok());
        assert!(decode_build_hex("0").is_err());
        assert!(decode_build_hex("gg").is_err());

        let executable = env::current_exe().unwrap();
        let wrapper = executable.clone();
        let mut rows = Vec::with_capacity(81);
        let mut observations = Vec::with_capacity(81);
        let fixtures = SCENARIOS
            .iter()
            .map(|scenario| fixture(*scenario).unwrap())
            .collect::<Vec<_>>();
        for sample_index in 0..9 {
            for (scenario, bytes) in SCENARIOS.into_iter().zip(&fixtures) {
                let child = format!(
                    "{}\n",
                    child_json(
                        scenario,
                        sample_index,
                        bytes,
                        u128::try_from(sample_index + 1).unwrap(),
                        u64::try_from(sample_index + 2).unwrap(),
                        u64::try_from(sample_index + 3).unwrap(),
                        ValidationReuseWorkCounter::default(),
                    )
                );
                let sample_u64 = u64::try_from(sample_index).unwrap();
                let row =
                    append_process_fields(&child, "1.000000000", 100 + sample_u64, 0).unwrap();
                observations.push(SummaryObservation {
                    scenario_id: scenario.id.to_owned(),
                    validation_elapsed_ns: u64::try_from(sample_index + 1).unwrap(),
                    allocation_events: u64::try_from(sample_index + 2).unwrap(),
                    allocated_bytes: u64::try_from(sample_index + 3).unwrap(),
                    process_peak_rss_kib: 100 + sample_u64,
                });
                rows.push(row);
            }
        }
        let summaries = SCENARIOS
            .iter()
            .map(|scenario| scenario_summary(*scenario, &observations).unwrap())
            .collect::<Vec<_>>()
            .join(",");
        let report = format!(
            "{}{}],\"summaries\":[{}]}}\n",
            run_report_prefix(&executable, &wrapper).unwrap(),
            rows.join(","),
            summaries,
        );
        validate_run_report(&report, &executable, &wrapper).unwrap();
        for invalid in [
            report.replacen("\"schema\":", "\"unknown\":0,\"schema\":", 1),
            report.replacen(env!("NPA_BUILD_CARGO_LOCK_SHA256"), &"0".repeat(64), 1),
            report.replacen(env!("NPA_BUILD_CVR_SOURCE_SET_SHA256"), &"0".repeat(64), 1),
            report.replacen(env!("NPA_BUILD_SOURCE_IDENTITY"), &"0".repeat(40), 1),
            report.replacen(SCENARIOS[0].input_sha256, &"0".repeat(64), 1),
            report.replacen("\"sample_index\":0", "\"sample_index\":1", 1),
            report.replacen("\"summaries\":[", "\"summaries\":[{}", 1),
            format!("{}x", report),
        ] {
            assert!(validate_run_report(&invalid, &executable, &wrapper).is_err());
        }

        let temporary = fs::canonicalize(env::temp_dir())
            .unwrap()
            .join(format!("npa-cvr-benchmark.{}", std::process::id()));
        let _ = fs::remove_dir_all(&temporary);
        fs::create_dir(&temporary).unwrap();
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&temporary, fs::Permissions::from_mode(0o700)).unwrap();
        }
        let work = ClosedPrivateDirectory::open_existing(&temporary, "npa-cvr-benchmark").unwrap();
        assert_eq!(
            work.catalog_root_paths().unwrap(),
            (BTreeSet::new(), BTreeSet::new())
        );
        assert!(validate_new_output_path(&temporary.join("report.json"), "test output").is_ok());
        assert!(validate_new_output_path(&temporary.join("-report.json"), "test output").is_err());
        fs::create_dir(temporary.join("nested")).unwrap();
        assert!(validate_new_output_path(
            &temporary.join("nested").join("..").join("report.json"),
            "test output",
        )
        .is_err());
        fs::remove_dir(temporary.join("nested")).unwrap();
        #[cfg(unix)]
        {
            fs::create_dir(temporary.join("real-parent")).unwrap();
            std::os::unix::fs::symlink(
                temporary.join("real-parent"),
                temporary.join("linked-parent"),
            )
            .unwrap();
            assert!(validate_new_output_path(
                &temporary.join("linked-parent").join("report.json"),
                "test output",
            )
            .is_err());
            std::os::unix::fs::symlink("missing", temporary.join("dangling.json")).unwrap();
            assert!(
                validate_new_output_path(&temporary.join("dangling.json"), "test output",).is_err()
            );
            fs::remove_file(temporary.join("dangling.json")).unwrap();
            fs::remove_file(temporary.join("linked-parent")).unwrap();
            fs::remove_dir(temporary.join("real-parent")).unwrap();
        }
        fs::write(temporary.join("collision"), b"occupied").unwrap();
        assert!(validate_new_output_path(&temporary.join("collision"), "test output").is_err());
        assert_ne!(
            work.catalog_root_paths().unwrap(),
            (BTreeSet::new(), BTreeSet::new())
        );
        assert!(validate_direct_work_file(
            &temporary,
            &temporary.join("expected.json"),
            "expected.json"
        )
        .is_ok());
        assert!(validate_direct_work_file(
            &temporary,
            &temporary.join("nested/expected.json"),
            "expected.json"
        )
        .is_err());
        #[cfg(unix)]
        {
            std::os::unix::fs::symlink(temporary.join("collision"), temporary.join("link"))
                .unwrap();
            assert!(work.read_regular_file(Path::new("link"), 1024).is_err());
        }
        fs::remove_dir_all(&temporary).unwrap();
    }

    #[test]
    #[ignore = "release-only isolated performance benchmark"]
    fn validation_reuse_release_benchmark() {
        let result = env::var("NPA_CVR_BENCH_MODE")
            .map_err(|_| "NPA_CVR_BENCH_MODE is required".to_owned())
            .and_then(|mode| match mode.as_str() {
                "child" => run_child(),
                "controller" => run_controller(),
                "validator" => run_validator(),
                _ => Err(format!("unknown benchmark mode {mode}")),
            });
        if let Err(error) = result {
            eprintln!(
                "certificate validation-reuse benchmark: {}",
                error.replace(['\n', '\r'], " ")
            );
            std::process::exit(2);
        }
    }
}

#[cfg(test)]
mod stack_safety_tests {
    use super::*;

    #[test]
    fn global_ref_collection_is_stack_safe_and_memoized() {
        std::thread::Builder::new()
            .stack_size(128 * 1024)
            .spawn(|| {
                let mut terms = vec![TermNode::Const {
                    global_ref: GlobalRef::Local { decl_index: 0 },
                    levels: vec![],
                }];
                for index in 0..MAX_STRUCTURAL_DEPTH - 1 {
                    terms.push(TermNode::App(index, index));
                }
                let mut refs = BTreeSet::new();
                collect_global_refs_from_term_table(&terms, terms.len() - 1, &mut refs).unwrap();
                assert_eq!(refs, BTreeSet::from([GlobalRef::Local { decl_index: 0 }]));
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn remap_bvars_preserves_preextended_mapping_under_binder() {
        let expr = Expr::lam("_", Expr::sort(Level::zero()), Expr::bvar(0));
        let remapped = remap_bvars(&expr, 1, 2, &[0, 1]).unwrap();

        assert_eq!(
            remapped,
            Expr::lam("_", Expr::sort(Level::zero()), Expr::bvar(1))
        );
    }
}

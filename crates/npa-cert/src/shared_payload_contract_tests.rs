//! Exact-name contract tests for the shared immutable payload implementation.

use std::collections::BTreeSet;

use npa_kernel::{Decl, Expr, KernelExecutionOptions, KernelWorkCounters, Level, Reducibility};

use crate::*;

fn fixture(module: &str) -> (ModuleCert, Vec<u8>) {
    let certificate = build_module_cert(
        CoreModule {
            name: Name::from_dotted(module),
            declarations: vec![Decl::Def {
                name: "value".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: Expr::pi(
                    "A",
                    Expr::sort(Level::param("u")),
                    Expr::pi("x", Expr::bvar(0), Expr::bvar(1)),
                ),
                value: Expr::lam(
                    "A",
                    Expr::sort(Level::param("u")),
                    Expr::lam("x", Expr::bvar(0), Expr::bvar(0)),
                ),
                reducibility: Reducibility::Reducible,
            }],
        },
        &[],
    )
    .unwrap();
    let bytes = encode_module_cert(&certificate).unwrap();
    (certificate, bytes)
}

fn verified_fixture(module: &str) -> (ModuleCert, Vec<u8>, VerifiedModule) {
    let (certificate, bytes) = fixture(module);
    let verified = verify_decoded_module_cert_with_import_refs(
        &certificate,
        &bytes,
        &[],
        &AxiomPolicy::normal(),
    )
    .unwrap();
    (certificate, bytes, verified)
}

fn assert_logical_accessors(certificate: &ModuleCert, parts: &ModuleCertParts) {
    assert_eq!(certificate.header(), &parts.header);
    assert_eq!(certificate.imports(), parts.imports);
    assert_eq!(certificate.name_table(), parts.name_table);
    assert_eq!(certificate.level_table(), parts.level_table);
    assert_eq!(certificate.term_table(), parts.term_table);
    assert_eq!(certificate.declarations(), parts.declarations);
    assert_eq!(certificate.export_block(), parts.export_block);
    assert_eq!(certificate.axiom_report(), &parts.axiom_report);
    assert_eq!(certificate.hashes(), &parts.hashes);
}

#[test]
fn payload_clone_oracle() {
    let (_, _, module) = verified_fixture("Contract.Clone");
    let module_clone = module.clone();
    assert_eq!(module_clone, module);
    assert_eq!(
        module_clone.logical_retained_bytes_v1(),
        module.logical_retained_bytes_v1()
    );

    let mut session = VerifierSession::new();
    session.register_verified_module(module);
    let snapshot = session.snapshot();
    assert_eq!(format!("{snapshot:?}"), format!("{session:?}"));
}

#[test]
fn shared_payload_value_oracle() {
    let (certificate, bytes) = fixture("Contract.Value");
    let decoded = decode_module_cert(&bytes).unwrap();
    assert_eq!(decoded, certificate);
    assert_eq!(encode_module_cert(&decoded).unwrap(), bytes);
    assert_eq!(decoded.hashes(), certificate.hashes());
}

#[test]
fn shared_payload_trust_oracle() {
    let (_, bytes, normal) = verified_fixture("Contract.Trust");
    let mut session = VerifierSession::new();
    let high_trust = verify_module_cert(&bytes, &mut session, &AxiomPolicy::high_trust()).unwrap();
    assert_eq!(normal, high_trust);
    assert_eq!(normal.certificate_hash(), high_trust.certificate_hash());
}

#[test]
fn shared_payload_import_error_oracle() {
    let (_, _, provider) = verified_fixture("Contract.Provider");
    let import = ImportEntry {
        module: provider.module().clone(),
        export_hash: provider.export_hash(),
        certificate_hash: Some([0xff; 32]),
    };
    let mut session = VerifierSession::new();
    session.register_verified_module_with_trust(provider, TrustMode::HighTrust);
    assert!(matches!(
        session.find_import(&import, TrustMode::HighTrust),
        Err(CertError::ImportCertificateHashMismatch { .. })
    ));
}

#[test]
fn golden_hashes() {
    let (certificate, bytes) = fixture("Contract.GoldenHashes");
    let decoded = verify_module_cert_hashes(&bytes).unwrap();
    assert_eq!(decoded.hashes(), certificate.hashes());
    assert_ne!(certificate.hashes().export_hash, [0; 32]);
    assert_ne!(certificate.hashes().certificate_hash, [0; 32]);
}

#[test]
fn module_cert_into_parts_unique() {
    let (certificate, _) = fixture("Contract.UniqueParts");
    let expected = certificate.clone().into_parts();
    let unique = ModuleCert::from_parts(expected.clone());
    let parts = unique.into_parts();
    assert_eq!(parts, expected);
}

#[test]
fn module_cert_parts_retained_charge_v1() {
    let (certificate, _) = fixture("Contract.PartsCharge");
    let parts = certificate.clone().into_parts();
    let expected_charge = crate::logical_charge::module_cert_logical_retained_bytes_v1(&parts);
    let refrozen = ModuleCert::from_parts(parts.clone());
    assert_logical_accessors(&refrozen, &parts);
    assert_eq!(refrozen.logical_retained_bytes_v1(), expected_charge);
    assert_eq!(refrozen, certificate);
}

#[test]
fn logical_retained_bytes_v1() {
    let (certificate, _) = fixture("Contract.LogicalCharge");
    let charge = certificate.logical_retained_bytes_v1();
    assert!(charge > 0);
    assert_eq!(certificate.clone().logical_retained_bytes_v1(), charge);
}

#[test]
fn retained_decoded_charge_landing_order() {
    let (certificate, _) = fixture("Contract.RetainedCharge");
    let charge = certificate.logical_retained_bytes_v1();
    let retained = RetainedDecodedModuleCert::from_decoded(certificate);
    assert_eq!(retained.logical_retained_bytes_v1(), charge);
    assert_eq!(
        retained.header().module.as_dotted(),
        "Contract.RetainedCharge"
    );
}

#[test]
fn retained_decoded_module_cert_header() {
    let (certificate, _) = fixture("Contract.RetainedHeader");
    let expected = certificate.header().clone();
    let retained = RetainedDecodedModuleCert::from_decoded(certificate);
    assert_eq!(retained.header(), &expected);
}

#[test]
fn retained_decoded_module_cert_hashes() {
    let (certificate, _) = fixture("Contract.RetainedHashes");
    let expected = certificate.hashes().clone();
    let retained = RetainedDecodedModuleCert::from_decoded(certificate);
    assert_eq!(retained.hashes(), &expected);
}

#[test]
fn retained_decoded_module_cert_axiom_report() {
    let (certificate, _) = fixture("Contract.RetainedAxioms");
    let expected = certificate.axiom_report().clone();
    let retained = RetainedDecodedModuleCert::from_decoded(certificate);
    assert_eq!(retained.axiom_report(), &expected);
}

#[test]
fn retained_certificate_measurement_summary() {
    let (certificate, _) = fixture("Contract.RetainedSummary");
    let retained = RetainedDecodedModuleCert::from_decoded(certificate);
    let summary = retained.measurement_summary(CertificateMeasurementDetail::Summary);
    let detailed = retained.measurement_summary(CertificateMeasurementDetail::Detailed);
    assert_eq!(summary.declaration_count, 1);
    assert!(summary.declarations.is_empty());
    assert_eq!(detailed.declaration_count, 1);
    assert_eq!(detailed.declarations.len(), 1);
    assert_eq!(detailed.declarations[0].declaration, "value");
}

#[test]
fn retained_decoded_module_cert_charge_accessor() {
    let (certificate, _) = fixture("Contract.RetainedAccessor");
    let expected = certificate.logical_retained_bytes_v1();
    let retained = RetainedDecodedModuleCert::from_decoded(certificate);
    assert_eq!(retained.logical_retained_bytes_v1(), expected);
    assert!(expected > 0);
}

#[test]
fn frozen_handle_api_contract() {
    fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<ModuleCert>();
    assert_send_sync::<VerifiedModule>();
    assert_send_sync::<VerifierSession>();

    let (certificate, _) = fixture("Contract.Frozen");
    let parts = certificate.clone().into_parts();
    assert_logical_accessors(&certificate, &parts);
}

#[test]
fn verified_module_charge_calculation_v1() {
    let (certificate, _, module) = verified_fixture("Contract.VerifiedCharge");
    assert!(module.logical_retained_bytes_v1() >= certificate.logical_retained_bytes_v1());
    assert_eq!(module.module(), &certificate.header().module);
}

#[test]
fn verify_decoded_module_cert() {
    let (certificate, bytes) = fixture("Contract.DecodedVerify");
    let direct = crate::verify_decoded_module_cert_with_import_refs(
        &certificate,
        &bytes,
        &[],
        &AxiomPolicy::normal(),
    )
    .unwrap();
    let mut session = VerifierSession::new();
    let registered = crate::verify_decoded_module_cert(
        &certificate,
        &bytes,
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap();
    assert_eq!(direct, registered);
}

#[test]
fn verified_module_retained_charge() {
    let (_, _, module) = verified_fixture("Contract.RetainedVerified");
    assert!(module.logical_retained_bytes_v1() > 0);
    assert_eq!(
        module.clone().logical_retained_bytes_v1(),
        module.logical_retained_bytes_v1()
    );
}

#[test]
fn public_handles_send_sync() {
    fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<ModuleCert>();
    assert_send_sync::<VerifiedModule>();
    assert_send_sync::<VerifierSession>();
    assert_send_sync::<RetainedDecodedModuleCert>();
}

#[test]
fn verifier_session_cow() {
    let (_, _, first) = verified_fixture("Contract.SessionFirst");
    let (_, _, second) = verified_fixture("Contract.SessionSecond");
    let mut session = VerifierSession::new();
    session.register_verified_module(first);
    let snapshot = session.snapshot();
    let mut observation = CertificatePayloadObservation::default();
    session.register_verified_module_with_trust_observed(
        second,
        TrustMode::Normal,
        Some(&mut observation),
    );
    assert_eq!(observation.session_index_cow_copies, 1);
    assert_eq!(observation.session_index_cow_entries, 1);
    assert_ne!(format!("{snapshot:?}"), format!("{session:?}"));
}

#[test]
fn certificate_payload_observation_updates() {
    let parts = fixture("Contract.ObservationUpdate").0.into_parts();
    let mut observation = CertificatePayloadObservation::default();
    let certificate = ModuleCert::from_parts_observed(parts, Some(&mut observation));
    assert_eq!(observation.payloads_frozen, 1);
    assert_eq!(
        observation.payload_unique_bytes,
        certificate.logical_retained_bytes_v1()
    );
    assert!(!observation.overflowed);
}

#[test]
fn raw_verifier_empty_observation_delegate() {
    let (_, bytes) = fixture("Contract.RawEmpty");
    let policy = AxiomPolicy::normal();
    let old = verify_module_cert_with_import_refs_and_kernel_options(
        &bytes,
        &[],
        &policy,
        KernelExecutionOptions::default(),
    )
    .unwrap();
    let sibling = verify_module_cert_with_import_refs_and_kernel_options_and_observations(
        &bytes,
        &[],
        &policy,
        KernelExecutionOptions::default(),
        CertificateVerificationObservationSinks::new(),
    )
    .unwrap();
    assert_eq!(old, sibling);
}

#[test]
fn raw_verifier_kernel_observation_delegate() {
    let (_, bytes) = fixture("Contract.RawKernel");
    let policy = AxiomPolicy::normal();
    let mut legacy = KernelWorkCounters::default();
    let old = verify_module_cert_with_import_refs_and_kernel_options_and_work_counters(
        &bytes,
        &[],
        &policy,
        KernelExecutionOptions::default(),
        &mut legacy,
    )
    .unwrap();
    let mut bundled = KernelWorkCounters::default();
    let sibling = verify_module_cert_with_import_refs_and_kernel_options_and_observations(
        &bytes,
        &[],
        &policy,
        KernelExecutionOptions::default(),
        CertificateVerificationObservationSinks::new().with_kernel(&mut bundled),
    )
    .unwrap();
    assert_eq!(old, sibling);
    assert_eq!(legacy, bundled);
}

#[test]
fn raw_verifier_observation_sinks() {
    raw_verifier_empty_observation_delegate();
    raw_verifier_kernel_observation_delegate();
    raw_verifier_payload_observation();
}

#[test]
fn raw_verifier_payload_observation() {
    let (certificate, bytes) = fixture("Contract.RawPayload");
    let decoded_charge = decode_module_cert(&bytes)
        .unwrap()
        .logical_retained_bytes_v1();
    let mut payload = CertificatePayloadObservation::default();
    let verified = verify_module_cert_with_import_refs_and_kernel_options_and_observations(
        &bytes,
        &[],
        &AxiomPolicy::normal(),
        KernelExecutionOptions::default(),
        CertificateVerificationObservationSinks::new().with_payload(&mut payload),
    )
    .unwrap();
    assert_eq!(payload.payloads_frozen, 1);
    assert_eq!(payload.payload_unique_bytes, decoded_charge);
    assert_eq!(verified.module(), &certificate.header().module);
}

#[test]
fn decoded_verifier_observation_sinks() {
    let (certificate, bytes) = fixture("Contract.DecodedSinks");
    let mut payload = CertificatePayloadObservation::default();
    let mut kernel = KernelWorkCounters::default();
    let observed = verify_decoded_module_cert_with_import_refs_and_kernel_options_and_observations(
        &certificate,
        &bytes,
        &[],
        &AxiomPolicy::normal(),
        KernelExecutionOptions::default(),
        CertificateVerificationObservationSinks::new()
            .with_kernel(&mut kernel)
            .with_payload(&mut payload),
    )
    .unwrap();
    assert_eq!(observed.module(), &certificate.header().module);
    assert_eq!(payload, CertificatePayloadObservation::default());
    assert!(kernel.check_calls > 0);
}

#[test]
fn decoded_verifier_observation_delegates() {
    let (certificate, bytes) = fixture("Contract.DecodedDelegates");
    let policy = AxiomPolicy::normal();
    let old = verify_decoded_module_cert_with_import_refs_and_kernel_options(
        &certificate,
        &bytes,
        &[],
        &policy,
        KernelExecutionOptions::default(),
    )
    .unwrap();
    let sibling = verify_decoded_module_cert_with_import_refs_and_kernel_options_and_observations(
        &certificate,
        &bytes,
        &[],
        &policy,
        KernelExecutionOptions::default(),
        CertificateVerificationObservationSinks::new(),
    )
    .unwrap();
    assert_eq!(old, sibling);
}

#[test]
fn verify_retained_decoded_module_cert_with_import_refs() {
    let (certificate, bytes) = fixture("Contract.RetainedRefs");
    let direct = crate::verify_decoded_module_cert_with_import_refs(
        &certificate,
        &bytes,
        &[],
        &AxiomPolicy::normal(),
    )
    .unwrap();
    let retained = RetainedDecodedModuleCert::from_decoded(certificate);
    let opaque = crate::verify_retained_decoded_module_cert_with_import_refs(
        &retained,
        &bytes,
        &[],
        &AxiomPolicy::normal(),
    )
    .unwrap();
    assert_eq!(direct, opaque);
}

#[test]
fn retained_decoded_options() {
    let (certificate, bytes) = fixture("Contract.RetainedOptions");
    let retained = RetainedDecodedModuleCert::from_decoded(certificate);
    let default = crate::verify_retained_decoded_module_cert_with_import_refs(
        &retained,
        &bytes,
        &[],
        &AxiomPolicy::normal(),
    )
    .unwrap();
    let options = crate::verify_retained_decoded_module_cert_with_import_refs_and_kernel_options(
        &retained,
        &bytes,
        &[],
        &AxiomPolicy::normal(),
        KernelExecutionOptions::default(),
    )
    .unwrap();
    assert_eq!(default, options);
}

#[test]
fn retained_decoded_observed() {
    let (certificate, bytes) = fixture("Contract.RetainedObserved");
    let retained = RetainedDecodedModuleCert::from_decoded(certificate);
    let mut payload = CertificatePayloadObservation::default();
    let mut kernel = KernelWorkCounters::default();
    let verified =
        crate::verify_retained_decoded_module_cert_with_import_refs_and_kernel_options_and_observations(
            &retained,
            &bytes,
            &[],
            &AxiomPolicy::normal(),
            KernelExecutionOptions::default(),
            CertificateVerificationObservationSinks::new()
                .with_kernel(&mut kernel)
                .with_payload(&mut payload),
        )
        .unwrap();
    assert_eq!(verified.module(), &retained.header().module);
    assert_eq!(payload, CertificatePayloadObservation::default());
    assert!(kernel.check_calls > 0);
}

#[test]
fn retained_decoded_session() {
    let (certificate, bytes) = fixture("Contract.RetainedSession");
    let retained = RetainedDecodedModuleCert::from_decoded(certificate);
    let mut session = VerifierSession::new();
    let verified = crate::verify_retained_decoded_module_cert(
        &retained,
        &bytes,
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap();
    let import = ImportEntry {
        module: verified.module().clone(),
        export_hash: verified.export_hash(),
        certificate_hash: None,
    };
    assert_eq!(
        session.find_import(&import, TrustMode::Normal).unwrap(),
        &verified
    );
}

#[test]
fn built_verifier_observation_sinks() {
    let (certificate, _) = fixture("Contract.BuiltSinks");
    let mut payload = CertificatePayloadObservation::default();
    let mut kernel = KernelWorkCounters::default();
    let old = verify_built_module_cert_with_import_refs_and_kernel_options(
        &certificate,
        &[],
        &AxiomPolicy::normal(),
        KernelExecutionOptions::default(),
    )
    .unwrap();
    let observed = verify_built_module_cert_with_import_refs_and_kernel_options_and_observations(
        &certificate,
        &[],
        &AxiomPolicy::normal(),
        KernelExecutionOptions::default(),
        CertificateVerificationObservationSinks::new()
            .with_kernel(&mut kernel)
            .with_payload(&mut payload),
    )
    .unwrap();
    assert_eq!(old, observed);
    assert_eq!(payload, CertificatePayloadObservation::default());
    assert!(kernel.check_calls > 0);
}

#[test]
fn verifier_session_snapshot_observed() {
    let mut observation = CertificatePayloadObservation::default();
    let session = VerifierSession::new();
    let snapshot = session.snapshot_observed(Some(&mut observation));
    assert_eq!(format!("{snapshot:?}"), format!("{session:?}"));
    assert_eq!(observation.session_snapshot_clones, 1);
    assert_eq!(observation.session_index_cow_copies, 0);
}

#[test]
fn verifier_session_registration_observed() {
    let (_, _, module) = verified_fixture("Contract.SessionRegistration");
    let mut session = VerifierSession::new();
    let _snapshot = session.snapshot();
    let mut observation = CertificatePayloadObservation::default();
    session.register_verified_module_with_trust_observed(
        module,
        TrustMode::Normal,
        Some(&mut observation),
    );
    assert_eq!(observation.session_index_cow_copies, 1);
    assert_eq!(observation.session_index_cow_entries, 0);
}

#[test]
fn shared_payload_differential() {
    let (certificate, bytes) = fixture("Contract.Differential");
    let raw = verify_module_cert_with_import_refs(&bytes, &[], &AxiomPolicy::normal()).unwrap();
    let decoded = verify_decoded_module_cert_with_import_refs(
        &certificate,
        &bytes,
        &[],
        &AxiomPolicy::normal(),
    )
    .unwrap();
    let built =
        verify_built_module_cert_with_import_refs(&certificate, &[], &AxiomPolicy::normal())
            .unwrap();
    assert_eq!(raw, decoded);
    assert_eq!(decoded, built);
    assert_eq!(encode_module_cert(&certificate).unwrap(), bytes);
    assert_eq!(raw.axiom_report().module_axioms, Vec::new());
    assert_eq!(raw.axiom_report().core_features, Vec::new());
    assert_eq!(AxiomPolicy::normal().allowlisted_axioms, BTreeSet::new());
}

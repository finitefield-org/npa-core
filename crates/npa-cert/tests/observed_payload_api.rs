use std::collections::BTreeMap;

use npa_cert::{
    build_module_cert, build_module_cert_from_import_refs,
    build_module_cert_from_import_refs_observed,
    build_module_cert_from_import_refs_with_preferred_imports,
    build_module_cert_from_import_refs_with_preferred_imports_observed, build_module_cert_observed,
    decode_module_cert, decode_module_cert_observed, decode_module_cert_with_import_offsets,
    decode_module_cert_with_import_offsets_observed, encode_module_cert, verify_module_cert,
    AxiomPolicy, CertificatePayloadObservation, CoreModule, ImportEntry, ModuleCert, Name,
    VerifiedModule, VerifierSession,
};
use npa_kernel::{Decl, Expr, Level};

fn module(name: &str) -> CoreModule {
    CoreModule {
        name: Name::from_dotted(name),
        declarations: vec![Decl::Axiom {
            name: format!("{name}.T"),
            universe_params: Vec::new(),
            ty: Expr::sort(Level::zero()),
        }],
    }
}

fn invalid_module(name: &str) -> CoreModule {
    let duplicate = format!("{name}.T");
    CoreModule {
        name: Name::from_dotted(name),
        declarations: vec![
            Decl::Axiom {
                name: duplicate.clone(),
                universe_params: Vec::new(),
                ty: Expr::sort(Level::zero()),
            },
            Decl::Axiom {
                name: duplicate,
                universe_params: Vec::new(),
                ty: Expr::sort(Level::zero()),
            },
        ],
    }
}

fn assert_one_freeze(observation: CertificatePayloadObservation, certificate: &ModuleCert) {
    assert_eq!(observation.payloads_frozen, 1);
    assert_eq!(
        observation.payload_unique_bytes,
        certificate.logical_retained_bytes_v1()
    );
    assert_eq!(observation.session_snapshot_clones, 0);
    assert_eq!(observation.session_index_cow_copies, 0);
    assert_eq!(observation.session_index_cow_entries, 0);
    assert!(!observation.overflowed);
}

fn assert_same_bytes(left: &ModuleCert, right: &ModuleCert) {
    assert_eq!(
        encode_module_cert(left).unwrap(),
        encode_module_cert(right).unwrap()
    );
}

#[test]
fn observed_module_cert_from_parts() {
    let ordinary = build_module_cert(module("Observed.FromParts"), &[]).unwrap();
    let parts = ordinary.clone().into_parts();
    let mut observation = CertificatePayloadObservation::default();
    let observed = ModuleCert::from_parts_observed(parts, Some(&mut observation));

    assert_same_bytes(&ordinary, &observed);
    assert_one_freeze(observation, &observed);
}

#[test]
fn observed_decode_module_cert() {
    let certificate = build_module_cert(module("Observed.Decode"), &[]).unwrap();
    let bytes = encode_module_cert(&certificate).unwrap();
    let ordinary = decode_module_cert(&bytes).unwrap();
    let mut observation = CertificatePayloadObservation::default();
    let observed = decode_module_cert_observed(&bytes, Some(&mut observation)).unwrap();

    assert_eq!(ordinary, observed);
    assert_one_freeze(observation, &observed);

    let mut malformed = bytes;
    malformed.push(0);
    let mut retained = CertificatePayloadObservation {
        payloads_frozen: 7,
        ..CertificatePayloadObservation::default()
    };
    assert_eq!(
        decode_module_cert(&malformed).unwrap_err(),
        decode_module_cert_observed(&malformed, Some(&mut retained)).unwrap_err()
    );
    assert_eq!(retained.payloads_frozen, 7);
}

#[test]
fn observed_decode_module_cert_with_import_offsets() {
    let provider_certificate = build_module_cert(module("Observed.OffsetProvider"), &[]).unwrap();
    let provider_bytes = encode_module_cert(&provider_certificate).unwrap();
    let provider = verify_module_cert(
        &provider_bytes,
        &mut VerifierSession::new(),
        &AxiomPolicy::normal(),
    )
    .unwrap();
    let certificate = build_module_cert(
        CoreModule {
            name: Name::from_dotted("Observed.OffsetDecode"),
            declarations: vec![Decl::Axiom {
                name: "Observed.OffsetDecode.Value".to_owned(),
                universe_params: Vec::new(),
                ty: Expr::konst("Observed.OffsetProvider.T", Vec::new()),
            }],
        },
        &[provider],
    )
    .unwrap();
    let bytes = encode_module_cert(&certificate).unwrap();
    let ordinary = decode_module_cert_with_import_offsets(&bytes).unwrap();
    let mut observation = CertificatePayloadObservation::default();
    let observed =
        decode_module_cert_with_import_offsets_observed(&bytes, Some(&mut observation)).unwrap();

    assert_eq!(ordinary, observed);
    assert_eq!(observed.1.len(), 1);
    assert_one_freeze(observation, &observed.0);

    let mut malformed = bytes;
    malformed.push(0);
    let before = CertificatePayloadObservation {
        payload_unique_bytes: 11,
        ..CertificatePayloadObservation::default()
    };
    let mut retained = before;
    assert_eq!(
        decode_module_cert_with_import_offsets(&malformed).unwrap_err(),
        decode_module_cert_with_import_offsets_observed(&malformed, Some(&mut retained))
            .unwrap_err()
    );
    assert_eq!(retained, before);
}

#[test]
fn observed_build_module_cert() {
    let ordinary = build_module_cert(module("Observed.Build"), &[]).unwrap();
    let mut observation = CertificatePayloadObservation::default();
    let observed =
        build_module_cert_observed(module("Observed.Build"), &[], Some(&mut observation)).unwrap();

    assert_same_bytes(&ordinary, &observed);
    assert_one_freeze(observation, &observed);
}

#[test]
fn observed_build_module_cert_from_import_refs() {
    let imports: [&VerifiedModule; 0] = [];
    let ordinary = build_module_cert_from_import_refs(module("Observed.Refs"), &imports).unwrap();
    let mut observation = CertificatePayloadObservation::default();
    let observed = build_module_cert_from_import_refs_observed(
        module("Observed.Refs"),
        &imports,
        Some(&mut observation),
    )
    .unwrap();

    assert_same_bytes(&ordinary, &observed);
    assert_one_freeze(observation, &observed);
}

#[test]
fn observed_build_module_cert_with_preferred_imports() {
    let imports: [&VerifiedModule; 0] = [];
    let preferred = BTreeMap::<Name, ImportEntry>::new();
    let ordinary = build_module_cert_from_import_refs_with_preferred_imports(
        module("Observed.Preferred"),
        &imports,
        &preferred,
    )
    .unwrap();
    let mut observation = CertificatePayloadObservation::default();
    let observed = build_module_cert_from_import_refs_with_preferred_imports_observed(
        module("Observed.Preferred"),
        &imports,
        &preferred,
        Some(&mut observation),
    )
    .unwrap();

    assert_same_bytes(&ordinary, &observed);
    assert_one_freeze(observation, &observed);
}

#[test]
fn observed_build_errors_are_exact_and_leave_observation_unchanged() {
    let imports: [&VerifiedModule; 0] = [];
    let preferred = BTreeMap::<Name, ImportEntry>::new();
    let before = CertificatePayloadObservation {
        payloads_frozen: 7,
        payload_unique_bytes: 11,
        session_snapshot_clones: 13,
        session_index_cow_copies: 17,
        session_index_cow_entries: 19,
        overflowed: true,
    };

    let mut observed = before;
    assert_eq!(
        build_module_cert(invalid_module("Observed.Invalid.Owned"), &[]).unwrap_err(),
        build_module_cert_observed(
            invalid_module("Observed.Invalid.Owned"),
            &[],
            Some(&mut observed),
        )
        .unwrap_err()
    );
    assert_eq!(observed, before);

    let mut observed = before;
    assert_eq!(
        build_module_cert_from_import_refs(invalid_module("Observed.Invalid.Refs"), &imports)
            .unwrap_err(),
        build_module_cert_from_import_refs_observed(
            invalid_module("Observed.Invalid.Refs"),
            &imports,
            Some(&mut observed),
        )
        .unwrap_err()
    );
    assert_eq!(observed, before);

    let mut observed = before;
    assert_eq!(
        build_module_cert_from_import_refs_with_preferred_imports(
            invalid_module("Observed.Invalid.Preferred"),
            &imports,
            &preferred,
        )
        .unwrap_err(),
        build_module_cert_from_import_refs_with_preferred_imports_observed(
            invalid_module("Observed.Invalid.Preferred"),
            &imports,
            &preferred,
            Some(&mut observed),
        )
        .unwrap_err()
    );
    assert_eq!(observed, before);
}

use super::*;
use npa_kernel::{
    eq, eq_inductive, eq_rec_type, eq_refl, eq_refl_type, nat, nat_inductive, nat_succ, nat_zero,
    prop, type0, Binder, ConstructorDecl, Ctx, Decl, Env, Expr, InductiveDecl,
    KernelExecutionOptions, KernelWorkCounterSink, KernelWorkCounters, Level, MutualInductiveBlock,
    RecursorDecl, Reducibility, ResourceLimitKind, UniverseConstraint,
};
use std::collections::{BTreeMap, BTreeSet};
use std::process::Command;

const V0_4_FIXTURE_MATRIX: &str =
    include_str!("../../../testdata/certificate-v0.4/fixture-matrix.tsv");

fn v0_4_fixture_matrix_rows() -> Vec<Vec<&'static str>> {
    V0_4_FIXTURE_MATRIX
        .lines()
        .skip(1)
        .map(|line| {
            let fields = line.split('\t').collect::<Vec<_>>();
            assert_eq!(fields.len(), 10, "malformed fixture matrix row: {line}");
            fields
        })
        .collect()
}

fn v0_4_fixture_rows(class: &str) -> Vec<Vec<&'static str>> {
    v0_4_fixture_matrix_rows()
        .into_iter()
        .filter(|fields| fields[1] == class)
        .collect()
}

fn encode_module_cert_without_certificate_hash(cert: &ModuleCert) -> Vec<u8> {
    encode_module_cert_without_certificate_hash_for_header(cert).unwrap()
}

fn interface_dependency(global_ref: GlobalRef, decl_interface_hash: Hash) -> DependencyEntry {
    DependencyEntry::checked_interface(global_ref, decl_interface_hash).unwrap()
}

fn id_type(a: &str, x: &str) -> Expr {
    Expr::pi(
        a,
        Expr::sort(Level::param("u")),
        Expr::pi(x, Expr::bvar(0), Expr::bvar(1)),
    )
}

fn id_value(a: &str, x: &str) -> Expr {
    Expr::lam(
        a,
        Expr::sort(Level::param("u")),
        Expr::lam(x, Expr::bvar(0), Expr::bvar(0)),
    )
}

fn const_type() -> Expr {
    let u = Level::param("u");
    let v = Level::param("v");
    Expr::pi(
        "A",
        Expr::sort(u),
        Expr::pi(
            "B",
            Expr::sort(v),
            Expr::pi(
                "x",
                Expr::bvar(1),
                Expr::pi("y", Expr::bvar(1), Expr::bvar(3)),
            ),
        ),
    )
}

fn const_value() -> Expr {
    let u = Level::param("u");
    let v = Level::param("v");
    Expr::lam(
        "A",
        Expr::sort(u),
        Expr::lam(
            "B",
            Expr::sort(v),
            Expr::lam(
                "x",
                Expr::bvar(1),
                Expr::lam("y", Expr::bvar(1), Expr::bvar(1)),
            ),
        ),
    )
}

fn id_value_with_beta_redex() -> Expr {
    Expr::lam(
        "A",
        Expr::sort(Level::param("u")),
        Expr::lam(
            "x",
            Expr::bvar(0),
            Expr::app(Expr::lam("y", Expr::bvar(1), Expr::bvar(0)), Expr::bvar(0)),
        ),
    )
}

fn id_module(a: &str, x: &str) -> CoreModule {
    id_def_module_with_value(id_value(a, x))
}

#[test]
fn canonical_level_key_goldens() {
    let child_a = [0x11; 32];
    let child_b = [0x22; 32];
    let names = vec![Name::from_dotted("u")];
    let cases = vec![
        (LevelNode::Zero, vec![0x00]),
        (LevelNode::Succ(0), [vec![0x01], child_a.to_vec()].concat()),
        (
            LevelNode::Max(0, 1),
            [vec![0x02], child_a.to_vec(), child_b.to_vec()].concat(),
        ),
        (
            LevelNode::IMax(1, 0),
            [vec![0x03], child_b.to_vec(), child_a.to_vec()].concat(),
        ),
        (LevelNode::Param(0), vec![0x04, 0x01, 0x01, b'u']),
    ];
    for (node, expected) in cases {
        let mut emitted = Vec::new();
        encode_level_node_key_to(&mut emitted, &node, &[child_a, child_b], &names).unwrap();
        assert_eq!(emitted, expected);
        assert_eq!(
            level_node_key(&node, &[child_a, child_b], &names).unwrap(),
            expected
        );
    }
}

#[test]
fn canonical_term_key_goldens() {
    let child_a = [0x11; 32];
    let child_b = [0x22; 32];
    let child_c = [0x33; 32];
    let level_a = [0x44; 32];
    let level_b = [0x55; 32];
    let local = GlobalRef::Local { decl_index: 7 };
    let cases = vec![
        (TermNode::Sort(1), [vec![0x00], level_b.to_vec()].concat()),
        (TermNode::BVar(128), vec![0x01, 0x80, 0x01]),
        (
            TermNode::Const {
                global_ref: local,
                levels: vec![0, 1],
            },
            [
                vec![0x02, 0x01, 0x07, 0x02],
                level_a.to_vec(),
                level_b.to_vec(),
            ]
            .concat(),
        ),
        (
            TermNode::App(0, 1),
            [vec![0x03], child_a.to_vec(), child_b.to_vec()].concat(),
        ),
        (
            TermNode::Lam { ty: 1, body: 2 },
            [vec![0x04], child_b.to_vec(), child_c.to_vec()].concat(),
        ),
        (
            TermNode::Pi { ty: 2, body: 0 },
            [vec![0x05], child_c.to_vec(), child_a.to_vec()].concat(),
        ),
    ];
    for (node, expected) in cases {
        let mut emitted = Vec::new();
        encode_term_node_key_to(
            &mut emitted,
            &node,
            &[child_a, child_b, child_c],
            &[level_a, level_b],
        )
        .unwrap();
        assert_eq!(emitted, expected);
        assert_eq!(
            term_node_key(&node, &[child_a, child_b, child_c], &[level_a, level_b]).unwrap(),
            expected
        );
    }
}

fn assert_canonical_hash_boundary(cert: &ModuleCert) {
    let encoding = encode_module_cert_full_with_boundary_for_header(cert).unwrap();
    assert_eq!(encoding.version, CertificateFormatVersion::V0_4_0);
    let expected_prefix = encode_module_cert_without_certificate_hash_for_header(cert).unwrap();
    assert_eq!(
        &encoding.bytes[..encoding.certificate_hash_input_end],
        expected_prefix
    );
    assert_eq!(
        &encoding.bytes[encoding.certificate_hash_input_end..],
        cert.hashes().certificate_hash
    );
}

#[test]
fn canonical_boundary_v0_4() {
    let cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    assert_canonical_hash_boundary(&cert);
}

#[test]
fn validation_reuse_byte_work_equation() {
    for cert in [
        build_module_cert(
            CoreModule {
                name: Name::from_dotted("Test.Cvr.Empty"),
                declarations: Vec::new(),
            },
            &[],
        )
        .unwrap(),
        build_module_cert(id_module("A", "x"), &[]).unwrap(),
    ] {
        let bytes = encode_module_cert(&cert).unwrap();
        let mut counter = ValidationReuseWorkCounter::default();
        let observed =
            verify_module_cert_hashes_impl_with_validation_reuse_counter(&bytes, &mut counter)
                .unwrap();
        assert_eq!(observed, cert);
        assert_eq!(counter.level_key_encodings, cert.level_table().len() as u64);
        assert_eq!(counter.term_key_encodings, cert.term_table().len() as u64);
        assert_eq!(counter.level_hash_passes, 1);
        assert_eq!(counter.term_hash_passes, 1);
        assert_eq!(counter.canonical_full_encodings, 1);
        assert_eq!(counter.authoritative_prefix_uses, 1);
        assert_eq!(counter.streamed_prehash_uses, 0);
        assert_eq!(counter.lazy_built_materializations, 0);
        assert!(counter.canonical_encoding_allocated_bytes >= bytes.len() as u64);
    }
}

#[test]
fn validation_reuse_built_work_equation() {
    for cert in [
        build_module_cert(
            CoreModule {
                name: Name::from_dotted("Test.Cvr.Empty"),
                declarations: Vec::new(),
            },
            &[],
        )
        .unwrap(),
        build_module_cert(id_module("A", "x"), &[]).unwrap(),
    ] {
        let mut counter = ValidationReuseWorkCounter::default();
        verify_built_module_cert_hashes_impl_with_validation_reuse_counter(&cert, &mut counter)
            .unwrap();
        assert_eq!(counter.level_key_encodings, cert.level_table().len() as u64);
        assert_eq!(counter.term_key_encodings, cert.term_table().len() as u64);
        assert_eq!(counter.level_hash_passes, 1);
        assert_eq!(counter.term_hash_passes, 1);
        assert_eq!(counter.canonical_full_encodings, 0);
        assert_eq!(counter.authoritative_prefix_uses, 0);
        assert_eq!(counter.streamed_prehash_uses, 0);
        assert_eq!(counter.lazy_built_materializations, 1);
    }
}

#[test]
fn validation_reuse_complete_table_differential() {
    let cert = build_module_cert(const_module(), &[]).unwrap();
    let expected_levels = compute_level_hashes(cert.level_table(), cert.name_table()).unwrap();
    let expected_terms = compute_term_hashes(cert.term_table(), &expected_levels).unwrap();
    let (level_hashes, term_hashes) = validation_reuse_verify_tables_for_test(&cert).unwrap();
    assert_eq!(level_hashes, expected_levels);
    assert_eq!(term_hashes, expected_terms);
}

#[test]
fn validation_reuse_legacy_table_oracle() {
    for bytes in validation_reuse_format_fixture_bytes() {
        let cert = decode_module_cert(&bytes).unwrap();
        assert_eq!(
            validation_reuse_verify_tables_for_test(&cert),
            validation_reuse_legacy_table_oracle_for_test(&cert),
        );
    }

    let mut malformed = build_module_cert(id_module("A", "x"), &[]).unwrap();
    malformed.mutate_parts_for_test(|parts| {
        parts.term_table[0] = TermNode::App(0, 0);
    });
    assert_eq!(
        validation_reuse_verify_tables_for_test(&malformed),
        validation_reuse_legacy_table_oracle_for_test(&malformed),
    );
    assert!(matches!(
        validation_reuse_legacy_table_oracle_for_test(&malformed),
        Err(CertError::NonCanonicalEncoding {
            object: "TermTable"
        })
    ));
}

#[test]
fn validation_reuse_legacy_hash_oracle() {
    for bytes in validation_reuse_format_fixture_bytes() {
        let cert = decode_module_cert(&bytes).unwrap();
        let mut counter = ValidationReuseWorkCounter::default();
        assert_eq!(
            verify_built_module_cert_hashes_impl_with_validation_reuse_counter(&cert, &mut counter,),
            validation_reuse_legacy_hash_oracle_for_test(&cert),
        );

        let mut malformed = cert.clone();
        malformed.mutate_parts_for_test(|parts| {
            parts.hashes.certificate_hash[0] ^= 1;
        });
        let mut counter = ValidationReuseWorkCounter::default();
        assert_eq!(
            verify_built_module_cert_hashes_impl_with_validation_reuse_counter(
                &malformed,
                &mut counter,
            ),
            validation_reuse_legacy_hash_oracle_for_test(&malformed),
        );
        assert!(matches!(
            validation_reuse_legacy_hash_oracle_for_test(&malformed),
            Err(CertError::HashMismatch {
                object: HashObject::ModuleCertificate,
                ..
            })
        ));
    }
}

#[test]
fn validation_reuse_late_hash_error_keeps_payload_and_work_order() {
    let mut cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    cert.mutate_parts_for_test(|parts| parts.hashes.certificate_hash[0] ^= 0x01);
    let bytes = encode_module_cert(&cert).unwrap();
    let mut counter = ValidationReuseWorkCounter::default();
    let error = verify_module_cert_hashes_impl_with_validation_reuse_counter(&bytes, &mut counter)
        .unwrap_err();
    assert!(matches!(
        error,
        CertError::HashMismatch {
            object: HashObject::ModuleCertificate,
            expected,
            actual,
        } if expected == cert.hashes().certificate_hash && expected != actual
    ));
    assert_eq!(counter.canonical_full_encodings, 1);
    assert_eq!(counter.authoritative_prefix_uses, 1);
    assert_eq!(counter.lazy_built_materializations, 0);
}

#[test]
fn validation_reuse_late_hash_mutation_reaches_module_hash_stage() {
    let cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let mut bytes = encode_module_cert(&cert).unwrap();
    let prefix_end = bytes.len() - 32;
    bytes[prefix_end] ^= 0x01;
    let mutated = decode_module_cert(&bytes).unwrap();
    assert_eq!(encode_module_cert(&mutated).unwrap(), bytes);
    let error = verify_module_certificate_hash_from_input_prefix_for_test(
        &mutated,
        CertificateFormatVersion::V0_4_0,
        &bytes[..prefix_end],
    )
    .unwrap_err();
    assert!(matches!(
        error,
        CertError::HashMismatch {
            object: HashObject::ModuleCertificate,
            expected,
            actual,
        } if expected == mutated.hashes().certificate_hash && expected != actual
    ));
}

#[test]
fn validation_reuse_scoped_allocation_meter() {
    use crate::validation_reuse_allocation_meter::{
        reset_and_start, set_for_saturation_test, stop, Snapshot,
    };

    let inactive = vec![0_u8; 32];
    std::hint::black_box(inactive);
    reset_and_start();
    let mut measured = Vec::with_capacity(16);
    measured.resize(64, 1_u8);
    std::hint::black_box(&measured);
    let snapshot = stop();
    assert!(snapshot.allocation_events >= 1);
    assert!(snapshot.allocated_bytes >= 16);

    let unchanged = vec![0_u8; 128];
    std::hint::black_box(unchanged);
    assert_eq!(stop(), snapshot);

    let other = std::thread::spawn(|| {
        reset_and_start();
        let value = vec![0_u8; 8];
        std::hint::black_box(value);
        stop()
    })
    .join()
    .unwrap();
    assert!(other.allocation_events >= 1);
    assert_eq!(stop(), snapshot);

    set_for_saturation_test(Snapshot {
        allocation_events: u64::MAX,
        allocated_bytes: u64::MAX,
    });
    let saturated = vec![0_u8; 8];
    std::hint::black_box(saturated);
    assert_eq!(
        stop(),
        Snapshot {
            allocation_events: u64::MAX,
            allocated_bytes: u64::MAX,
        }
    );
}

fn validation_reuse_format_fixture_bytes() -> Vec<Vec<u8>> {
    let current = build_module_cert(id_module("A", "x"), &[]).unwrap();
    vec![encode_module_cert(&current).unwrap()]
}

#[test]
fn validation_reuse_format_goldens() {
    let actual = validation_reuse_format_fixture_bytes()
        .into_iter()
        .map(|bytes| {
            let cert = decode_module_cert(&bytes).unwrap();
            let full = encode_module_cert_full_with_boundary_for_header(&cert).unwrap();
            (
                cert.header().format.clone(),
                bytes.len(),
                full.certificate_hash_input_end,
                hash_hex(hash_with_domain(b"", &bytes)),
                hash_hex(hash_with_domain(
                    b"",
                    &bytes[..full.certificate_hash_input_end],
                )),
                hash_hex(cert.hashes().export_hash),
                hash_hex(cert.hashes().axiom_report_hash),
                hash_hex(cert.hashes().certificate_hash),
            )
        })
        .collect::<Vec<_>>();
    let expected = vec![(
        FORMAT.to_owned(),
        364,
        332,
        "c06e7ea9ecde9a349a04f9c66e96ee7c7b2bdff1b65a7d2293709f9d46740054".to_owned(),
        "2359528c4b045bc2f97b36c61eb61b9732d4f73a5e562ee88ffa3456f5b74430".to_owned(),
        "495c350b0f738421ad48ef76bd2b5c21ee1b34eeab717086b416d6868aa124e8".to_owned(),
        "a1ef77782ab68d41aede3e412c79174432934c3cac66c319dd2d406cf514f40e".to_owned(),
        "150843ddf2724fb226b81079d0168d2fcc633419a99aa78ef30945b0826ed08b".to_owned(),
    )];
    assert_eq!(actual, expected);
}

#[test]
fn level_key_sink_differential() {
    let cert = build_module_cert(const_module(), &[]).unwrap();
    let mut child_hashes = Vec::new();
    for level in cert.level_table() {
        let expected = level_node_key(level, &child_hashes, cert.name_table());
        let mut emitted = Vec::new();
        let actual =
            match encode_level_node_key_to(&mut emitted, level, &child_hashes, cert.name_table()) {
                Ok(()) => Ok(emitted),
                Err(error) => Err(error),
            };
        assert_eq!(actual, expected);
        child_hashes.push(hash_with_domain(b"NPA-LEVEL-0.1", &actual.unwrap()));
    }

    let invalid = LevelNode::Param(usize::MAX);
    let expected = level_node_key(&invalid, &child_hashes, cert.name_table());
    let mut emitted = Vec::new();
    let actual = encode_level_node_key_to(&mut emitted, &invalid, &child_hashes, cert.name_table())
        .map(|()| emitted);
    assert_eq!(actual, expected);
}

#[test]
fn term_key_sink_differential() {
    let child_hashes = [[0x11; 32], [0x22; 32], [0x33; 32]];
    let level_hashes = [[0x44; 32], [0x55; 32], [0x66; 32]];
    let nodes = [
        TermNode::Sort(0),
        TermNode::BVar(7),
        TermNode::Const {
            global_ref: GlobalRef::Local { decl_index: 3 },
            levels: vec![0, 1, 2],
        },
        TermNode::App(0, 1),
        TermNode::Lam { ty: 0, body: 1 },
        TermNode::Pi { ty: 1, body: 2 },
    ];
    for term in nodes {
        let expected = term_node_key(&term, &child_hashes, &level_hashes);
        let mut emitted = Vec::new();
        let actual = encode_term_node_key_to(&mut emitted, &term, &child_hashes, &level_hashes)
            .map(|()| emitted);
        assert_eq!(actual, expected);
    }

    let invalid = TermNode::Sort(usize::MAX);
    let expected = term_node_key(&invalid, &child_hashes, &level_hashes);
    let mut emitted = Vec::new();
    let actual = encode_term_node_key_to(&mut emitted, &invalid, &child_hashes, &level_hashes)
        .map(|()| emitted);
    assert_eq!(actual, expected);
}

#[test]
fn one_pass_level_table_processor() {
    let cert = build_module_cert(const_module(), &[]).unwrap();
    let expected = compute_level_hashes(cert.level_table(), cert.name_table()).unwrap();
    let mut counter = ValidationReuseWorkCounter::default();
    let (actual, _) =
        validation_reuse_verify_tables_with_counter_for_test(&cert, &mut counter).unwrap();
    assert_eq!(actual, expected);
    assert_eq!(counter.level_key_encodings, cert.level_table().len() as u64);
    assert_eq!(counter.level_hash_passes, 1);
}

#[test]
fn one_pass_term_table_processor() {
    let cert = build_module_cert(const_module(), &[]).unwrap();
    let levels = compute_level_hashes(cert.level_table(), cert.name_table()).unwrap();
    let expected = compute_term_hashes(cert.term_table(), &levels).unwrap();
    let mut counter = ValidationReuseWorkCounter::default();
    let (_, actual) =
        validation_reuse_verify_tables_with_counter_for_test(&cert, &mut counter).unwrap();
    assert_eq!(actual, expected);
    assert_eq!(counter.term_key_encodings, cert.term_table().len() as u64);
    assert_eq!(counter.term_hash_passes, 1);
}

#[test]
fn validation_reuse_level_normalization_order() {
    let mut non_normal = build_module_cert(
        CoreModule {
            name: Name::from_dotted("Test.CvrLevelOrder"),
            declarations: vec![Decl::Axiom {
                name: "Test.CvrLevelOrder.target".to_owned(),
                universe_params: Vec::new(),
                ty: Expr::sort(Level::succ(Level::zero())),
            }],
        },
        &[],
    )
    .unwrap();
    let succ = non_normal
        .level_table()
        .iter()
        .position(|level| matches!(level, LevelNode::Succ(_)))
        .unwrap();
    non_normal.mutate_parts_for_test(|parts| {
        parts.level_table[succ] = LevelNode::Max(0, 0);
        parts.hashes.certificate_hash[0] ^= 1;
    });
    assert_eq!(
        validation_reuse_verify_tables_for_test(&non_normal).unwrap_err(),
        CertError::NonCanonicalEncoding {
            object: "LevelTable"
        }
    );

    let mut bad_reference = non_normal;
    bad_reference.mutate_parts_for_test(|parts| {
        parts.level_table[succ] = LevelNode::Max(succ, succ);
    });
    assert_eq!(
        validation_reuse_verify_tables_for_test(&bad_reference).unwrap_err(),
        CertError::NonCanonicalEncoding {
            object: "LevelTable"
        }
    );
}

#[test]
fn validation_reuse_term_reference_order() {
    let cert = build_module_cert(const_module(), &[]).unwrap();
    let mut cases = Vec::new();

    let mut child = cert.clone();
    let index = child
        .term_table()
        .iter()
        .enumerate()
        .find(|(_, term)| matches!(term, TermNode::Pi { .. } | TermNode::Lam { .. }))
        .map(|(index, _)| index)
        .unwrap();
    child.mutate_parts_for_test(|parts| match &mut parts.term_table[index] {
        TermNode::Pi { ty, .. } | TermNode::Lam { ty, .. } => *ty = index,
        _ => unreachable!(),
    });
    cases.push(child);

    let mut level = cert.clone();
    let index = level
        .term_table()
        .iter()
        .enumerate()
        .find(|(_, term)| matches!(term, TermNode::Sort(_)))
        .map(|(index, _)| index)
        .unwrap();
    level.mutate_parts_for_test(|parts| {
        parts.term_table[index] = TermNode::Sort(usize::MAX);
    });
    cases.push(level);

    let mut global = cert;
    global.mutate_parts_for_test(|parts| {
        parts.term_table[0] = TermNode::Const {
            global_ref: GlobalRef::Local {
                decl_index: usize::MAX,
            },
            levels: Vec::new(),
        };
    });
    cases.push(global);

    for malformed in cases {
        assert_eq!(
            validation_reuse_verify_tables_for_test(&malformed).unwrap_err(),
            CertError::NonCanonicalEncoding {
                object: "TermTable"
            }
        );
    }
}

#[test]
fn validation_reuse_reference_stage_differential() {
    let mut cert = build_module_cert(const_module(), &[]).unwrap();
    let index = cert
        .term_table()
        .iter()
        .enumerate()
        .find(|(_, term)| matches!(term, TermNode::Pi { .. }))
        .map(|(index, _)| index)
        .unwrap();
    cert.mutate_parts_for_test(|parts| {
        if let TermNode::Pi { body, .. } = &mut parts.term_table[index] {
            *body = index;
        }
    });
    let mut counter = ValidationReuseWorkCounter::default();
    let error =
        validation_reuse_verify_tables_with_counter_for_test(&cert, &mut counter).unwrap_err();
    assert_eq!(
        error,
        CertError::NonCanonicalEncoding {
            object: "TermTable"
        }
    );
    assert_eq!(counter.term_key_encodings, 0);
    assert_eq!(counter.term_hash_passes, 0);
}

#[test]
fn validation_reuse_hash_pass_counts() {
    validation_reuse_byte_work_equation();
    validation_reuse_built_work_equation();
}

#[test]
fn validation_reuse_typed_hash_differential() {
    for bytes in validation_reuse_format_fixture_bytes() {
        let mut cert = decode_module_cert(&bytes).unwrap();
        cert.mutate_parts_for_test(|parts| parts.hashes.certificate_hash[0] ^= 1);
        let mutated = encode_module_cert(&cert).unwrap();
        let mut byte_counter = ValidationReuseWorkCounter::default();
        let byte = verify_module_cert_hashes_impl_with_validation_reuse_counter(
            &mutated,
            &mut byte_counter,
        )
        .map(|_| ());
        let mut built_counter = ValidationReuseWorkCounter::default();
        let built = verify_built_module_cert_hashes_impl_with_validation_reuse_counter(
            &cert,
            &mut built_counter,
        );
        assert_eq!(byte, built);
        assert_eq!(byte_counter.level_hash_passes, 1);
        assert_eq!(built_counter.level_hash_passes, 1);
    }
}

#[test]
fn validation_reuse_all_byte_entry_paths() {
    let cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let bytes = encode_module_cert(&cert).unwrap();
    assert_eq!(verify_module_cert_hashes(&bytes).unwrap(), cert);
    let policy = AxiomPolicy::normal();
    let expected = verify_module_cert_with_import_refs(&bytes, &[], &policy).unwrap();
    assert_eq!(
        verify_decoded_module_cert_with_import_refs(&cert, &bytes, &[], &policy).unwrap(),
        expected
    );
    let mut session = VerifierSession::new();
    assert_eq!(
        verify_module_cert(&bytes, &mut session, &policy).unwrap(),
        expected
    );
    let mut session = VerifierSession::new();
    assert_eq!(
        verify_decoded_module_cert(&cert, &bytes, &mut session, &policy).unwrap(),
        expected
    );
}

fn validation_reuse_legacy_built_result(cert: &ModuleCert) -> Result<()> {
    structural_preflight(cert)?;
    validation_reuse_legacy_table_oracle_for_test(cert)?;
    validation_reuse_legacy_hash_oracle_for_test(cert)
}

fn validation_reuse_new_built_result(cert: &ModuleCert) -> Result<()> {
    let mut counter = ValidationReuseWorkCounter::default();
    verify_built_module_cert_hashes_impl_with_validation_reuse_counter(cert, &mut counter)
}

#[test]
fn validation_reuse_built_multifault_differential() {
    for bytes in validation_reuse_format_fixture_bytes() {
        let cert = decode_module_cert(&bytes).unwrap();

        let mut table_then_late_hash = cert.clone();
        table_then_late_hash.mutate_parts_for_test(|parts| {
            parts.term_table.push(parts.term_table[0].clone());
            parts.declarations[0].hashes.decl_interface_hash[0] ^= 1;
            parts.hashes.export_hash[0] ^= 1;
            parts.hashes.certificate_hash[0] ^= 1;
        });
        let expected = validation_reuse_legacy_built_result(&table_then_late_hash);
        assert_eq!(
            validation_reuse_new_built_result(&table_then_late_hash),
            expected
        );
        assert!(matches!(
            expected,
            Err(CertError::NonCanonicalEncoding {
                object: "TermTable"
            })
        ));

        let mut declaration_then_export = cert.clone();
        declaration_then_export.mutate_parts_for_test(|parts| {
            parts.declarations[0].hashes.decl_interface_hash[0] ^= 1;
            parts.hashes.export_hash[0] ^= 1;
            parts.hashes.certificate_hash[0] ^= 1;
        });
        let expected = validation_reuse_legacy_built_result(&declaration_then_export);
        assert_eq!(
            validation_reuse_new_built_result(&declaration_then_export),
            expected
        );
        assert!(
            matches!(
                &expected,
                Err(CertError::HashMismatch {
                    object: HashObject::DeclInterface,
                    ..
                })
            ),
            "observed declaration rejection: {expected:?}"
        );

        let mut export_then_certificate = cert;
        export_then_certificate.mutate_parts_for_test(|parts| {
            parts.hashes.export_hash[0] ^= 1;
            parts.hashes.certificate_hash[0] ^= 1;
        });
        let expected = validation_reuse_legacy_built_result(&export_then_certificate);
        assert_eq!(
            validation_reuse_new_built_result(&export_then_certificate),
            expected
        );
        assert!(matches!(
            expected,
            Err(CertError::HashMismatch {
                object: HashObject::ExportBlock,
                ..
            })
        ));
    }

    let tagged = v0_4_opaque_alias_cert_with_local_implementation_dependency();
    assert_eq!(
        validation_reuse_new_built_result(&tagged),
        validation_reuse_legacy_built_result(&tagged)
    );
}

#[test]
fn validation_reuse_bounded_dag_differential() {
    let mut valid = 0_usize;
    let mut malformed = 0_usize;
    for module in [id_module("A", "x"), const_module(), nat_module()] {
        let cert = build_module_cert(module, &[]).unwrap();
        let expected = validation_reuse_legacy_table_oracle_for_test(&cert);
        assert_eq!(validation_reuse_verify_tables_for_test(&cert), expected);
        valid += usize::from(expected.is_ok());

        for index in 0..cert.level_table().len() {
            for child in 0..=cert.level_table().len() {
                let mut candidate = cert.clone();
                candidate.mutate_parts_for_test(|parts| {
                    parts.level_table[index] = LevelNode::Succ(child);
                });
                let expected = validation_reuse_legacy_table_oracle_for_test(&candidate);
                assert_eq!(
                    validation_reuse_verify_tables_for_test(&candidate),
                    expected
                );
                valid += usize::from(expected.is_ok());
                malformed += usize::from(expected.is_err());
            }
        }
        for index in 0..cert.term_table().len() {
            for child in 0..=cert.term_table().len() {
                for replacement in [TermNode::Sort(child), TermNode::App(child, child)] {
                    let mut candidate = cert.clone();
                    candidate.mutate_parts_for_test(|parts| {
                        parts.term_table[index] = replacement.clone();
                    });
                    let expected = validation_reuse_legacy_table_oracle_for_test(&candidate);
                    assert_eq!(
                        validation_reuse_verify_tables_for_test(&candidate),
                        expected
                    );
                    valid += usize::from(expected.is_ok());
                    malformed += usize::from(expected.is_err());
                }
            }
        }
    }
    assert!(valid >= 3);
    assert!(malformed >= 100);
}

#[test]
fn validation_reuse_all_formats_byte_differential() {
    for bytes in validation_reuse_format_fixture_bytes() {
        let decoded = decode_module_cert(&bytes).unwrap();
        assert_eq!(verify_module_cert_hashes(&bytes).unwrap(), decoded);
        assert_eq!(encode_module_cert(&decoded).unwrap(), bytes);

        let mut rejected = decoded.clone();
        rejected.mutate_parts_for_test(|parts| parts.hashes.certificate_hash[0] ^= 1);
        let rejected_bytes = encode_module_cert(&rejected).unwrap();
        let mut counter = ValidationReuseWorkCounter::default();
        let observed = verify_module_cert_hashes_impl_with_validation_reuse_counter(
            &rejected_bytes,
            &mut counter,
        )
        .map(|_| ());
        assert_eq!(observed, validation_reuse_legacy_built_result(&rejected));
        assert!(matches!(
            observed,
            Err(CertError::HashMismatch {
                object: HashObject::ModuleCertificate,
                ..
            })
        ));
        assert_eq!(counter.level_hash_passes, 1);
        assert_eq!(counter.term_hash_passes, 1);
        assert_eq!(counter.canonical_full_encodings, 1);
    }
}

#[test]
fn validation_reuse_all_formats_built_differential() {
    for bytes in validation_reuse_format_fixture_bytes() {
        let cert = decode_module_cert(&bytes).unwrap();
        let mut counter = ValidationReuseWorkCounter::default();
        verify_built_module_cert_hashes_impl_with_validation_reuse_counter(&cert, &mut counter)
            .unwrap();
        assert_eq!(counter.canonical_full_encodings, 0);
        assert_eq!(counter.lazy_built_materializations, 1);

        let mut rejected = cert;
        rejected.mutate_parts_for_test(|parts| {
            parts.declarations[0].hashes.decl_certificate_hash[0] ^= 1;
            parts.hashes.certificate_hash[0] ^= 1;
        });
        let mut counter = ValidationReuseWorkCounter::default();
        let observed = verify_built_module_cert_hashes_impl_with_validation_reuse_counter(
            &rejected,
            &mut counter,
        );
        assert_eq!(observed, validation_reuse_legacy_built_result(&rejected));
        assert!(matches!(
            observed,
            Err(CertError::HashMismatch {
                object: HashObject::DeclCertificate,
                ..
            })
        ));
        assert_eq!(counter.canonical_full_encodings, 0);
        assert_eq!(counter.lazy_built_materializations, 0);
    }
}

#[test]
fn validation_reuse_outer_error_order() {
    let cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let bytes = encode_module_cert(&cert).unwrap();
    let mut nonminimal_uvar = bytes.clone();
    nonminimal_uvar[0] |= 0x80;
    nonminimal_uvar.insert(1, 0x00);
    let mut unsupported = bytes.clone();
    let offset = unsupported
        .windows(FORMAT.len())
        .position(|window| window == FORMAT.as_bytes())
        .unwrap();
    unsupported[offset..offset + FORMAT.len()].copy_from_slice(b"NPA-CERT-9.9.9");
    let mut structural = cert.clone();
    let duplicate = structural.term_table()[0].clone();
    structural.mutate_parts_for_test(|parts| parts.term_table.push(duplicate));
    let structural_bytes = encode_module_cert(&structural).unwrap();
    let over_limit = vec![0_u8; MAX_CERTIFICATE_BYTES + 1];
    let cases = vec![
        (bytes[..bytes.len() - 1].to_vec(), "truncated"),
        ([bytes.as_slice(), &[0xff]].concat(), "trailing"),
        (nonminimal_uvar, "nonminimal-uvar"),
        (unsupported, "unsupported-format"),
        (structural_bytes, "structural"),
        (over_limit, "over-byte-limit"),
    ];
    for (malformed, label) in cases {
        let mut counter = ValidationReuseWorkCounter::default();
        let error =
            verify_module_cert_hashes_impl_with_validation_reuse_counter(&malformed, &mut counter)
                .unwrap_err();
        match label {
            "nonminimal-uvar" => assert!(matches!(
                error,
                CertError::NonCanonicalEncoding { object: "uvar" }
            )),
            "unsupported-format" => {
                assert!(matches!(error, CertError::UnsupportedFormat { .. }))
            }
            "structural" => assert!(matches!(
                error,
                CertError::NonCanonicalEncoding {
                    object: "TermTable"
                }
            )),
            "over-byte-limit" => assert!(matches!(
                error,
                CertError::StructuralLimitExceeded {
                    kind: StructuralLimitKind::CertificateBytes,
                    ..
                }
            )),
            "truncated" | "trailing" => assert!(matches!(error, CertError::DecodeError)),
            _ => unreachable!(),
        }
        if label == "structural" {
            assert_eq!(counter.level_hash_passes, 1);
            assert_eq!(counter.level_key_encodings, cert.level_table().len() as u64);
            assert!(counter.term_key_encodings > 0);
            assert_eq!(counter.term_hash_passes, 0);
            assert_eq!(counter.canonical_full_encodings, 1);
        } else {
            assert_eq!(counter.level_key_encodings, 0);
            assert_eq!(counter.term_key_encodings, 0);
            assert_eq!(counter.canonical_full_encodings, 0);
        }
    }
}

#[test]
fn validation_reuse_error_precedence_baseline() {
    validation_reuse_level_normalization_order();
    validation_reuse_term_reference_order();
    validation_reuse_typed_hash_differential();
    validation_reuse_outer_error_order();
}

#[test]
fn canonical_full_buffer_default_dispatch() {
    let cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let bytes = encode_module_cert(&cert).unwrap();
    let mut counter = ValidationReuseWorkCounter::default();
    verify_module_cert_hashes_impl_with_validation_reuse_counter(&bytes, &mut counter).unwrap();
    assert_eq!(counter.canonical_full_encodings, 1);
    assert_eq!(counter.authoritative_prefix_uses, 1);
    assert_eq!(counter.streamed_prehash_uses, 0);
}

#[test]
fn reusable_vector_key_sink_default_dispatch() {
    let cert = build_module_cert(const_module(), &[]).unwrap();
    let mut counter = ValidationReuseWorkCounter::default();
    validation_reuse_verify_tables_with_counter_for_test(&cert, &mut counter).unwrap();
    assert_eq!(counter.level_key_encodings, cert.level_table().len() as u64);
    assert_eq!(counter.term_key_encodings, cert.term_table().len() as u64);
    assert!(counter.key_scratch_allocated_bytes > 0);
}

fn id_def_module_with_value(value: Expr) -> CoreModule {
    id_def_module_with_value_and_reducibility(value, Reducibility::Reducible)
}

fn id_def_module_with_value_and_reducibility(
    value: Expr,
    reducibility: Reducibility,
) -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Test.Id"),
        declarations: vec![Decl::Def {
            name: "id".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: id_type("A", "x"),
            value,
            reducibility,
        }],
    }
}

#[test]
fn explicit_ephemeral_kernel_memo_preserves_verified_module_identity() {
    let cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let bytes = encode_module_cert(&cert).unwrap();
    let policy = AxiomPolicy::normal();
    let off = verify_module_cert_with_import_refs(&bytes, &[], &policy).unwrap();
    let mut counters = npa_kernel::KernelWorkCounters::default();
    let memo = verify_module_cert_with_import_refs_and_kernel_options_and_work_counters(
        &bytes,
        &[],
        &policy,
        npa_kernel::KernelExecutionOptions::ephemeral_memo(),
        &mut counters,
    )
    .unwrap();
    assert_eq!(memo, off);
    assert!(counters.infer_calls > 0);
    assert!(counters.check_calls > 0);
    assert_eq!(counters.memo_entry_capacity, 12_288);
}

fn const_module() -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Test.Const"),
        declarations: vec![Decl::Def {
            name: "const".to_owned(),
            universe_params: vec!["u".to_owned(), "v".to_owned()],
            ty: const_type(),
            value: const_value(),
            reducibility: Reducibility::Reducible,
        }],
    }
}

fn constrained_axiom_module(constraints: Vec<UniverseConstraint>) -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Test.UniverseConstraints"),
        declarations: vec![if constraints.is_empty() {
            Decl::Axiom {
                name: "List.map".to_owned(),
                universe_params: vec!["u".to_owned(), "v".to_owned(), "w".to_owned()],
                ty: Expr::sort(Level::param("w")),
            }
        } else {
            Decl::AxiomConstrained {
                name: "List.map".to_owned(),
                universe_params: vec!["u".to_owned(), "v".to_owned(), "w".to_owned()],
                universe_constraints: constraints,
                ty: Expr::sort(Level::param("w")),
            }
        }],
    }
}

fn max_u_v_le_w() -> UniverseConstraint {
    UniverseConstraint::le(
        Level::max(Level::param("u"), Level::param("v")),
        Level::param("w"),
    )
}

fn succ_u_le_u() -> UniverseConstraint {
    UniverseConstraint::le(Level::succ(Level::param("u")), Level::param("u"))
}

fn opaque_alias_module() -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Test.OpaqueAlias"),
        declarations: vec![
            Decl::Def {
                name: "opaque_id".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: id_type("A", "x"),
                value: id_value("A", "x"),
                reducibility: Reducibility::Opaque,
            },
            Decl::Def {
                name: "opaque_id_alias".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: id_type("A", "x"),
                value: Expr::konst("opaque_id", vec![Level::param("u")]),
                reducibility: Reducibility::Reducible,
            },
        ],
    }
}

fn named_opaque_id(name: &str, value: Expr) -> Decl {
    Decl::Def {
        name: name.to_owned(),
        universe_params: vec!["u".to_owned()],
        ty: id_type("A", "x"),
        value,
        reducibility: Reducibility::Opaque,
    }
}

fn named_id_alias(name: &str, target: &str, reducibility: Reducibility) -> Decl {
    Decl::Def {
        name: name.to_owned(),
        universe_params: vec!["u".to_owned()],
        ty: id_type("A", "x"),
        value: Expr::konst(target, vec![Level::param("u")]),
        reducibility,
    }
}

fn named_id_theorem(name: &str, proof: &str) -> Decl {
    Decl::Theorem {
        name: name.to_owned(),
        universe_params: vec!["u".to_owned()],
        ty: id_type("A", "x"),
        proof: Expr::konst(proof, vec![Level::param("u")]),
    }
}

fn opaque_alias_chain_module() -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Test.OpaqueAliasChain"),
        declarations: vec![
            named_opaque_id("hidden", id_value("A", "x")),
            named_id_alias("alias", "hidden", Reducibility::Reducible),
            named_id_theorem("uses_alias", "alias"),
        ],
    }
}

fn opaque_nat_equality_module(value: Expr) -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Test.OpaqueNatEquality"),
        declarations: vec![
            Decl::Def {
                name: "hidden_nat".to_owned(),
                universe_params: vec![],
                ty: nat(),
                value,
                reducibility: Reducibility::Opaque,
            },
            Decl::Theorem {
                name: "hidden_nat_eq_zero".to_owned(),
                universe_params: vec![],
                ty: eq(
                    type0(),
                    nat(),
                    Expr::konst("hidden_nat", vec![]),
                    nat_zero(),
                ),
                proof: eq_refl(type0(), nat(), nat_zero()),
            },
        ],
    }
}

fn imported_opaque_nat_equality_module() -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Test.ImportedOpaqueNatEquality"),
        declarations: vec![Decl::Theorem {
            name: "imported_hidden_nat_eq_zero".to_owned(),
            universe_params: vec![],
            ty: eq(
                type0(),
                nat(),
                Expr::konst("hidden_nat", vec![]),
                nat_zero(),
            ),
            proof: eq_refl(type0(), nat(), nat_zero()),
        }],
    }
}

fn opaque_declared_type_module() -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Test.OpaqueDeclaredType"),
        declarations: vec![
            Decl::Def {
                name: "hidden_type".to_owned(),
                universe_params: vec![],
                ty: Expr::sort(Level::succ(Level::zero())),
                value: Expr::sort(Level::zero()),
                reducibility: Reducibility::Opaque,
            },
            Decl::Axiom {
                name: "hidden_witness".to_owned(),
                universe_params: vec![],
                ty: Expr::konst("hidden_type", vec![]),
            },
            Decl::Axiom {
                name: "typed_constant".to_owned(),
                universe_params: vec![],
                ty: Expr::pi(
                    "_",
                    Expr::konst("hidden_type", vec![]),
                    Expr::sort(Level::zero()),
                ),
            },
            Decl::Theorem {
                name: "uses_witness_type".to_owned(),
                universe_params: vec![],
                ty: Expr::sort(Level::zero()),
                proof: Expr::app(
                    Expr::konst("typed_constant", vec![]),
                    Expr::konst("hidden_witness", vec![]),
                ),
            },
        ],
    }
}

fn nested_opaque_module() -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Test.NestedOpaque"),
        declarations: vec![
            named_opaque_id("inner_hidden", id_value("A", "x")),
            named_opaque_id(
                "outer_hidden",
                Expr::konst("inner_hidden", vec![Level::param("u")]),
            ),
            named_id_alias("uses_outer", "outer_hidden", Reducibility::Reducible),
        ],
    }
}

fn theorem_interface_only_module(hidden_value: Expr) -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Test.TheoremInterfaceOnly"),
        declarations: vec![
            named_opaque_id("hidden", hidden_value),
            named_id_theorem("stable_theorem", "hidden"),
            named_id_alias(
                "uses_stable_theorem",
                "stable_theorem",
                Reducibility::Reducible,
            ),
        ],
    }
}

fn build_v0_4_cert(module: CoreModule) -> ModuleCert {
    build_module_cert(module, &[]).unwrap()
}

fn v0_4_opaque_alias_cert_with_interface_dependency() -> ModuleCert {
    let mut cert = build_v0_4_cert(opaque_alias_module());
    replace_first_local_dependency_with_interface(&mut cert);
    cert
}

fn first_local_dependency(cert: &ModuleCert) -> (usize, usize) {
    let consumer_index = cert
        .declarations()
        .iter()
        .position(|decl| {
            decl.dependencies
                .iter()
                .any(|dependency| matches!(dependency.global_ref(), GlobalRef::Local { .. }))
        })
        .unwrap();
    let dependency_index = cert.declarations()[consumer_index]
        .dependencies
        .iter()
        .position(|dependency| matches!(dependency.global_ref(), GlobalRef::Local { .. }))
        .unwrap();
    (consumer_index, dependency_index)
}

fn replace_first_local_dependency_with_interface(cert: &mut ModuleCert) -> usize {
    let (consumer_index, dependency_index) = first_local_dependency(cert);
    let dependency = &cert.declarations()[consumer_index].dependencies[dependency_index];
    let interface = DependencyEntry::checked_interface(
        dependency.global_ref().clone(),
        dependency.decl_interface_hash(),
    )
    .unwrap();
    cert.mutate_parts_for_test(|parts| {
        parts.declarations[consumer_index].dependencies[dependency_index] = interface;
    });
    rehash_v0_4_dependency_change(cert, consumer_index);
    consumer_index
}

fn replace_first_local_dependency_with_implementation(cert: &mut ModuleCert) -> usize {
    let (consumer_index, dependency_index) = first_local_dependency(cert);
    let global_ref = cert.declarations()[consumer_index].dependencies[dependency_index]
        .global_ref()
        .clone();
    let implementation = DependencyEntry::checked_local_implementation(
        global_ref,
        consumer_index,
        cert.declarations(),
    )
    .unwrap();
    cert.mutate_parts_for_test(|parts| {
        parts.declarations[consumer_index].dependencies[dependency_index] = implementation;
    });
    rehash_v0_4_dependency_change(cert, consumer_index);
    consumer_index
}

fn rehash_v0_4_dependency_change(cert: &mut ModuleCert, consumer_index: usize) {
    let level_hashes = compute_level_hashes(cert.level_table(), cert.name_table()).unwrap();
    let term_hashes = compute_term_hashes(cert.term_table(), &level_hashes).unwrap();
    let declaration_hashes = compute_decl_hashes(
        CertificateFormatVersion::V0_4_0,
        &cert.declarations()[consumer_index].decl,
        &cert.declarations()[consumer_index].dependencies,
        &cert.declarations()[consumer_index].axiom_dependencies,
        DeclHashTables {
            terms: cert.term_table(),
            level_hashes: &level_hashes,
            term_hashes: &term_hashes,
            names: cert.name_table(),
        },
    )
    .unwrap();
    cert.mutate_parts_for_test(|parts| {
        parts.declarations[consumer_index].hashes = declaration_hashes;
    });
    let export_block =
        build_export_block(cert.declarations(), cert.term_table(), &term_hashes).unwrap();
    let export_hash = hash_with_domain(MODULE_EXPORT_DOMAIN, &encode_export_block(&export_block));
    cert.mutate_parts_for_test(|parts| {
        parts.export_block = export_block;
        parts.hashes.export_hash = export_hash;
    });
    let certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash_for_header(cert).unwrap(),
    );
    cert.mutate_parts_for_test(|parts| parts.hashes.certificate_hash = certificate_hash);
}

fn v0_4_opaque_alias_cert_with_local_implementation_dependency() -> ModuleCert {
    build_v0_4_cert(opaque_alias_module())
}

fn v0_4_dependency_bytes(entry: &DependencyEntry) -> Vec<u8> {
    let mut bytes = vec![match entry.kind() {
        DependencyEntryKind::Interface => 0x00,
        DependencyEntryKind::LocalImplementation => 0x01,
    }];
    encode_global_ref_to(&mut bytes, entry.global_ref());
    bytes.extend(entry.decl_interface_hash());
    if let Some(decl_certificate_hash) = entry.decl_certificate_hash() {
        bytes.extend(decl_certificate_hash);
    }
    bytes
}

fn decl_index_named(cert: &ModuleCert, expected: &str) -> usize {
    let expected = Name::from_dotted(expected);
    cert.declarations()
        .iter()
        .position(|declaration| {
            let name = match &declaration.decl {
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
            cert.name_table()[name] == expected
        })
        .unwrap()
}

fn local_implementation_targets(cert: &ModuleCert, decl_index: usize) -> BTreeSet<usize> {
    cert.declarations()[decl_index]
        .dependencies
        .iter()
        .filter_map(|dependency| {
            (dependency.kind() == DependencyEntryKind::LocalImplementation)
                .then(|| match dependency.global_ref() {
                    GlobalRef::Local { decl_index } => Some(*decl_index),
                    _ => None,
                })
                .flatten()
        })
        .collect()
}

fn replace_first_local_dependency_with_raw_implementation(
    cert: &mut ModuleCert,
    global_ref: GlobalRef,
    decl_interface_hash: Hash,
    decl_certificate_hash: Hash,
) -> usize {
    let (consumer_index, dependency_index) = first_local_dependency(cert);
    cert.mutate_parts_for_test(|parts| {
        parts.declarations[consumer_index].dependencies[dependency_index] =
            DependencyEntry::from_decoded_local_implementation(
                global_ref,
                decl_interface_hash,
                decl_certificate_hash,
            );
        parts.declarations[consumer_index].dependencies.sort();
    });
    rehash_v0_4_dependency_change(cert, consumer_index);
    consumer_index
}

fn assert_local_implementation_error(
    cert: &ModuleCert,
    expected_reason: LocalImplementationDependencyErrorReason,
) {
    let err = verify_module_cert_with_import_refs(
        &encode_module_cert(cert).unwrap(),
        &[],
        &AxiomPolicy::normal(),
    )
    .unwrap_err();
    assert!(
        matches!(
            err,
        CertError::InvalidLocalImplementationDependency { reason, .. }
            if reason == expected_reason && reason.as_str() == expected_reason.as_str()
        ),
        "unexpected error for {expected_reason:?}: {err:?}"
    );
}

fn height_order_regression_constraints() -> Vec<UniverseConstraint> {
    vec![
        UniverseConstraint::le(Level::succ(Level::succ(Level::zero())), Level::param("u")),
        max_u_v_le_w(),
    ]
}

fn universe_meta_param_certificate_bytes() -> Vec<u8> {
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
    cert.mutate_parts_for_test(|parts| {
        for name in &mut parts.name_table {
            if name.as_dotted() == "w" {
                *name = Name::from_dotted("z?meta");
            }
        }
    });
    encode_module_cert(&cert).unwrap()
}

#[test]
fn decode_with_import_offsets_preserves_import_order() {
    let id_cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let mut session = VerifierSession::new();
    let verified_id = verify_cert(&id_cert, &mut session);
    let use_id_cert = build_module_cert(use_id_module(), &[verified_id]).unwrap();
    let bytes = encode_module_cert(&use_id_cert).unwrap();

    let (decoded, import_offsets) = decode_module_cert_with_import_offsets(&bytes).unwrap();

    assert_eq!(decoded, use_id_cert);
    assert_eq!(import_offsets.len(), decoded.imports().len());
    assert_eq!(import_offsets.len(), 1);
    assert!(import_offsets[0] < bytes.len());
}

#[test]
fn hash_only_verification_rejects_a_corrupted_stored_certificate_hash() {
    let cert = build_module_cert(id_module("HashOnly", "x"), &[]).unwrap();
    let mut bytes = encode_module_cert(&cert).unwrap();
    let last = bytes.last_mut().expect("certificate hash trailer");
    *last ^= 1;

    assert!(matches!(
        verify_module_cert_hashes(&bytes),
        Err(CertError::HashMismatch {
            object: HashObject::ModuleCertificate,
            ..
        })
    ));
}

#[test]
fn canonical_certificate_name_grammar_allows_ascii_prime() {
    assert!(Name::from_dotted("Math.Algebra.eq_trans'").is_canonical());
    assert!(Name::from_dotted("Foo.Bar.baz''").is_canonical());
    assert!(Name::from_dotted("_Private._helper2'").is_canonical());

    let cert = build_module_cert(
        CoreModule {
            name: Name::from_dotted("Test.NameGrammar"),
            declarations: vec![Decl::Axiom {
                name: "p'".to_owned(),
                universe_params: Vec::new(),
                ty: Expr::sort(Level::zero()),
            }],
        },
        &[],
    )
    .unwrap();
    assert_eq!(
        cert.name_table()
            .iter()
            .map(Name::as_dotted)
            .collect::<Vec<_>>(),
        vec!["Test.NameGrammar", "p'"]
    );
}

#[test]
fn canonical_certificate_name_grammar_rejects_operator_and_unicode_prime() {
    for name in [
        "",
        ".Nat",
        "Nat.",
        "Nat..add",
        "2Nat",
        "Nat.2add",
        "Nat.+",
        "Nat.mul*",
        "Nat.add-prime",
        "Nat.add′",
        "'Nat",
    ] {
        assert!(!Name::from_dotted(name).is_canonical(), "{name}");
    }

    let err = build_module_cert(
        CoreModule {
            name: Name::from_dotted("Test.NameGrammar"),
            declarations: vec![Decl::Axiom {
                name: "p+".to_owned(),
                universe_params: Vec::new(),
                ty: Expr::sort(Level::zero()),
            }],
        },
        &[],
    )
    .unwrap_err();
    assert!(matches!(
        err,
        CertError::NonCanonicalEncoding { object: "Name" }
    ));
}

#[test]
fn universe_constraints_canonical_hash_accepts_empty_and_non_empty_sets() {
    let params = vec!["u".to_owned(), "v".to_owned(), "w".to_owned()];
    let empty = universe_constraints_hash(&params, &[]).unwrap();
    let also_empty = universe_constraints_hash(&params, &[]).unwrap();
    let constrained = universe_constraints_hash(&params, &[max_u_v_le_w()]).unwrap();

    assert_eq!(empty, also_empty);
    assert_ne!(empty, constrained);
    assert_ne!(
        universe_constraints_canonical_bytes(&params, &[]).unwrap(),
        universe_constraints_canonical_bytes(&params, &[max_u_v_le_w()]).unwrap()
    );
}

#[test]
fn universe_constraints_reject_unresolved_meta_params() {
    let meta = universe_constraints_hash(&["z?meta".to_owned()], &[]);
    assert!(matches!(
        meta,
        Err(CertError::Kernel(
            npa_kernel::Error::UnresolvedUniverseMeta(param)
        )) if param == "z?meta"
    ));

    let cert = build_module_cert(
        CoreModule {
            name: Name::from_dotted("Test.UniverseMeta"),
            declarations: vec![Decl::Axiom {
                name: "a".to_owned(),
                universe_params: vec!["z?meta".to_owned()],
                ty: Expr::sort(Level::param("z?meta")),
            }],
        },
        &[],
    );
    assert!(matches!(
        cert,
        Err(CertError::NonCanonicalEncoding { object: "Name" })
    ));
}

#[test]
fn universe_constraints_reject_bad_params_and_noncanonical_levels() {
    let duplicate = universe_constraints_hash(&["u".to_owned(), "u".to_owned()], &[]);
    assert!(matches!(
        duplicate,
        Err(CertError::Kernel(npa_kernel::Error::DuplicateUniverseParam(param)))
            if param == "u"
    ));

    let noncanonical_params = universe_constraints_hash(&["v".to_owned(), "u".to_owned()], &[]);
    assert!(matches!(
        noncanonical_params,
        Err(CertError::Kernel(
            npa_kernel::Error::NonCanonicalUniverseParams(_)
        ))
    ));

    let unknown_param = universe_constraints_hash(
        &["u".to_owned()],
        &[UniverseConstraint::le(Level::param("u"), Level::param("v"))],
    );
    assert!(matches!(
        unknown_param,
        Err(CertError::Kernel(npa_kernel::Error::UnknownUniverseParam(param)))
            if param == "v"
    ));

    let noncanonical_level = UniverseConstraint::le(
        Level::Max(Box::new(Level::param("v")), Box::new(Level::param("u"))),
        Level::param("v"),
    );
    let noncanonical_level_err =
        universe_constraints_hash(&["u".to_owned(), "v".to_owned()], &[noncanonical_level]);
    assert!(matches!(
        noncanonical_level_err,
        Err(CertError::Kernel(
            npa_kernel::Error::NonCanonicalUniverseLevel { .. }
        ))
    ));
}

#[test]
fn universe_constraints_change_certificate_hash_and_import_hash() {
    let empty = build_module_cert(constrained_axiom_module(vec![]), &[]).unwrap();
    let constrained =
        build_module_cert(constrained_axiom_module(vec![max_u_v_le_w()]), &[]).unwrap();

    assert_ne!(
        empty.declarations()[0].hashes.decl_interface_hash,
        constrained.declarations()[0].hashes.decl_interface_hash
    );
    assert_ne!(empty.hashes().export_hash, constrained.hashes().export_hash);
    assert_ne!(
        empty.hashes().certificate_hash,
        constrained.hashes().certificate_hash
    );
}

#[test]
fn constrained_export_entries_encode_universe_constraints_in_current_format() {
    let cert = build_module_cert(constrained_axiom_module(vec![max_u_v_le_w()]), &[]).unwrap();

    assert_eq!(cert.header().format, FORMAT);
    assert_eq!(cert.header().core_spec, CORE_SPEC);
    assert_eq!(
        cert.hashes().export_hash,
        hash_with_domain(
            MODULE_EXPORT_DOMAIN,
            &encode_export_block(cert.export_block())
        )
    );
    assert_eq!(
        cert.hashes().certificate_hash,
        hash_with_domain(
            MODULE_CERT_DOMAIN,
            &encode_module_cert_without_certificate_hash(&cert)
        )
    );
    assert_eq!(cert.export_block().len(), 1);
    assert_eq!(cert.export_block()[0].universe_constraints.len(), 1);

    let bytes = encode_module_cert(&cert).unwrap();
    let decoded = decode_module_cert(&bytes).unwrap();
    assert_eq!(
        decoded.export_block()[0].universe_constraints,
        cert.export_block()[0].universe_constraints
    );

    let mut session = VerifierSession::new();
    verify_module_cert(&bytes, &mut session, &AxiomPolicy::normal()).unwrap();
}

#[test]
fn imported_public_signature_reconstructs_exported_universe_constraints() {
    let cert = build_module_cert(constrained_axiom_module(vec![max_u_v_le_w()]), &[]).unwrap();
    let mut session = VerifierSession::new();
    let verified = verify_module_cert(
        &encode_module_cert(&cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap();

    let decls = verified_module_to_kernel_decls(&verified).unwrap();
    assert!(matches!(
        &decls[0],
        Decl::AxiomConstrained {
            universe_constraints,
            ..
        } if universe_constraints == &[max_u_v_le_w()]
    ));

    let mut stripped_export = verified.clone();
    stripped_export.mutate_certificate_parts_for_test(|parts| {
        parts.export_block[0].universe_constraints.clear();
    });
    let stripped_decls = verified_module_to_kernel_decls(&stripped_export).unwrap();
    assert!(matches!(&stripped_decls[0], Decl::Axiom { .. }));
}

#[test]
fn hash_v0_4_opaque_body_change_keeps_public_identity() {
    let direct = build_v0_4_cert(id_def_module_with_value_and_reducibility(
        id_value("A", "x"),
        Reducibility::Opaque,
    ));
    let beta = build_v0_4_cert(id_def_module_with_value_and_reducibility(
        id_value_with_beta_redex(),
        Reducibility::Opaque,
    ));

    assert_eq!(
        direct.declarations()[0].hashes.decl_interface_hash,
        beta.declarations()[0].hashes.decl_interface_hash
    );
    assert_eq!(direct.export_block(), beta.export_block());
    assert_eq!(direct.hashes().export_hash, beta.hashes().export_hash);
    assert_ne!(
        direct.declarations()[0].hashes.decl_certificate_hash,
        beta.declarations()[0].hashes.decl_certificate_hash
    );
    assert_ne!(
        direct.hashes().certificate_hash,
        beta.hashes().certificate_hash
    );
    verify_module_cert_hashes(&encode_module_cert(&direct).unwrap()).unwrap();
    verify_module_cert_hashes(&encode_module_cert(&beta).unwrap()).unwrap();
}

#[test]
fn hash_v0_4_transitive_axiom_change_still_changes_public_identity() {
    let p1 = build_v0_4_cert(theorem_using_axiom_module("p1"));
    let p2 = build_v0_4_cert(theorem_using_axiom_module("p2"));

    assert_ne!(
        p1.axiom_report().per_declaration[3].transitive_axioms,
        p2.axiom_report().per_declaration[3].transitive_axioms
    );
    assert_ne!(
        p1.declarations()[3].hashes.decl_interface_hash,
        p2.declarations()[3].hashes.decl_interface_hash
    );
    assert_ne!(p1.export_block(), p2.export_block());
    assert_ne!(p1.hashes().export_hash, p2.hashes().export_hash);
    verify_module_cert_hashes(&encode_module_cert(&p1).unwrap()).unwrap();
    verify_module_cert_hashes(&encode_module_cert(&p2).unwrap()).unwrap();
}

#[test]
fn hash_v0_4_local_implementation_projects_to_public_interface_dependency() {
    let interface = v0_4_opaque_alias_cert_with_interface_dependency();
    let implementation = v0_4_opaque_alias_cert_with_local_implementation_dependency();
    let consumer_index = implementation
        .declarations()
        .iter()
        .position(|declaration| {
            declaration
                .dependencies
                .iter()
                .any(|dependency| dependency.kind() == DependencyEntryKind::LocalImplementation)
        })
        .unwrap();

    assert_eq!(
        interface.declarations()[consumer_index]
            .hashes
            .decl_interface_hash,
        implementation.declarations()[consumer_index]
            .hashes
            .decl_interface_hash
    );
    assert_eq!(interface.export_block(), implementation.export_block());
    assert_eq!(
        interface.hashes().export_hash,
        implementation.hashes().export_hash
    );
    assert_ne!(
        interface.declarations()[consumer_index]
            .hashes
            .decl_certificate_hash,
        implementation.declarations()[consumer_index]
            .hashes
            .decl_certificate_hash
    );
    assert_ne!(
        interface.hashes().certificate_hash,
        implementation.hashes().certificate_hash
    );
    verify_module_cert_hashes(&encode_module_cert(&implementation).unwrap()).unwrap();
}

#[test]
fn hash_v0_4_local_implementation_certificate_hash_is_committed_privately() {
    let cert = v0_4_opaque_alias_cert_with_interface_dependency();
    let consumer_index = cert
        .declarations()
        .iter()
        .position(|declaration| {
            declaration
                .dependencies
                .iter()
                .any(|dependency| matches!(dependency.global_ref(), GlobalRef::Local { .. }))
        })
        .unwrap();
    let global_ref = cert.declarations()[consumer_index]
        .dependencies
        .iter()
        .find(|dependency| matches!(dependency.global_ref(), GlobalRef::Local { .. }))
        .unwrap()
        .global_ref()
        .clone();
    let original_dependency = DependencyEntry::checked_local_implementation(
        global_ref.clone(),
        consumer_index,
        cert.declarations(),
    )
    .unwrap();
    let mut changed_targets = cert.declarations().to_vec();
    let GlobalRef::Local { decl_index } = global_ref else {
        unreachable!()
    };
    changed_targets[decl_index].hashes.decl_certificate_hash[0] ^= 0x01;
    let changed_dependency = DependencyEntry::checked_local_implementation(
        GlobalRef::Local { decl_index },
        consumer_index,
        &changed_targets,
    )
    .unwrap();
    let consumer = &cert.declarations()[consumer_index];
    let level_hashes = compute_level_hashes(cert.level_table(), cert.name_table()).unwrap();
    let term_hashes = compute_term_hashes(cert.term_table(), &level_hashes).unwrap();
    let original_hashes = compute_decl_hashes(
        CertificateFormatVersion::V0_4_0,
        &consumer.decl,
        &[original_dependency],
        &consumer.axiom_dependencies,
        DeclHashTables {
            terms: cert.term_table(),
            level_hashes: &level_hashes,
            term_hashes: &term_hashes,
            names: cert.name_table(),
        },
    )
    .unwrap();
    let changed_hashes = compute_decl_hashes(
        CertificateFormatVersion::V0_4_0,
        &consumer.decl,
        &[changed_dependency],
        &consumer.axiom_dependencies,
        DeclHashTables {
            terms: cert.term_table(),
            level_hashes: &level_hashes,
            term_hashes: &term_hashes,
            names: cert.name_table(),
        },
    )
    .unwrap();

    assert_eq!(
        original_hashes.decl_interface_hash,
        changed_hashes.decl_interface_hash
    );
    assert_ne!(
        original_hashes.decl_certificate_hash,
        changed_hashes.decl_certificate_hash
    );
}

#[test]
fn hash_v0_4_closure_only_local_implementation_is_absent_from_public_projection() {
    let mut module = opaque_alias_module();
    match &mut module.declarations[1] {
        Decl::Def { reducibility, .. } => *reducibility = Reducibility::Opaque,
        _ => panic!("expected definition"),
    }
    let mut interface = build_v0_4_cert(module);
    replace_first_local_dependency_with_interface(&mut interface);
    let mut implementation = interface.clone();
    let consumer_index = replace_first_local_dependency_with_implementation(&mut implementation);
    let consumer = &implementation.declarations()[consumer_index];
    let level_hashes =
        compute_level_hashes(implementation.level_table(), implementation.name_table()).unwrap();
    let term_hashes = compute_term_hashes(implementation.term_table(), &level_hashes).unwrap();
    let without_closure_dependency = compute_decl_hashes(
        CertificateFormatVersion::V0_4_0,
        &consumer.decl,
        &[],
        &consumer.axiom_dependencies,
        DeclHashTables {
            terms: implementation.term_table(),
            level_hashes: &level_hashes,
            term_hashes: &term_hashes,
            names: implementation.name_table(),
        },
    )
    .unwrap();

    assert_eq!(
        consumer.hashes.decl_interface_hash,
        without_closure_dependency.decl_interface_hash
    );
    assert_eq!(
        interface.declarations()[consumer_index]
            .hashes
            .decl_interface_hash,
        consumer.hashes.decl_interface_hash
    );
    assert_eq!(interface.export_block(), implementation.export_block());
    assert_eq!(
        interface.hashes().export_hash,
        implementation.hashes().export_hash
    );
    assert_ne!(
        interface.declarations()[consumer_index]
            .hashes
            .decl_certificate_hash,
        consumer.hashes.decl_certificate_hash
    );
    verify_module_cert_hashes(&encode_module_cert(&implementation).unwrap()).unwrap();
}

#[test]
fn current_module_opaque_body_supports_v0_4_equality_and_keeps_stored_decl_opaque() {
    let cert = build_v0_4_cert(opaque_nat_equality_module(nat_zero()));
    let hidden = decl_index_named(&cert, "hidden_nat");
    let theorem = decl_index_named(&cert, "hidden_nat_eq_zero");

    assert!(matches!(
        cert.declarations()[hidden].decl,
        DeclPayload::Def {
            reducibility: CertReducibility::Opaque,
            ..
        }
    ));
    assert_eq!(
        local_implementation_targets(&cert, theorem),
        [hidden].into()
    );
    let verified = verify_module_cert_with_import_refs(
        &encode_module_cert(&cert).unwrap(),
        &[],
        &AxiomPolicy::normal(),
    )
    .unwrap();
    assert_eq!(verified.certificate_format(), FORMAT);
    assert_eq!(verified.core_spec(), CORE_SPEC);
}

#[test]
fn imported_opaque_body_is_not_available_to_conversion_or_export_projection() {
    let imported_cert = build_v0_4_cert(CoreModule {
        name: Name::from_dotted("Test.OpaqueNatImport"),
        declarations: vec![Decl::Def {
            name: "hidden_nat".to_owned(),
            universe_params: vec![],
            ty: nat(),
            value: nat_zero(),
            reducibility: Reducibility::Opaque,
        }],
    });
    let mut imported = verify_module_cert_with_import_refs(
        &encode_module_cert(&imported_cert).unwrap(),
        &[],
        &AxiomPolicy::normal(),
    )
    .unwrap();

    assert!(matches!(
        build_module_cert_from_import_refs_with_preferred_imports(
            imported_opaque_nat_equality_module(),
            &[&imported],
            &std::collections::BTreeMap::new(),
        ),
        Err(CertError::Kernel(npa_kernel::Error::TypeMismatch { .. }))
    ));

    imported.mutate_certificate_parts_for_test(|parts| match &mut parts.declarations[0].decl {
        DeclPayload::Def { value, .. } => *value = usize::MAX,
        _ => panic!("expected opaque definition"),
    });
    assert!(matches!(
        verified_module_to_kernel_decls(&imported).unwrap().as_slice(),
        [Decl::Axiom { name, .. }] if name == "hidden_nat"
    ));
}

#[test]
fn current_module_failed_opaque_body_check_inserts_no_local_view() {
    let mut env = Env::new();
    let bad = Decl::Def {
        name: "bad_hidden".to_owned(),
        universe_params: vec![],
        ty: Expr::sort(Level::succ(Level::zero())),
        value: Expr::sort(Level::succ(Level::zero())),
        reducibility: Reducibility::Opaque,
    };
    assert!(matches!(
        add_current_module_decl_to_env(&mut env, bad, CertificateFormatVersion::V0_4_0),
        Err(CertError::Kernel(npa_kernel::Error::TypeMismatch { .. }))
    ));
    assert!(env.decl("bad_hidden").is_none());
    assert!(!env.expose_checked_opaque_definition("bad_hidden"));
}

#[test]
fn current_module_opaque_view_obeys_conversion_fuel_exhaustion() {
    let mut opaque = Env::new();
    add_current_module_decl_to_env(
        &mut opaque,
        Decl::Def {
            name: "opaque_zero".to_owned(),
            universe_params: vec![],
            ty: Expr::sort(Level::succ(Level::zero())),
            value: Expr::sort(Level::zero()),
            reducibility: Reducibility::Opaque,
        },
        CertificateFormatVersion::V0_4_0,
    )
    .unwrap();
    let mut reducible = Env::new();
    add_decl_to_env(
        &mut reducible,
        Decl::Def {
            name: "reducible_zero".to_owned(),
            universe_params: vec![],
            ty: Expr::sort(Level::succ(Level::zero())),
            value: Expr::sort(Level::zero()),
            reducibility: Reducibility::Reducible,
        },
    )
    .unwrap();

    for (env, name) in [(&opaque, "opaque_zero"), (&reducible, "reducible_zero")] {
        assert_eq!(
            env.is_defeq_with_fuel(
                &Ctx::new(),
                &[],
                &Expr::konst(name, vec![]),
                &Expr::sort(Level::zero()),
                0,
            ),
            Err(npa_kernel::Error::ResourceLimit {
                kind: ResourceLimitKind::Conversion,
            })
        );
    }
}

#[test]
fn opaque_body_check_consumes_same_kernel_work_as_reducible_body() {
    let module = |name: &str, reducibility| CoreModule {
        name: Name::from_dotted(name),
        declarations: vec![Decl::Def {
            name: "checked_value".to_owned(),
            universe_params: vec![],
            ty: Expr::sort(Level::succ(Level::zero())),
            value: Expr::sort(Level::zero()),
            reducibility,
        }],
    };
    let opaque = build_v0_4_cert(module("Test.OpaqueBodyWork", Reducibility::Opaque));
    let reducible = build_v0_4_cert(module("Test.ReducibleBodyWork", Reducibility::Reducible));
    let mut opaque_counters = npa_kernel::KernelWorkCounters::default();
    let mut reducible_counters = npa_kernel::KernelWorkCounters::default();
    verify_module_cert_with_import_refs_and_kernel_options_and_work_counters(
        &encode_module_cert(&opaque).unwrap(),
        &[],
        &AxiomPolicy::normal(),
        npa_kernel::KernelExecutionOptions::memo_off(),
        &mut opaque_counters,
    )
    .unwrap();
    verify_module_cert_with_import_refs_and_kernel_options_and_work_counters(
        &encode_module_cert(&reducible).unwrap(),
        &[],
        &AxiomPolicy::normal(),
        npa_kernel::KernelExecutionOptions::memo_off(),
        &mut reducible_counters,
    )
    .unwrap();

    assert_eq!(opaque_counters.check_calls, reducible_counters.check_calls);
    assert_eq!(opaque_counters.infer_calls, reducible_counters.infer_calls);
    assert_eq!(
        opaque_counters.logical_fuel,
        reducible_counters.logical_fuel
    );
    assert_eq!(
        opaque_counters.exhausted_fuel,
        reducible_counters.exhausted_fuel
    );
}

#[test]
fn current_module_opaque_stale_dependency_evidence_is_rejected() {
    let direct = build_v0_4_cert(opaque_nat_equality_module(nat_zero()));
    let beta_zero = Expr::app(Expr::lam("x", nat(), Expr::bvar(0)), nat_zero());
    let mut changed = build_v0_4_cert(opaque_nat_equality_module(beta_zero));
    let (consumer, dependency_index) = first_local_dependency(&changed);
    let stale_hash = direct.declarations()[decl_index_named(&direct, "hidden_nat")]
        .hashes
        .decl_certificate_hash;
    let dependency = &changed.declarations()[consumer].dependencies[dependency_index];
    let global_ref = dependency.global_ref().clone();
    let interface_hash = dependency.decl_interface_hash();
    replace_first_local_dependency_with_raw_implementation(
        &mut changed,
        global_ref,
        interface_hash,
        stale_hash,
    );
    assert_local_implementation_error(
        &changed,
        LocalImplementationDependencyErrorReason::CertificateHashMismatch,
    );
}

const OPAQUE_DETERMINISM_CHILD_ENV: &str = "NPA_ODS18_OPAQUE_DETERMINISM_CHILD";
const OPAQUE_DETERMINISM_PREFIX: &str = "ODS18_OPAQUE_DETERMINISM=";

fn opaque_determinism_stale_reason(
    bytes: &[u8],
    options: npa_kernel::KernelExecutionOptions,
) -> &'static str {
    match verify_module_cert_with_import_refs_and_kernel_options(
        bytes,
        &[],
        &AxiomPolicy::normal(),
        options,
    ) {
        Err(CertError::InvalidLocalImplementationDependency { reason, .. }) => reason.as_str(),
        Err(error) => panic!("unexpected stale-evidence error: {error:?}"),
        Ok(_) => panic!("stale local implementation evidence must be rejected"),
    }
}

fn opaque_determinism_fuel_result(
    reducibility: Reducibility,
    options: npa_kernel::KernelExecutionOptions,
) -> &'static str {
    let mut env = Env::with_execution_options(options);
    env.add_def(
        "sealed",
        vec![],
        Expr::sort(Level::succ(Level::zero())),
        Expr::sort(Level::zero()),
        reducibility,
    )
    .unwrap();
    match env.is_defeq_with_fuel(
        &Ctx::new(),
        &[],
        &Expr::konst("sealed", vec![]),
        &Expr::sort(Level::zero()),
        0,
    ) {
        Err(npa_kernel::Error::ResourceLimit {
            kind: ResourceLimitKind::Conversion,
        }) => "conversion_fuel_exhausted",
        other => panic!("zero-fuel conversion must fail closed, got {other:?}"),
    }
}

fn opaque_determinism_snapshot() -> String {
    let canonical_cert_a = build_v0_4_cert(opaque_alias_chain_module());
    let canonical_cert_b = build_v0_4_cert(opaque_alias_chain_module());
    let canonical_hash = hash_hex(canonical_cert_a.hashes().certificate_hash);
    let canonical_a = encode_module_cert(&canonical_cert_a).unwrap();
    let canonical_b = encode_module_cert(&canonical_cert_b).unwrap();
    assert_eq!(
        canonical_a, canonical_b,
        "identical opaque source modules must have identical canonical certificates"
    );

    let direct = build_v0_4_cert(opaque_nat_equality_module(nat_zero()));
    let beta_zero = Expr::app(Expr::lam("x", nat(), Expr::bvar(0)), nat_zero());
    let mut changed = build_v0_4_cert(opaque_nat_equality_module(beta_zero));
    let (consumer, dependency_index) = first_local_dependency(&changed);
    let stale_hash = direct.declarations()[decl_index_named(&direct, "hidden_nat")]
        .hashes
        .decl_certificate_hash;
    let dependency = &changed.declarations()[consumer].dependencies[dependency_index];
    let global_ref = dependency.global_ref().clone();
    let interface_hash = dependency.decl_interface_hash();
    replace_first_local_dependency_with_raw_implementation(
        &mut changed,
        global_ref,
        interface_hash,
        stale_hash,
    );
    let stale_bytes = encode_module_cert(&changed).unwrap();
    let stale_hash = hash_hex(changed.hashes().certificate_hash);

    let off_reason = opaque_determinism_stale_reason(
        &stale_bytes,
        npa_kernel::KernelExecutionOptions::memo_off(),
    );
    let memo_reason = opaque_determinism_stale_reason(
        &stale_bytes,
        npa_kernel::KernelExecutionOptions::ephemeral_memo(),
    );
    assert_eq!(off_reason, "certificate_hash_mismatch");
    assert_eq!(memo_reason, off_reason);

    let opaque_fuel_off = opaque_determinism_fuel_result(
        Reducibility::Opaque,
        npa_kernel::KernelExecutionOptions::memo_off(),
    );
    let reducible_fuel_off = opaque_determinism_fuel_result(
        Reducibility::Reducible,
        npa_kernel::KernelExecutionOptions::memo_off(),
    );
    let opaque_fuel_memo = opaque_determinism_fuel_result(
        Reducibility::Opaque,
        npa_kernel::KernelExecutionOptions::ephemeral_memo(),
    );
    let reducible_fuel_memo = opaque_determinism_fuel_result(
        Reducibility::Reducible,
        npa_kernel::KernelExecutionOptions::ephemeral_memo(),
    );
    assert_eq!(opaque_fuel_off, reducible_fuel_off);
    assert_eq!(opaque_fuel_memo, opaque_fuel_off);
    assert_eq!(reducible_fuel_memo, opaque_fuel_off);

    format!(
        "canonical_bytes={};canonical_hash={canonical_hash};stale_hash={stale_hash};stale_memo_off={off_reason};stale_ephemeral_memo={memo_reason};opaque_fuel_off={opaque_fuel_off};reducible_fuel_off={reducible_fuel_off};opaque_fuel_memo={opaque_fuel_memo};reducible_fuel_memo={reducible_fuel_memo}",
        canonical_a.len()
    )
}

fn opaque_determinism_child_snapshot() -> String {
    let output = Command::new(std::env::current_exe().expect("test executable must exist"))
        .arg("--exact")
        .arg("tests::opaque_definition_determinism_is_stable_across_fresh_processes")
        .arg("--nocapture")
        .env(OPAQUE_DETERMINISM_CHILD_ENV, "1")
        .output()
        .expect("fresh determinism fixture process must start");
    assert!(
        output.status.success(),
        "fresh determinism fixture process failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout)
        .expect("determinism fixture stdout must be UTF-8")
        .lines()
        .find_map(|line| {
            line.strip_prefix(OPAQUE_DETERMINISM_PREFIX)
                .map(str::to_owned)
        })
        .expect("fresh determinism fixture must emit its trusted snapshot")
}

#[test]
fn opaque_definition_determinism_is_stable_across_fresh_processes() {
    if std::env::var_os(OPAQUE_DETERMINISM_CHILD_ENV).is_some() {
        println!(
            "{OPAQUE_DETERMINISM_PREFIX}{}",
            opaque_determinism_snapshot()
        );
        return;
    }

    let first = opaque_determinism_child_snapshot();
    let second = opaque_determinism_child_snapshot();
    assert_eq!(
        first, second,
        "opaque stale-cache and fuel evidence must be stable across fresh processes"
    );
}

#[test]
fn local_transparency_direct_dependency_matches_producer_and_verifier() {
    let cert = v0_4_opaque_alias_cert_with_local_implementation_dependency();
    let hidden = decl_index_named(&cert, "opaque_id");
    let alias = decl_index_named(&cert, "opaque_id_alias");

    assert_eq!(local_implementation_targets(&cert, alias), [hidden].into());
    for (decl_index, declaration) in cert.declarations().iter().enumerate() {
        assert_eq!(
            declaration.dependencies,
            expected_dependencies_for_decl(&cert, &[], decl_index, &declaration.decl).unwrap()
        );
    }
    verify_module_cert_with_import_refs(
        &encode_module_cert(&cert).unwrap(),
        &[],
        &AxiomPolicy::normal(),
    )
    .unwrap();
}

#[test]
fn local_transparency_alias_chain_propagates_existing_reducible_body_path() {
    let cert = build_v0_4_cert(opaque_alias_chain_module());
    let hidden = decl_index_named(&cert, "hidden");
    let alias = decl_index_named(&cert, "alias");
    let uses_alias = decl_index_named(&cert, "uses_alias");

    assert_eq!(local_implementation_targets(&cert, alias), [hidden].into());
    assert_eq!(
        local_implementation_targets(&cert, uses_alias),
        [hidden].into()
    );
    assert!(cert.declarations()[uses_alias]
        .dependencies
        .iter()
        .any(|dependency| {
            dependency.kind() == DependencyEntryKind::Interface
                && matches!(
                    dependency.global_ref(),
                    GlobalRef::Local { decl_index } if *decl_index == alias
                )
        }));
    assert_eq!(
        cert.declarations()[uses_alias].dependencies,
        expected_dependencies_for_decl(
            &cert,
            &[],
            uses_alias,
            &cert.declarations()[uses_alias].decl,
        )
        .unwrap()
    );
}

#[test]
fn local_transparency_follows_referenced_declared_type() {
    let cert = build_v0_4_cert(opaque_declared_type_module());
    let hidden_type = decl_index_named(&cert, "hidden_type");
    let hidden_witness = decl_index_named(&cert, "hidden_witness");
    let uses_witness = decl_index_named(&cert, "uses_witness_type");

    assert_eq!(
        local_implementation_targets(&cert, hidden_witness),
        [hidden_type].into()
    );
    assert_eq!(
        local_implementation_targets(&cert, uses_witness),
        [hidden_type].into()
    );
    assert!(cert.declarations()[uses_witness]
        .dependencies
        .iter()
        .any(|dependency| {
            dependency.kind() == DependencyEntryKind::Interface
                && matches!(
                    dependency.global_ref(),
                    GlobalRef::Local { decl_index } if *decl_index == hidden_witness
                )
        }));
}

#[test]
fn local_transparency_nested_opaque_bodies_propagate_all_reached_targets() {
    let cert = build_v0_4_cert(nested_opaque_module());
    let inner = decl_index_named(&cert, "inner_hidden");
    let outer = decl_index_named(&cert, "outer_hidden");
    let consumer = decl_index_named(&cert, "uses_outer");

    assert_eq!(local_implementation_targets(&cert, outer), [inner].into());
    assert_eq!(
        local_implementation_targets(&cert, consumer),
        [inner, outer].into()
    );
}

#[test]
fn local_transparency_stops_at_referenced_theorem_proof() {
    let direct = build_v0_4_cert(theorem_interface_only_module(id_value("A", "x")));
    let changed = build_v0_4_cert(theorem_interface_only_module(id_value_with_beta_redex()));
    let hidden = decl_index_named(&direct, "hidden");
    let theorem = decl_index_named(&direct, "stable_theorem");
    let consumer = decl_index_named(&direct, "uses_stable_theorem");

    assert_eq!(
        local_implementation_targets(&direct, theorem),
        [hidden].into()
    );
    assert!(local_implementation_targets(&direct, consumer).is_empty());
    assert_eq!(
        dependency_selective_fingerprint_canonical_bytes(
            &direct.declarations()[consumer].dependencies,
        ),
        dependency_selective_fingerprint_canonical_bytes(
            &changed.declarations()[consumer].dependencies,
        )
    );
    assert_eq!(
        direct.declarations()[consumer].hashes.decl_certificate_hash,
        changed.declarations()[consumer]
            .hashes
            .decl_certificate_hash
    );
    assert_ne!(
        direct.declarations()[theorem].hashes.decl_certificate_hash,
        changed.declarations()[theorem].hashes.decl_certificate_hash
    );
}

#[test]
fn local_transparency_stops_at_imported_opaque_body() {
    let imported_cert = build_v0_4_cert(CoreModule {
        name: Name::from_dotted("Test.ImportedOpaque"),
        declarations: vec![named_opaque_id("imported_hidden", id_value("A", "x"))],
    });
    let imported = verify_module_cert_with_import_refs(
        &encode_module_cert(&imported_cert).unwrap(),
        &[],
        &AxiomPolicy::normal(),
    )
    .unwrap();
    let cert = build_module_cert_from_import_refs_with_preferred_imports(
        CoreModule {
            name: Name::from_dotted("Test.UseImportedOpaque"),
            declarations: vec![named_id_alias(
                "use_imported_hidden",
                "imported_hidden",
                Reducibility::Reducible,
            )],
        },
        &[&imported],
        &std::collections::BTreeMap::new(),
    )
    .unwrap();

    assert!(local_implementation_targets(&cert, 0).is_empty());
    assert!(cert.declarations()[0]
        .dependencies
        .iter()
        .all(|dependency| dependency.kind() == DependencyEntryKind::Interface));
    verify_module_cert_with_import_refs(
        &encode_module_cert(&cert).unwrap(),
        &[&imported],
        &AxiomPolicy::normal(),
    )
    .unwrap();
}

#[test]
fn local_transparency_dependency_selective_fingerprint_commits_only_reached_bodies() {
    let mut changed_module = opaque_alias_chain_module();
    match &mut changed_module.declarations[0] {
        Decl::Def { value, .. } => *value = id_value_with_beta_redex(),
        _ => panic!("expected opaque definition"),
    }
    let direct = build_v0_4_cert(opaque_alias_chain_module());
    let changed = build_v0_4_cert(changed_module);
    let consumer = decl_index_named(&direct, "uses_alias");
    let direct_fingerprint = dependency_selective_fingerprint_canonical_bytes(
        &direct.declarations()[consumer].dependencies,
    );
    let changed_fingerprint = dependency_selective_fingerprint_canonical_bytes(
        &changed.declarations()[consumer].dependencies,
    );

    assert_ne!(direct_fingerprint, changed_fingerprint);
    let mut reversed = direct.declarations()[consumer].dependencies.clone();
    reversed.reverse();
    assert_eq!(
        direct_fingerprint,
        dependency_selective_fingerprint_canonical_bytes(&reversed)
    );
}

#[test]
fn local_transparency_declaration_order_uses_paths_without_bare_source_authority() {
    let declarations = vec![
        named_id_theorem("uses_alias", "alias"),
        named_id_alias("alias", "hidden", Reducibility::Reducible),
        named_opaque_id("hidden", id_value("A", "x")),
        named_opaque_id("aaa_unrelated", id_value("A", "x")),
    ];
    let cert = build_v0_4_cert(CoreModule {
        name: Name::from_dotted("Test.OpaqueOrdering"),
        declarations: declarations.clone(),
    });
    let reordered = build_v0_4_cert(CoreModule {
        name: Name::from_dotted("Test.OpaqueOrdering"),
        declarations: declarations.into_iter().rev().collect(),
    });
    let names = cert
        .declarations()
        .iter()
        .map(|declaration| {
            let name = match declaration.decl {
                DeclPayload::Def { name, .. } | DeclPayload::Theorem { name, .. } => name,
                _ => panic!("expected definition or theorem"),
            };
            cert.name_table()[name].clone()
        })
        .collect::<Vec<_>>();
    assert_eq!(
        names,
        ["aaa_unrelated", "hidden", "alias", "uses_alias"]
            .map(Name::from_dotted)
            .to_vec()
    );
    assert_eq!(cert, reordered);
    let unrelated = decl_index_named(&cert, "aaa_unrelated");
    let hidden = decl_index_named(&cert, "hidden");
    let consumer = decl_index_named(&cert, "uses_alias");
    assert_eq!(
        local_implementation_targets(&cert, consumer),
        [hidden].into()
    );
    assert!(!local_implementation_targets(&cert, consumer).contains(&unrelated));
}

#[test]
fn local_transparency_wrong_reference_kinds_use_fixed_reason() {
    let base = v0_4_opaque_alias_cert_with_local_implementation_dependency();
    let (consumer, dependency_index) = first_local_dependency(&base);
    let dependency = &base.declarations()[consumer].dependencies[dependency_index];
    let interface_hash = dependency.decl_interface_hash();
    let certificate_hash = dependency.decl_certificate_hash().unwrap();
    let target = match dependency.global_ref() {
        GlobalRef::Local { decl_index } => *decl_index,
        _ => unreachable!(),
    };
    for global_ref in [
        GlobalRef::Builtin {
            name: 0,
            decl_interface_hash: interface_hash,
        },
        GlobalRef::Imported {
            import_index: 0,
            name: 0,
            decl_interface_hash: interface_hash,
        },
        GlobalRef::LocalGenerated {
            decl_index: target,
            name: 0,
        },
    ] {
        let mut cert = base.clone();
        replace_first_local_dependency_with_raw_implementation(
            &mut cert,
            global_ref,
            interface_hash,
            certificate_hash,
        );
        assert_local_implementation_error(
            &cert,
            LocalImplementationDependencyErrorReason::WrongReferenceKind,
        );
    }
}

#[test]
fn local_transparency_non_earlier_targets_use_fixed_reason() {
    let base = v0_4_opaque_alias_cert_with_local_implementation_dependency();
    let (consumer, dependency_index) = first_local_dependency(&base);
    let dependency = &base.declarations()[consumer].dependencies[dependency_index];
    for target in [consumer, base.declarations().len() + 7] {
        let mut cert = base.clone();
        replace_first_local_dependency_with_raw_implementation(
            &mut cert,
            GlobalRef::Local { decl_index: target },
            dependency.decl_interface_hash(),
            dependency.decl_certificate_hash().unwrap(),
        );
        assert_local_implementation_error(
            &cert,
            LocalImplementationDependencyErrorReason::TargetNotEarlier,
        );
    }

    let mut later = build_v0_4_cert(nested_opaque_module());
    let current = decl_index_named(&later, "outer_hidden");
    let later_target = decl_index_named(&later, "uses_outer");
    let dependency_index = later.declarations()[current]
        .dependencies
        .iter()
        .position(|dependency| dependency.kind() == DependencyEntryKind::LocalImplementation)
        .unwrap();
    let dependency = &later.declarations()[current].dependencies[dependency_index];
    let interface_hash = dependency.decl_interface_hash();
    let certificate_hash = dependency.decl_certificate_hash().unwrap();
    later.mutate_parts_for_test(|parts| {
        parts.declarations[current].dependencies[dependency_index] =
            DependencyEntry::from_decoded_local_implementation(
                GlobalRef::Local {
                    decl_index: later_target,
                },
                interface_hash,
                certificate_hash,
            );
        parts.declarations[current].dependencies.sort();
    });
    rehash_v0_4_dependency_change(&mut later, current);
    assert_local_implementation_error(
        &later,
        LocalImplementationDependencyErrorReason::TargetNotEarlier,
    );
}

#[test]
fn local_transparency_error_reason_vocabulary_is_exact() {
    let cases = [
        (
            LocalImplementationDependencyErrorReason::WrongReferenceKind,
            "wrong_reference_kind",
        ),
        (
            LocalImplementationDependencyErrorReason::TargetNotEarlier,
            "target_not_earlier",
        ),
        (
            LocalImplementationDependencyErrorReason::TargetNotOpaque,
            "target_not_opaque",
        ),
        (
            LocalImplementationDependencyErrorReason::InterfaceHashMismatch,
            "interface_hash_mismatch",
        ),
        (
            LocalImplementationDependencyErrorReason::CertificateHashMismatch,
            "certificate_hash_mismatch",
        ),
        (
            LocalImplementationDependencyErrorReason::MissingImplementationDependency,
            "missing_implementation_dependency",
        ),
        (
            LocalImplementationDependencyErrorReason::SurplusImplementationDependency,
            "surplus_implementation_dependency",
        ),
    ];
    for (reason, expected) in cases {
        assert_eq!(reason.as_str(), expected);
    }
}

#[test]
fn local_transparency_non_opaque_target_uses_fixed_reason() {
    let mut cert = build_v0_4_cert(CoreModule {
        name: Name::from_dotted("Test.NonOpaqueImplementation"),
        declarations: vec![
            Decl::Def {
                name: "plain".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: id_type("A", "x"),
                value: id_value("A", "x"),
                reducibility: Reducibility::Reducible,
            },
            named_id_alias("uses_plain", "plain", Reducibility::Reducible),
        ],
    });
    let target = decl_index_named(&cert, "plain");
    let consumer = decl_index_named(&cert, "uses_plain");
    let target_hashes = cert.declarations()[target].hashes.clone();
    let dependency_index = cert.declarations()[consumer]
        .dependencies
        .iter()
        .position(|dependency| {
            matches!(
                dependency.global_ref(),
                GlobalRef::Local { decl_index } if *decl_index == target
            )
        })
        .unwrap();
    cert.mutate_parts_for_test(|parts| {
        parts.declarations[consumer].dependencies[dependency_index] =
            DependencyEntry::from_decoded_local_implementation(
                GlobalRef::Local { decl_index: target },
                target_hashes.decl_interface_hash,
                target_hashes.decl_certificate_hash,
            );
        parts.declarations[consumer].dependencies.sort();
    });
    rehash_v0_4_dependency_change(&mut cert, consumer);
    assert_local_implementation_error(
        &cert,
        LocalImplementationDependencyErrorReason::TargetNotOpaque,
    );
}

#[test]
fn local_transparency_forged_hashes_use_fixed_reasons() {
    let base = v0_4_opaque_alias_cert_with_local_implementation_dependency();
    let (consumer, dependency_index) = first_local_dependency(&base);
    let dependency = &base.declarations()[consumer].dependencies[dependency_index];
    let global_ref = dependency.global_ref().clone();
    let interface_hash = dependency.decl_interface_hash();
    let certificate_hash = dependency.decl_certificate_hash().unwrap();

    let mut forged_interface = interface_hash;
    forged_interface[0] ^= 0x01;
    let mut cert = base.clone();
    replace_first_local_dependency_with_raw_implementation(
        &mut cert,
        global_ref.clone(),
        forged_interface,
        certificate_hash,
    );
    assert_local_implementation_error(
        &cert,
        LocalImplementationDependencyErrorReason::InterfaceHashMismatch,
    );

    let mut forged_certificate = certificate_hash;
    forged_certificate[0] ^= 0x01;
    let mut cert = base;
    replace_first_local_dependency_with_raw_implementation(
        &mut cert,
        global_ref,
        interface_hash,
        forged_certificate,
    );
    assert_local_implementation_error(
        &cert,
        LocalImplementationDependencyErrorReason::CertificateHashMismatch,
    );
}

#[test]
fn local_transparency_missing_and_surplus_entries_use_fixed_reasons() {
    let missing = v0_4_opaque_alias_cert_with_interface_dependency();
    assert_local_implementation_error(
        &missing,
        LocalImplementationDependencyErrorReason::MissingImplementationDependency,
    );

    let mut surplus = build_v0_4_cert(CoreModule {
        name: Name::from_dotted("Test.SurplusImplementation"),
        declarations: vec![
            named_opaque_id("a_unrelated_hidden", id_value("A", "x")),
            Decl::Def {
                name: "z_independent".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: id_type("A", "x"),
                value: id_value("A", "x"),
                reducibility: Reducibility::Reducible,
            },
        ],
    });
    let target = decl_index_named(&surplus, "a_unrelated_hidden");
    let consumer = decl_index_named(&surplus, "z_independent");
    let implementation = DependencyEntry::checked_local_implementation(
        GlobalRef::Local { decl_index: target },
        consumer,
        surplus.declarations(),
    )
    .unwrap();
    surplus.mutate_parts_for_test(|parts| {
        parts.declarations[consumer]
            .dependencies
            .push(implementation);
        parts.declarations[consumer].dependencies.sort();
    });
    rehash_v0_4_dependency_change(&mut surplus, consumer);
    assert_local_implementation_error(
        &surplus,
        LocalImplementationDependencyErrorReason::SurplusImplementationDependency,
    );
}

#[test]
fn local_transparency_source_cycle_remains_rejected() {
    let err = build_module_cert_from_import_refs_with_preferred_imports(
        CoreModule {
            name: Name::from_dotted("Test.OpaqueCycle"),
            declarations: vec![
                named_id_alias("cycle_a", "cycle_b", Reducibility::Reducible),
                named_id_alias("cycle_b", "cycle_a", Reducibility::Reducible),
            ],
        },
        &[],
        &std::collections::BTreeMap::new(),
    )
    .unwrap_err();
    assert!(matches!(err, CertError::DependencyCycle { .. }));
}

#[test]
fn binary_v0_4_local_implementation_dependency_round_trips_with_complete_payload() {
    let cert = v0_4_opaque_alias_cert_with_local_implementation_dependency();
    let dependency = cert
        .declarations()
        .iter()
        .flat_map(|decl| &decl.dependencies)
        .find(|dependency| dependency.kind() == DependencyEntryKind::LocalImplementation)
        .unwrap();
    assert!(dependency.decl_certificate_hash().is_some());

    let bytes = encode_module_cert(&cert).unwrap();
    let decoded = decode_module_cert(&bytes).unwrap();
    assert_eq!(decoded, cert);
    assert_eq!(encode_module_cert(&decoded).unwrap(), bytes);
}

#[test]
fn binary_dependency_checked_constructors_enforce_hash_and_earlier_opaque_target() {
    let mismatched_interface = DependencyEntry::checked_interface(
        GlobalRef::Imported {
            import_index: 0,
            name: 0,
            decl_interface_hash: [1; 32],
        },
        [2; 32],
    );
    assert!(matches!(
        mismatched_interface,
        Err(CertError::HashMismatch {
            object: HashObject::DeclInterface,
            ..
        })
    ));

    let opaque = v0_4_opaque_alias_cert_with_interface_dependency();
    let (alias_index, target_ref) = opaque
        .declarations()
        .iter()
        .enumerate()
        .find_map(|(decl_index, decl)| {
            decl.dependencies.iter().find_map(|dependency| {
                matches!(dependency.global_ref(), GlobalRef::Local { .. })
                    .then(|| (decl_index, dependency.global_ref().clone()))
            })
        })
        .unwrap();
    let accepted = DependencyEntry::checked_local_implementation(
        target_ref.clone(),
        alias_index,
        opaque.declarations(),
    )
    .unwrap();
    assert_eq!(accepted.kind(), DependencyEntryKind::LocalImplementation);

    assert!(matches!(
        DependencyEntry::checked_local_implementation(target_ref, 0, opaque.declarations(),),
        Err(CertError::DependencyCycle { .. })
    ));
    assert!(matches!(
        DependencyEntry::checked_local_implementation(
            GlobalRef::Builtin {
                name: 0,
                decl_interface_hash: [0; 32],
            },
            alias_index,
            opaque.declarations(),
        ),
        Err(CertError::DecodeError)
    ));

    let reducible = build_module_cert(id_module("A", "x"), &[]).unwrap();
    assert!(matches!(
        DependencyEntry::checked_local_implementation(
            GlobalRef::Local { decl_index: 0 },
            1,
            reducible.declarations(),
        ),
        Err(CertError::DecodeError)
    ));
}

#[test]
fn binary_v0_4_dependency_rejects_truncation_and_unknown_tag() {
    let cert = v0_4_opaque_alias_cert_with_local_implementation_dependency();
    let dependency = cert
        .declarations()
        .iter()
        .flat_map(|decl| &decl.dependencies)
        .find(|dependency| dependency.kind() == DependencyEntryKind::LocalImplementation)
        .unwrap();
    let dependency_bytes = v0_4_dependency_bytes(dependency);
    let bytes = encode_module_cert(&cert).unwrap();
    let dependency_offset = bytes
        .windows(dependency_bytes.len())
        .position(|window| window == dependency_bytes)
        .unwrap();

    let truncated = &bytes[..dependency_offset + dependency_bytes.len() - 1];
    assert!(decode_module_cert(truncated).is_err());

    let mut unknown_tag = bytes;
    unknown_tag[dependency_offset] = 0x7f;
    assert!(matches!(
        decode_module_cert(&unknown_tag),
        Err(CertError::UnsupportedEncoding { tag: 0x7f })
    ));
}

#[test]
fn certificate_format_old_pair_rejects_before_term_decoding() {
    let cert = v0_4_opaque_alias_cert_with_local_implementation_dependency();
    let mut bytes = encode_module_cert(&cert).unwrap();
    let term_offset = term_tag_offsets(&bytes)[0];
    bytes[term_offset] = 0x06;
    let core_spec_offset = bytes
        .windows(CORE_SPEC.len())
        .position(|window| window == CORE_SPEC.as_bytes())
        .unwrap();
    let old_core_spec = "NPA-Core-0.3.0";
    bytes[core_spec_offset..core_spec_offset + old_core_spec.len()]
        .copy_from_slice(old_core_spec.as_bytes());

    assert!(matches!(
        decode_module_cert(&bytes),
        Err(CertError::UnsupportedFormat { format, core_spec })
            if format == FORMAT && core_spec == old_core_spec
    ));
}

#[test]
fn certificate_format_header_only_downgrade_cannot_erase_local_implementation_commitment() {
    let mut cert = v0_4_opaque_alias_cert_with_local_implementation_dependency();
    cert.mutate_parts_for_test(|parts| {
        parts.header.format = "NPA-CERT-0.3.0".to_owned();
        parts.header.core_spec = "NPA-Core-0.3.0".to_owned();
    });
    assert!(matches!(
        encode_module_cert(&cert),
        Err(CertError::UnsupportedFormat { .. })
    ));
}

#[test]
fn certificate_format_accepts_only_exact_known_pairs() {
    let rows = v0_4_fixture_rows("header");
    assert_eq!(rows.len(), 28);
    for fields in rows {
        let case_id = fields[0];
        let format = fields[3];
        let core_spec = fields[4];
        let expected = fields[6];
        let result = certificate_format_version(&CertHeader {
            format: format.to_owned(),
            core_spec: core_spec.to_owned(),
            module: Name::from_dotted("Test.HeaderMatrix"),
        });
        if expected == "checked" {
            assert_eq!(result, Ok(CertificateFormatVersion::V0_4_0), "{case_id}");
            assert_eq!((format, core_spec), (FORMAT, CORE_SPEC), "{case_id}");
        } else {
            assert_eq!(expected, "unsupported_format", "{case_id}");
            assert!(
                matches!(result, Err(CertError::UnsupportedFormat { .. })),
                "{case_id}: {result:?}"
            );
        }
    }
}

#[test]
fn v0_4_fixture_matrix_is_complete_and_has_closed_result_vocabularies() {
    let rows = v0_4_fixture_matrix_rows();
    assert_eq!(rows.len(), 72);
    let mut case_ids = BTreeSet::new();
    let mut classes = BTreeMap::new();
    for fields in rows {
        assert!(
            case_ids.insert(fields[0]),
            "duplicate case id: {}",
            fields[0]
        );
        *classes.entry(fields[1]).or_insert(0usize) += 1;
        let normalized = fields.join("\t").to_ascii_lowercase();
        for forbidden in ["todo", "skip", "ignore", "expected-failure"] {
            assert!(
                !normalized.contains(forbidden),
                "{} contains forbidden marker {forbidden}",
                fields[0]
            );
        }
        if fields[1].starts_with("source_") {
            assert_eq!(fields[7], "not_applicable", "{}", fields[0]);
            assert_eq!(fields[8], "not_applicable", "{}", fields[0]);
        } else {
            assert_ne!(fields[6], "not_applicable", "{}", fields[0]);
            assert_ne!(fields[7], "not_applicable", "{}", fields[0]);
            assert_ne!(fields[8], "not_applicable", "{}", fields[0]);
        }
    }
    assert_eq!(
        classes,
        BTreeMap::from([
            ("closure_rejection", 3),
            ("hash", 10),
            ("hash_rejection", 3),
            ("header", 28),
            ("positive_semantics", 3),
            ("positive_structure", 2),
            ("positive_term", 6),
            ("retired_tag", 6),
            ("source_positive", 6),
            ("source_rejection", 5),
        ])
    );
}

#[test]
fn binary_v0_4_dependency_order_and_duplicates_are_rejected() {
    let mut cert = v0_4_opaque_alias_cert_with_interface_dependency();
    let (decl_index, dependency_index) = cert
        .declarations()
        .iter()
        .enumerate()
        .find_map(|(decl_index, decl)| {
            decl.dependencies
                .iter()
                .position(|dependency| matches!(dependency.global_ref(), GlobalRef::Local { .. }))
                .map(|dependency_index| (decl_index, dependency_index))
        })
        .unwrap();
    let interface = cert.declarations()[decl_index].dependencies[dependency_index].clone();
    let implementation = DependencyEntry::checked_local_implementation(
        interface.global_ref().clone(),
        decl_index,
        cert.declarations(),
    )
    .unwrap();
    assert!(interface < implementation);

    cert.mutate_parts_for_test(|parts| {
        parts.declarations[decl_index].dependencies = vec![implementation, interface.clone()];
    });
    assert!(matches!(
        decode_module_cert(&encode_module_cert(&cert).unwrap()),
        Err(CertError::NonCanonicalEncoding {
            object: "Dependencies"
        })
    ));

    cert.mutate_parts_for_test(|parts| {
        parts.declarations[decl_index].dependencies = vec![interface.clone(), interface];
    });
    assert!(matches!(
        decode_module_cert(&encode_module_cert(&cert).unwrap()),
        Err(CertError::NonCanonicalEncoding {
            object: "Dependencies"
        })
    ));
}

#[test]
fn structural_v0_4_local_implementation_counts_added_certificate_hash_bytes() {
    let interface_cert = v0_4_opaque_alias_cert_with_interface_dependency();
    let implementation_cert = v0_4_opaque_alias_cert_with_local_implementation_dependency();
    let interface_bytes = encode_module_cert(&interface_cert).unwrap();
    let implementation_bytes = encode_module_cert(&implementation_cert).unwrap();
    assert_eq!(implementation_bytes.len(), interface_bytes.len() + 32);

    let interface_audit = audit_certificate_structural_limits(&interface_bytes).unwrap();
    let implementation_audit = audit_certificate_structural_limits(&implementation_bytes).unwrap();
    assert_eq!(interface_audit.certificate_bytes, interface_bytes.len());
    assert_eq!(
        implementation_audit.certificate_bytes,
        implementation_bytes.len()
    );
    assert_eq!(
        implementation_audit.nested_vector_entries,
        interface_audit.nested_vector_entries
    );
}

#[test]
fn universe_constraints_fast_verifier_accepts_canonical_constraint_bytes() {
    let cert = build_module_cert(
        constrained_axiom_module(height_order_regression_constraints()),
        &[],
    )
    .unwrap();
    assert!(matches!(
        cert.declarations()[0].decl,
        DeclPayload::AxiomConstrained { .. }
    ));
    let bytes = encode_module_cert(&cert).unwrap();
    let mut session = VerifierSession::new();
    verify_module_cert(&bytes, &mut session, &AxiomPolicy::normal()).unwrap();
}

#[test]
fn universe_constraints_producer_rejects_unsatisfiable_context() {
    let err = build_module_cert(constrained_axiom_module(vec![succ_u_le_u()]), &[]).unwrap_err();

    assert!(matches!(
        err,
        CertError::Kernel(npa_kernel::Error::UnsatisfiableUniverseConstraints)
    ));
}

#[test]
fn universe_meta_param_fixture_rejected_by_fast_verifier() {
    let bytes = universe_meta_param_certificate_bytes();
    let err = verify_module_cert(&bytes, &mut VerifierSession::new(), &AxiomPolicy::normal())
        .unwrap_err();

    assert!(matches!(
        err,
        CertError::NonCanonicalEncoding { object: "Name" }
    ));
}

#[test]
fn universe_constraints_fast_verifier_rejects_empty_constrained_payload() {
    let mut cert = build_module_cert(constrained_axiom_module(vec![]), &[]).unwrap();
    let DeclPayload::Axiom {
        name,
        universe_params,
        ty,
    } = cert.declarations()[0].decl.clone()
    else {
        panic!("expected unconstrained axiom payload");
    };
    cert.mutate_parts_for_test(|parts| {
        parts.declarations[0].decl = DeclPayload::AxiomConstrained {
            name,
            universe_params,
            universe_constraints: Vec::new(),
            ty,
        };
    });
    let bytes = encode_module_cert(&cert).unwrap();
    let err = verify_module_cert(&bytes, &mut VerifierSession::new(), &AxiomPolicy::normal())
        .unwrap_err();
    assert!(matches!(
        err,
        CertError::NonCanonicalEncoding {
            object: "UniverseConstraints"
        }
    ));
}

fn nat_module() -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Std.Nat.Basic"),
        declarations: vec![Decl::Inductive {
            name: "Nat".to_owned(),
            universe_params: vec![],
            ty: Expr::sort(type0()),
            data: Box::new(nat_inductive()),
        }],
    }
}

fn eq_module() -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Std.Logic.Eq"),
        declarations: vec![Decl::Inductive {
            name: "Eq".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: Expr::pi(
                "A",
                Expr::sort(Level::param("u")),
                Expr::pi(
                    "lhs",
                    Expr::bvar(0),
                    Expr::pi("rhs", Expr::bvar(1), Expr::sort(Level::zero())),
                ),
            ),
            data: Box::new(eq_inductive()),
        }],
    }
}

fn eq_axiom_module_without_rec() -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Std.Logic.EqShape"),
        declarations: vec![
            Decl::Axiom {
                name: "Eq".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: Expr::pi(
                    "A",
                    Expr::sort(Level::param("u")),
                    Expr::pi(
                        "lhs",
                        Expr::bvar(0),
                        Expr::pi("rhs", Expr::bvar(1), Expr::sort(Level::zero())),
                    ),
                ),
            },
            Decl::Axiom {
                name: "Eq.refl".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: eq_refl_type(Level::param("u")),
            },
        ],
    }
}

fn use_builtin_eq_rec_with_imported_eq_module() -> CoreModule {
    let u = Level::param("u");
    let v = Level::param("v");
    CoreModule {
        name: Name::from_dotted("Test.UseBuiltinEqRecWithImportedEq"),
        declarations: vec![Decl::Theorem {
            name: "use_builtin_eq_rec_with_imported_eq".to_owned(),
            universe_params: vec!["u".to_owned(), "v".to_owned()],
            ty: eq_rec_type(u.clone(), v.clone()),
            proof: Expr::konst("Eq.rec", vec![u, v]),
        }],
    }
}

fn nat_add_type() -> Expr {
    Expr::pi("n", nat(), Expr::pi("m", nat(), nat()))
}

fn nat_add_value() -> Expr {
    let motive = Expr::lam("_", nat(), nat());
    let step = Expr::lam("_", nat(), Expr::lam("ih", nat(), nat_succ(Expr::bvar(0))));
    let rec = Expr::apps(
        Expr::konst("Nat.rec", vec![type0()]),
        vec![motive, Expr::bvar(1), step, Expr::bvar(0)],
    );
    Expr::lam("n", nat(), Expr::lam("m", nat(), rec))
}

fn nat_add_module() -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Std.Nat.Add"),
        declarations: vec![Decl::Def {
            name: "Nat.add".to_owned(),
            universe_params: vec![],
            ty: nat_add_type(),
            value: nat_add_value(),
            reducibility: Reducibility::Reducible,
        }],
    }
}

fn add_zero_type() -> Expr {
    let add_n_zero = Expr::apps(
        Expr::konst("Nat.add", vec![]),
        vec![Expr::bvar(0), nat_zero()],
    );
    Expr::pi("n", nat(), eq(type0(), nat(), add_n_zero, Expr::bvar(0)))
}

fn add_zero_value() -> Expr {
    Expr::lam("n", nat(), eq_refl(type0(), nat(), Expr::bvar(0)))
}

fn add_zero_module() -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Std.Nat.AddZero"),
        declarations: vec![Decl::Theorem {
            name: "Nat.add_zero".to_owned(),
            universe_params: vec![],
            ty: add_zero_type(),
            proof: add_zero_value(),
        }],
    }
}

fn id_theorem_module(proof: Expr) -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Test.IdTheorem"),
        declarations: vec![Decl::Theorem {
            name: "id_thm".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: id_type("A", "x"),
            proof,
        }],
    }
}

fn two_id_theorems_module() -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Test.TwoIdTheorems"),
        declarations: vec![
            Decl::Theorem {
                name: "id_thm_a".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: id_type("A", "x"),
                proof: id_value("A", "x"),
            },
            Decl::Theorem {
                name: "id_thm_b".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: id_type("A", "x"),
                proof: id_value("A", "x"),
            },
        ],
    }
}

fn use_id_module() -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Test.UseId"),
        declarations: vec![Decl::Def {
            name: "use_id".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: id_type("A", "x"),
            value: Expr::konst("id", vec![Level::param("u")]),
            reducibility: Reducibility::Reducible,
        }],
    }
}

fn local_transparent_alias_module(base_value: Expr) -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Test.LocalTransparentAlias"),
        declarations: vec![
            Decl::Def {
                name: "base".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: id_type("A", "x"),
                value: base_value,
                reducibility: Reducibility::Reducible,
            },
            Decl::Def {
                name: "alias".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: id_type("A", "x"),
                value: Expr::konst("base", vec![Level::param("u")]),
                reducibility: Reducibility::Reducible,
            },
        ],
    }
}

fn use_imported_use_id_module() -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Test.UseImportedUseId"),
        declarations: vec![Decl::Def {
            name: "use_imported_use_id".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: id_type("A", "x"),
            value: Expr::konst("use_id", vec![Level::param("u")]),
            reducibility: Reducibility::Reducible,
        }],
    }
}

fn local_authoring_reconstruction_identity(
    bytes: &[u8],
    cert: &ModuleCert,
    policy: &AxiomPolicy,
) -> LocalAuthoringReconstructionIdentity {
    LocalAuthoringReconstructionIdentity::new(
        crate::local_authoring::certificate_file_hash(bytes),
        cert.header().format.clone(),
        cert.header().core_spec.clone(),
        cert.header().module.clone(),
        cert.imports().to_vec(),
        cert.hashes().export_hash,
        cert.hashes().axiom_report_hash,
        cert.hashes().certificate_hash,
        policy.policy_hash(),
    )
}

fn local_authoring_interface_identity(cert: &ModuleCert) -> LocalAuthoringInterfaceIdentity {
    LocalAuthoringInterfaceIdentity::new(
        cert.header().module.clone(),
        cert.hashes().export_hash,
        cert.hashes().certificate_hash,
    )
}

#[test]
fn local_authoring_build_live_and_reconstructed_contexts_produce_identical_certificates() {
    let policy = AxiomPolicy::normal();
    let imported_cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let imported_bytes = encode_module_cert(&imported_cert).unwrap();
    let verified_import =
        verify_module_cert_with_import_refs(&imported_bytes, &[], &policy).unwrap();
    let expected_bytes = encode_module_cert(
        &build_module_cert_from_import_refs(use_id_module(), &[&verified_import]).unwrap(),
    )
    .unwrap();

    let live_session = LocalAuthoringVerifierSession::new();
    let live_import = live_session.register_verified_module(&verified_import);
    let live_built = live_session
        .build_module_cert(use_id_module(), &[&live_import], &BTreeMap::new())
        .unwrap();
    assert_eq!(live_built.certificate_bytes(), expected_bytes);
    assert!(!live_built.observations().closure_used_cached_context());
    let live_checked = live_session
        .check_built_module_cert(live_built, &[&live_import], &policy)
        .unwrap();

    let reconstructed_session = LocalAuthoringVerifierSession::new();
    let pending = reconstructed_session
        .reconstruct_pending_context(
            &imported_bytes,
            &local_authoring_reconstruction_identity(&imported_bytes, &imported_cert, &policy),
            &local_authoring_interface_identity(&imported_cert),
            &[],
            &policy,
        )
        .unwrap();
    assert_eq!(pending.module(), &imported_cert.header().module);
    let reconstructed_import = reconstructed_session.adopt_pending_context(pending);
    let reconstructed_built = reconstructed_session
        .build_module_cert(use_id_module(), &[&reconstructed_import], &BTreeMap::new())
        .unwrap();
    assert_eq!(reconstructed_built.certificate_bytes(), expected_bytes);
    assert!(reconstructed_built
        .observations()
        .closure_used_cached_context());
    let reconstructed_checked = reconstructed_session
        .check_built_module_cert(reconstructed_built, &[&reconstructed_import], &policy)
        .unwrap();

    assert_eq!(live_checked.certificate_bytes(), expected_bytes);
    assert_eq!(reconstructed_checked.certificate_bytes(), expected_bytes);
    assert_eq!(
        live_checked.context().module(),
        reconstructed_checked.context().module()
    );
    assert_eq!(
        live_checked.context().export_hash(),
        reconstructed_checked.context().export_hash()
    );
    assert_eq!(
        live_checked.context().certificate_hash(),
        reconstructed_checked.context().certificate_hash()
    );
    assert_eq!(
        live_import.kernel_declarations().unwrap(),
        reconstructed_import.kernel_declarations().unwrap()
    );
    let exported_type = live_import.export_block()[0].ty;
    assert_eq!(
        live_import.term_expression(exported_type).unwrap(),
        reconstructed_import.term_expression(exported_type).unwrap()
    );
    assert!(!live_checked.is_proof_evidence());
    assert!(!reconstructed_checked.is_proof_evidence());
    assert!(reconstructed_checked
        .context()
        .closure_used_cached_context());
    assert!(!reconstructed_checked.context().is_publication_eligible());
    assert!(!reconstructed_checked.context().is_proof_evidence());
    let (bytes, observations, fresh_context) = reconstructed_checked.into_parts();
    assert_eq!(bytes, expected_bytes);
    assert!(observations.closure_used_cached_context());
    assert!(fresh_context.closure_used_cached_context());
    assert!(!fresh_context.is_publication_eligible());
}

#[test]
fn local_authoring_reconstruction_rejects_certificate_and_interface_identity_drift() {
    let policy = AxiomPolicy::normal();
    let cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let bytes = encode_module_cert(&cert).unwrap();
    let identity = local_authoring_reconstruction_identity(&bytes, &cert, &policy);
    let interface = local_authoring_interface_identity(&cert);
    let session = LocalAuthoringVerifierSession::new();

    let mut wrong_file = identity.clone();
    wrong_file.certificate_file_hash[0] ^= 1;
    assert!(matches!(
        session.reconstruct_pending_context(&bytes, &wrong_file, &interface, &[], &policy),
        Err(CertError::NonCanonicalEncoding {
            object: "local authoring certificate file identity"
        })
    ));

    let mut wrong_imports = identity.clone();
    wrong_imports.imports.push(ImportEntry {
        module: Name::from_dotted("Test.Other"),
        export_hash: [1; 32],
        certificate_hash: None,
    });
    assert!(matches!(
        session.reconstruct_pending_context(&bytes, &wrong_imports, &interface, &[], &policy),
        Err(CertError::NonCanonicalEncoding {
            object: "local authoring module/import identity"
        })
    ));

    let wrong_interface = LocalAuthoringInterfaceIdentity::new(
        cert.header().module.clone(),
        [2; 32],
        cert.hashes().certificate_hash,
    );
    assert!(matches!(
        session.reconstruct_pending_context(&bytes, &identity, &wrong_interface, &[], &policy),
        Err(CertError::NonCanonicalEncoding {
            object: "local authoring parsed interface identity"
        })
    ));
}

#[test]
fn local_authoring_reconstruction_resolves_an_exact_nonempty_import_table() {
    let policy = AxiomPolicy::normal();
    let base_cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let base_bytes = encode_module_cert(&base_cert).unwrap();
    let verified_base = verify_module_cert_with_import_refs(&base_bytes, &[], &policy).unwrap();
    let use_cert = build_module_cert_from_import_refs(use_id_module(), &[&verified_base]).unwrap();
    let use_bytes = encode_module_cert(&use_cert).unwrap();
    let verified_use =
        verify_module_cert_with_import_refs(&use_bytes, &[&verified_base], &policy).unwrap();
    let expected_bytes = encode_module_cert(
        &build_module_cert_from_import_refs(
            use_imported_use_id_module(),
            &[&verified_base, &verified_use],
        )
        .unwrap(),
    )
    .unwrap();

    let session = LocalAuthoringVerifierSession::new();
    let base_pending = session
        .reconstruct_pending_context(
            &base_bytes,
            &local_authoring_reconstruction_identity(&base_bytes, &base_cert, &policy),
            &local_authoring_interface_identity(&base_cert),
            &[],
            &policy,
        )
        .unwrap();
    let base_context = session.adopt_pending_context(base_pending);
    let use_pending = session
        .reconstruct_pending_context(
            &use_bytes,
            &local_authoring_reconstruction_identity(&use_bytes, &use_cert, &policy),
            &local_authoring_interface_identity(&use_cert),
            &[&base_context],
            &policy,
        )
        .unwrap();
    let use_context = session.adopt_pending_context(use_pending);
    let built = session
        .build_module_cert(
            use_imported_use_id_module(),
            &[&base_context, &use_context],
            &BTreeMap::new(),
        )
        .unwrap();

    assert_eq!(built.certificate_bytes(), expected_bytes);
    assert!(built.observations().closure_used_cached_context());
    assert!(!built.is_proof_evidence());
    let checked = session
        .check_built_module_cert(built, &[&base_context, &use_context], &policy)
        .unwrap();
    assert_eq!(checked.certificate_bytes(), expected_bytes);
}

#[test]
fn local_authoring_reconstruction_rechecks_canonical_bytes_hashes_and_policy() {
    let normal_policy = AxiomPolicy::normal();
    let cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let bytes = encode_module_cert(&cert).unwrap();
    let interface = local_authoring_interface_identity(&cert);
    let session = LocalAuthoringVerifierSession::new();

    let mut noncanonical = bytes.clone();
    noncanonical.push(0);
    let noncanonical_identity =
        local_authoring_reconstruction_identity(&noncanonical, &cert, &normal_policy);
    assert!(session
        .reconstruct_pending_context(
            &noncanonical,
            &noncanonical_identity,
            &interface,
            &[],
            &normal_policy,
        )
        .is_err());

    let mut wrong_hash = local_authoring_reconstruction_identity(&bytes, &cert, &normal_policy);
    wrong_hash.export_hash[0] ^= 1;
    assert!(matches!(
        session.reconstruct_pending_context(&bytes, &wrong_hash, &interface, &[], &normal_policy),
        Err(CertError::HashMismatch {
            object: HashObject::ExportBlock,
            ..
        })
    ));

    let high_trust_policy = AxiomPolicy::high_trust();
    let normal_identity = local_authoring_reconstruction_identity(&bytes, &cert, &normal_policy);
    assert!(matches!(
        session.reconstruct_pending_context(
            &bytes,
            &normal_identity,
            &interface,
            &[],
            &high_trust_policy,
        ),
        Err(CertError::NonCanonicalEncoding {
            object: "local authoring axiom policy identity"
        })
    ));

    let axiom_cert = build_module_cert(axiom_module(), &[]).unwrap();
    let axiom_bytes = encode_module_cert(&axiom_cert).unwrap();
    let high_trust_identity =
        local_authoring_reconstruction_identity(&axiom_bytes, &axiom_cert, &high_trust_policy);
    assert!(matches!(
        session.reconstruct_pending_context(
            &axiom_bytes,
            &high_trust_identity,
            &local_authoring_interface_identity(&axiom_cert),
            &[],
            &high_trust_policy,
        ),
        Err(CertError::ForbiddenAxiom { .. })
    ));
}

#[test]
fn local_authoring_reconstruction_is_structural_and_does_not_create_kernel_evidence() {
    let policy = AxiomPolicy::normal();
    let mut cert = build_module_cert(two_id_theorems_module(), &[]).unwrap();
    cert.mutate_parts_for_test(|parts| match &mut parts.declarations[1].decl {
        DeclPayload::Theorem { proof, ty, .. } => *proof = *ty,
        _ => panic!("expected theorem"),
    });
    rehash_cert_after_decl_change(&mut cert);
    let bytes = encode_module_cert(&cert).unwrap();
    assert!(matches!(
        verify_module_cert_with_import_refs(&bytes, &[], &policy),
        Err(CertError::Kernel(_))
    ));

    let session = LocalAuthoringVerifierSession::new();
    let pending = session
        .reconstruct_pending_context(
            &bytes,
            &local_authoring_reconstruction_identity(&bytes, &cert, &policy),
            &local_authoring_interface_identity(&cert),
            &[],
            &policy,
        )
        .unwrap();
    let context = session.adopt_pending_context(pending);

    assert_eq!(context.module(), &cert.header().module);
    assert!(context.closure_used_cached_context());
}

#[test]
fn local_authoring_contexts_are_rejected_by_a_different_session() {
    let policy = AxiomPolicy::normal();
    let cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let bytes = encode_module_cert(&cert).unwrap();
    let verified = verify_module_cert_with_import_refs(&bytes, &[], &policy).unwrap();
    let owner = LocalAuthoringVerifierSession::new();
    let context = owner.register_verified_module(&verified);
    let other = LocalAuthoringVerifierSession::new();

    assert!(matches!(
        other.build_module_cert(use_id_module(), &[&context], &BTreeMap::new()),
        Err(CertError::ImportNotVerifiedInSession { module })
            if &module == verified.module()
    ));
}

#[test]
fn local_authoring_built_check_preserves_cached_provenance_if_import_origin_changes() {
    let policy = AxiomPolicy::normal();
    let cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let bytes = encode_module_cert(&cert).unwrap();
    let verified = verify_module_cert_with_import_refs(&bytes, &[], &policy).unwrap();
    let session = LocalAuthoringVerifierSession::new();
    let live = session.register_verified_module(&verified);
    let pending = session
        .reconstruct_pending_context(
            &bytes,
            &local_authoring_reconstruction_identity(&bytes, &cert, &policy),
            &local_authoring_interface_identity(&cert),
            &[],
            &policy,
        )
        .unwrap();
    let cached = session.adopt_pending_context(pending);
    let built = session
        .build_module_cert(use_id_module(), &[&live], &BTreeMap::new())
        .unwrap();
    assert!(!built.observations().closure_used_cached_context());

    let checked = session
        .check_built_module_cert(built, &[&cached], &policy)
        .unwrap();
    assert!(checked.observations().closure_used_cached_context());
    assert!(checked.context().closure_used_cached_context());
}

fn eq_rec_alias_module() -> CoreModule {
    let u = Level::param("u");
    let v = Level::param("v");
    CoreModule {
        name: Name::from_dotted("Test.EqRecAlias"),
        declarations: vec![Decl::Theorem {
            name: "eq_rec_alias".to_owned(),
            universe_params: vec!["u".to_owned(), "v".to_owned()],
            ty: eq_rec_type(u.clone(), v.clone()),
            proof: Expr::konst("Eq.rec", vec![u, v]),
        }],
    }
}

fn use_imported_eq_rec_alias_module() -> CoreModule {
    let u = Level::param("u");
    let v = Level::param("v");
    CoreModule {
        name: Name::from_dotted("Test.UseEqRecAlias"),
        declarations: vec![Decl::Def {
            name: "use_eq_rec_alias".to_owned(),
            universe_params: vec!["u".to_owned(), "v".to_owned()],
            ty: eq_rec_type(u.clone(), v.clone()),
            value: Expr::konst("eq_rec_alias", vec![u, v]),
            reducibility: Reducibility::Reducible,
        }],
    }
}

fn axiom_module() -> CoreModule {
    named_axiom_module("Test.Axiom", "P")
}

fn named_axiom_module(module: &str, axiom: &str) -> CoreModule {
    CoreModule {
        name: Name::from_dotted(module),
        declarations: vec![Decl::Axiom {
            name: axiom.to_owned(),
            universe_params: vec![],
            ty: Expr::sort(Level::zero()),
        }],
    }
}

fn ordered_axioms_module(order: &[&str]) -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Test.OrderedAxioms"),
        declarations: order
            .iter()
            .map(|name| Decl::Axiom {
                name: (*name).to_owned(),
                universe_params: vec![],
                ty: Expr::sort(Level::zero()),
            })
            .collect(),
    }
}

fn forward_axiom_dependency_module() -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Test.ForwardAxiom"),
        declarations: vec![
            Decl::Axiom {
                name: "p".to_owned(),
                universe_params: vec![],
                ty: Expr::konst("P", vec![]),
            },
            Decl::Axiom {
                name: "P".to_owned(),
                universe_params: vec![],
                ty: Expr::sort(Level::zero()),
            },
        ],
    }
}

fn use_axiom_module() -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Test.UseAxiom"),
        declarations: vec![Decl::Def {
            name: "use_p".to_owned(),
            universe_params: vec![],
            ty: Expr::sort(Level::zero()),
            value: Expr::konst("P", vec![]),
            reducibility: Reducibility::Reducible,
        }],
    }
}

fn use_imported_use_p_module() -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Test.UseImportedUseP"),
        declarations: vec![Decl::Def {
            name: "use_use_p".to_owned(),
            universe_params: vec![],
            ty: Expr::sort(Level::zero()),
            value: Expr::konst("use_p", vec![]),
            reducibility: Reducibility::Reducible,
        }],
    }
}

fn hidden_proof_helper_module() -> CoreModule {
    named_axiom_module("Test.HiddenProofHelper", "hidden_witness")
}

fn public_id_with_hidden_import_proof_module() -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Test.PublicIdWithHiddenProof"),
        declarations: vec![
            Decl::Theorem {
                name: "hidden_thm".to_owned(),
                universe_params: vec![],
                ty: Expr::sort(Level::zero()),
                proof: Expr::konst("hidden_witness", vec![]),
            },
            Decl::Def {
                name: "hidden_opaque_def".to_owned(),
                universe_params: vec![],
                ty: Expr::sort(Level::zero()),
                value: Expr::konst("hidden_witness", vec![]),
                reducibility: Reducibility::Opaque,
            },
            Decl::Def {
                name: "public_id".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: id_type("A", "x"),
                value: id_value("A", "x"),
                reducibility: Reducibility::Reducible,
            },
        ],
    }
}

fn use_public_id_module() -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Test.UsePublicId"),
        declarations: vec![Decl::Def {
            name: "use_public_id".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: id_type("A", "x"),
            value: Expr::konst("public_id", vec![Level::param("u")]),
            reducibility: Reducibility::Reducible,
        }],
    }
}

fn use_two_axioms_module() -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Test.UseTwoAxioms"),
        declarations: vec![
            Decl::Def {
                name: "use_alpha".to_owned(),
                universe_params: vec![],
                ty: Expr::sort(Level::zero()),
                value: Expr::konst("Alpha", vec![]),
                reducibility: Reducibility::Reducible,
            },
            Decl::Def {
                name: "use_beta".to_owned(),
                universe_params: vec![],
                ty: Expr::sort(Level::zero()),
                value: Expr::konst("Beta", vec![]),
                reducibility: Reducibility::Reducible,
            },
        ],
    }
}

fn theorem_using_axiom_module(proof_axiom: &str) -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Test.AxiomProof"),
        declarations: vec![
            Decl::Axiom {
                name: "P".to_owned(),
                universe_params: vec![],
                ty: Expr::sort(Level::zero()),
            },
            Decl::Axiom {
                name: "p1".to_owned(),
                universe_params: vec![],
                ty: Expr::konst("P", vec![]),
            },
            Decl::Axiom {
                name: "p2".to_owned(),
                universe_params: vec![],
                ty: Expr::konst("P", vec![]),
            },
            Decl::Theorem {
                name: "t".to_owned(),
                universe_params: vec![],
                ty: Expr::konst("P", vec![]),
                proof: Expr::konst(proof_axiom, vec![]),
            },
        ],
    }
}

fn unary_inductive_module() -> CoreModule {
    let data = InductiveDecl::new(
        "Unary",
        vec![],
        vec![],
        vec![],
        Level::succ(Level::zero()),
        vec![
            ConstructorDecl::new("Unary.zero", unary()),
            ConstructorDecl::new("Unary.succ", Expr::pi("_", unary(), unary())),
        ],
        None,
    );
    CoreModule {
        name: Name::from_dotted("Test.Unary"),
        declarations: vec![Decl::Inductive {
            name: "Unary".to_owned(),
            universe_params: vec![],
            ty: Expr::sort(Level::succ(Level::zero())),
            data: Box::new(data),
        }],
    }
}

fn unary() -> Expr {
    Expr::konst("Unary", vec![])
}

fn unary_zero() -> Expr {
    Expr::konst("Unary.zero", vec![])
}

fn unary_succ(arg: Expr) -> Expr {
    Expr::app(Expr::konst("Unary.succ", vec![]), arg)
}

fn unary_rec_type(level: Level) -> Expr {
    let motive_ty = Expr::pi("_", unary(), Expr::sort(level));
    let z_ty = Expr::app(Expr::bvar(0), unary_zero());
    let s_ty = Expr::pi(
        "n",
        unary(),
        Expr::pi(
            "ih",
            Expr::app(Expr::bvar(2), Expr::bvar(0)),
            Expr::app(Expr::bvar(3), unary_succ(Expr::bvar(1))),
        ),
    );

    Expr::pi(
        "motive",
        motive_ty,
        Expr::pi(
            "z",
            z_ty,
            Expr::pi(
                "s",
                s_ty,
                Expr::pi("n", unary(), Expr::app(Expr::bvar(3), Expr::bvar(0))),
            ),
        ),
    )
}

fn unary_rec_type_with_beta_result(level: Level) -> Expr {
    let motive_ty = Expr::pi("_", unary(), Expr::sort(level));
    let z_ty = Expr::app(Expr::bvar(0), unary_zero());
    let s_ty = Expr::pi(
        "n",
        unary(),
        Expr::pi(
            "ih",
            Expr::app(Expr::bvar(2), Expr::bvar(0)),
            Expr::app(Expr::bvar(3), unary_succ(Expr::bvar(1))),
        ),
    );
    let beta_result = Expr::app(
        Expr::lam("y", unary(), Expr::app(Expr::bvar(4), Expr::bvar(0))),
        Expr::bvar(0),
    );

    Expr::pi(
        "motive",
        motive_ty,
        Expr::pi(
            "z",
            z_ty,
            Expr::pi("s", s_ty, Expr::pi("n", unary(), beta_result)),
        ),
    )
}

fn unary_inductive_with_recursor_module() -> CoreModule {
    let data = InductiveDecl::new(
        "Unary",
        vec![],
        vec![],
        vec![],
        Level::succ(Level::zero()),
        vec![
            ConstructorDecl::new("Unary.zero", unary()),
            ConstructorDecl::new("Unary.succ", Expr::pi("_", unary(), unary())),
        ],
        Some(RecursorDecl::new(
            "Unary.rec",
            vec!["u".to_owned()],
            unary_rec_type(Level::param("u")),
        )),
    );
    CoreModule {
        name: Name::from_dotted("Test.UnaryRec"),
        declarations: vec![Decl::Inductive {
            name: "Unary".to_owned(),
            universe_params: vec![],
            ty: Expr::sort(Level::succ(Level::zero())),
            data: Box::new(data),
        }],
    }
}

fn unary_inductive_with_beta_recursor_module() -> CoreModule {
    let data = InductiveDecl::new(
        "Unary",
        vec![],
        vec![],
        vec![],
        Level::succ(Level::zero()),
        vec![
            ConstructorDecl::new("Unary.zero", unary()),
            ConstructorDecl::new("Unary.succ", Expr::pi("_", unary(), unary())),
        ],
        Some(RecursorDecl::new(
            "Unary.rec",
            vec!["u".to_owned()],
            unary_rec_type_with_beta_result(Level::param("u")),
        )),
    );
    CoreModule {
        name: Name::from_dotted("Test.UnaryBetaRec"),
        declarations: vec![Decl::Inductive {
            name: "Unary".to_owned(),
            universe_params: vec![],
            ty: Expr::sort(Level::succ(Level::zero())),
            data: Box::new(data),
        }],
    }
}

fn unary_inductive_with_recursor_type_anchor_module() -> CoreModule {
    let mut module = unary_inductive_with_recursor_module();
    module.declarations.push(Decl::Axiom {
        name: "Unary.rec_anchor".to_owned(),
        universe_params: vec!["u".to_owned()],
        ty: unary_rec_type(Level::param("u")),
    });
    module
}

fn box_inductive_module() -> CoreModule {
    let u = Level::param("u");
    let box_a = |a: Expr| Expr::app(Expr::konst("Box", vec![u.clone()]), a);
    let data = InductiveDecl::new(
        "Box",
        vec!["u".to_owned()],
        vec![Binder::new("A", Expr::sort(u.clone()))],
        vec![],
        u.clone(),
        vec![ConstructorDecl::new(
            "Box.mk",
            Expr::pi(
                "A",
                Expr::sort(u.clone()),
                Expr::pi("x", Expr::bvar(0), box_a(Expr::bvar(1))),
            ),
        )],
        None,
    );
    CoreModule {
        name: Name::from_dotted("Test.Box"),
        declarations: vec![Decl::Inductive {
            name: "Box".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: Expr::pi("A", Expr::sort(u.clone()), Expr::sort(u)),
            data: Box::new(data),
        }],
    }
}

fn list_type(level: Level, elem: Expr) -> Expr {
    Expr::app(Expr::konst("List", vec![level]), elem)
}

fn list_inductive_base() -> InductiveDecl {
    let u = Level::param("u");
    InductiveDecl::new(
        "List",
        vec!["u".to_owned()],
        vec![Binder::new("A", Expr::sort(u.clone()))],
        vec![],
        u.clone(),
        vec![
            ConstructorDecl::new(
                "List.nil",
                Expr::pi(
                    "A",
                    Expr::sort(u.clone()),
                    list_type(u.clone(), Expr::bvar(0)),
                ),
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
                            list_type(u.clone(), Expr::bvar(1)),
                            list_type(u.clone(), Expr::bvar(2)),
                        ),
                    ),
                ),
            ),
        ],
        None,
    )
}

fn rose_type(level: Level, elem: Expr) -> Expr {
    Expr::app(Expr::konst("Rose", vec![level]), elem)
}

fn rose_inductive_with_child(child_ty: Expr) -> InductiveDecl {
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
                    Expr::pi("children", child_ty, rose_type(u, Expr::bvar(2))),
                ),
            ),
        )],
        None,
    )
}

fn rose_nested_list_base() -> InductiveDecl {
    let u = Level::param("u");
    rose_inductive_with_child(list_type(u.clone(), rose_type(u, Expr::bvar(1))))
}

fn rose_unknown_functor_base() -> InductiveDecl {
    let u = Level::param("u");
    rose_inductive_with_child(Expr::app(
        Expr::konst("Box", vec![u.clone()]),
        rose_type(u, Expr::bvar(1)),
    ))
}

fn rose_negative_arrow_base(result_ty: Expr) -> InductiveDecl {
    let u = Level::param("u");
    rose_inductive_with_child(Expr::pi(
        "_",
        rose_type(u.clone(), Expr::bvar(1)),
        result_ty,
    ))
}

fn rose_higher_order_negative_base() -> InductiveDecl {
    let u = Level::param("u");
    let inner = Expr::pi("_", rose_type(u.clone(), Expr::bvar(1)), Expr::bvar(2));
    rose_inductive_with_child(Expr::pi("_", inner, rose_type(u, Expr::bvar(2))))
}

fn nested_rose_module() -> CoreModule {
    let list = generate_inductive_artifacts_v1(&list_inductive_base()).unwrap();
    let rose = generate_inductive_artifacts_v1(&rose_nested_list_base()).unwrap();
    CoreModule {
        name: Name::from_dotted("Test.NestedRose"),
        declarations: vec![
            Decl::Inductive {
                name: "List".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: Expr::pi(
                    "A",
                    Expr::sort(Level::param("u")),
                    Expr::sort(Level::param("u")),
                ),
                data: Box::new(list),
            },
            Decl::Inductive {
                name: "Rose".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: Expr::pi(
                    "A",
                    Expr::sort(Level::param("u")),
                    Expr::sort(Level::param("u")),
                ),
                data: Box::new(rose),
            },
        ],
    }
}

fn vec_type(level: Level, a: Expr, n: Expr) -> Expr {
    Expr::apps(Expr::konst("Vec", vec![level]), vec![a, n])
}

fn vec_inductive_base() -> InductiveDecl {
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

fn fin_inductive_base() -> InductiveDecl {
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

fn non_positive_even_odd_mutual_base() -> MutualInductiveBlock {
    MutualInductiveBlock::new(
        "BadEvenOdd",
        vec![],
        vec![
            InductiveDecl::new(
                "Even",
                vec![],
                vec![],
                vec![Binder::new("n", nat())],
                prop(),
                vec![ConstructorDecl::new(
                    "Even.bad",
                    Expr::pi(
                        "f",
                        Expr::pi("_", odd_type(nat_zero()), nat()),
                        even_type(nat_zero()),
                    ),
                )],
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

fn even_odd_mutual_block() -> MutualInductiveBlock {
    generate_mutual_inductive_artifacts_v1(&even_odd_mutual_base()).unwrap()
}

fn even_odd_mutual_module() -> CoreModule {
    let block = even_odd_mutual_block();
    CoreModule {
        name: Name::from_dotted("Test.EvenOdd"),
        declarations: vec![Decl::MutualInductiveBlock {
            name: block.name.clone(),
            universe_params: block.universe_params.clone(),
            data: Box::new(block),
        }],
    }
}

fn indexed_inductive_module() -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Test.Indexed"),
        declarations: vec![
            Decl::Inductive {
                name: "Vec".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: Expr::pi(
                    "A",
                    Expr::sort(Level::param("u")),
                    Expr::pi("n", nat(), Expr::sort(Level::param("u"))),
                ),
                data: Box::new(generate_inductive_artifacts_v1(&vec_inductive_base()).unwrap()),
            },
            Decl::Inductive {
                name: "Fin".to_owned(),
                universe_params: vec![],
                ty: Expr::pi("n", nat(), Expr::sort(type0())),
                data: Box::new(generate_inductive_artifacts_v1(&fin_inductive_base()).unwrap()),
            },
        ],
    }
}

fn unary_with_local_constructor_use_module() -> CoreModule {
    let mut module = unary_inductive_module();
    module.declarations.push(Decl::Def {
        name: "z".to_owned(),
        universe_params: vec![],
        ty: Expr::konst("Unary", vec![]),
        value: Expr::konst("Unary.zero", vec![]),
        reducibility: Reducibility::Reducible,
    });
    module
}

fn use_imported_unary_constructor_module() -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Test.UseUnary"),
        declarations: vec![Decl::Def {
            name: "z".to_owned(),
            universe_params: vec![],
            ty: Expr::konst("Unary", vec![]),
            value: Expr::konst("Unary.zero", vec![]),
            reducibility: Reducibility::Reducible,
        }],
    }
}

fn use_imported_unary_recursor_module() -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Test.UseUnaryRec"),
        declarations: vec![Decl::Def {
            name: "rec_alias".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: unary_rec_type(Level::param("u")),
            value: Expr::konst("Unary.rec", vec![Level::param("u")]),
            reducibility: Reducibility::Reducible,
        }],
    }
}

fn hash_hex(hash: Hash) -> String {
    hash.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn test_hash(byte: u8) -> Hash {
    [byte; 32]
}

struct HashContractDefFixture {
    decl: DeclPayload,
    dependencies: Vec<DependencyEntry>,
    axiom_dependencies: Vec<AxiomRef>,
    term_table: Vec<TermNode>,
    term_hashes: Vec<Hash>,
    names: Vec<Name>,
}

fn hash_contract_def_fixture() -> HashContractDefFixture {
    let names = vec![
        Name::from_dotted("f"),
        Name::from_dotted("u"),
        Name::from_dotted("Dep"),
        Name::from_dotted("Ax"),
    ];
    let dependency_ref = GlobalRef::Imported {
        import_index: 0,
        name: 2,
        decl_interface_hash: test_hash(0x31),
    };
    let axiom_ref = GlobalRef::Imported {
        import_index: 0,
        name: 3,
        decl_interface_hash: test_hash(0x41),
    };
    let decl = DeclPayload::Def {
        name: 0,
        universe_params: vec![1],
        ty: 0,
        value: 1,
        reducibility: CertReducibility::Reducible,
    };
    let dependencies = vec![interface_dependency(
        dependency_ref.clone(),
        test_hash(0x31),
    )];
    let axiom_dependencies = vec![AxiomRef {
        global_ref: axiom_ref.clone(),
        name: 3,
        decl_interface_hash: test_hash(0x41),
    }];
    let term_table = vec![
        TermNode::Const {
            global_ref: dependency_ref,
            levels: vec![],
        },
        TermNode::Const {
            global_ref: axiom_ref,
            levels: vec![],
        },
    ];
    let term_hashes = vec![test_hash(0x10), test_hash(0x20)];

    HashContractDefFixture {
        decl,
        dependencies,
        axiom_dependencies,
        term_table,
        term_hashes,
        names,
    }
}

fn append_name_id(out: &mut Vec<u8>, names: &[Name], id: NameId) {
    encode_name_to(out, &names[id]);
}

fn append_name_ids(out: &mut Vec<u8>, names: &[Name], ids: &[NameId]) {
    encode_uvar_to(out, ids.len() as u64);
    for id in ids {
        append_name_id(out, names, *id);
    }
}

fn append_test_string(bytes: &mut Vec<u8>, value: &str) {
    encode_uvar_to(bytes, value.len() as u64);
    bytes.extend(value.as_bytes());
}

fn read_test_uvar(bytes: &[u8], offset: &mut usize) -> u64 {
    let mut result = 0;
    let mut shift = 0;
    loop {
        let byte = bytes[*offset];
        *offset += 1;
        result |= ((byte & 0x7f) as u64) << shift;
        if byte & 0x80 == 0 {
            return result;
        }
        shift += 7;
    }
}

fn skip_test_string(bytes: &[u8], offset: &mut usize) {
    let len = read_test_uvar(bytes, offset) as usize;
    *offset += len;
}

fn skip_test_name(bytes: &[u8], offset: &mut usize) {
    let len = read_test_uvar(bytes, offset);
    for _ in 0..len {
        skip_test_string(bytes, offset);
    }
}

fn skip_test_imports(bytes: &[u8], offset: &mut usize) {
    let len = read_test_uvar(bytes, offset);
    for _ in 0..len {
        skip_test_name(bytes, offset);
        *offset += 32;
        match bytes[*offset] {
            0x00 => *offset += 1,
            0x01 => *offset += 33,
            tag => panic!("unexpected option tag {tag}"),
        }
    }
}

fn skip_test_name_table(bytes: &[u8], offset: &mut usize) {
    let len = read_test_uvar(bytes, offset);
    for _ in 0..len {
        skip_test_name(bytes, offset);
    }
}

fn skip_test_level_table(bytes: &[u8], offset: &mut usize) {
    let len = read_test_uvar(bytes, offset);
    for _ in 0..len {
        let tag = bytes[*offset];
        *offset += 1;
        match tag {
            0x00 => {}
            0x01 | 0x04 => {
                read_test_uvar(bytes, offset);
            }
            0x02 | 0x03 => {
                read_test_uvar(bytes, offset);
                read_test_uvar(bytes, offset);
            }
            tag => panic!("unexpected level tag {tag}"),
        }
    }
}

fn term_tag_offsets(bytes: &[u8]) -> Vec<usize> {
    let mut offset = 0;
    skip_test_string(bytes, &mut offset);
    skip_test_string(bytes, &mut offset);
    skip_test_name(bytes, &mut offset);
    skip_test_imports(bytes, &mut offset);
    skip_test_name_table(bytes, &mut offset);
    skip_test_level_table(bytes, &mut offset);
    let term_len = read_test_uvar(bytes, &mut offset);
    let mut offsets = Vec::with_capacity(term_len as usize);
    for _ in 0..term_len {
        offsets.push(offset);
        let tag = bytes[offset];
        offset += 1;
        match tag {
            0x00 | 0x01 => {
                read_test_uvar(bytes, &mut offset);
            }
            0x02 => {
                let global_ref_tag = bytes[offset];
                offset += 1;
                match global_ref_tag {
                    0x00 => {
                        read_test_uvar(bytes, &mut offset);
                        read_test_uvar(bytes, &mut offset);
                        offset += 32;
                    }
                    0x01 => {
                        read_test_uvar(bytes, &mut offset);
                    }
                    0x02 => {
                        read_test_uvar(bytes, &mut offset);
                        read_test_uvar(bytes, &mut offset);
                    }
                    0x03 => {
                        read_test_uvar(bytes, &mut offset);
                        offset += 32;
                    }
                    tag => panic!("unexpected global reference tag {tag}"),
                }
                let level_len = read_test_uvar(bytes, &mut offset);
                for _ in 0..level_len {
                    read_test_uvar(bytes, &mut offset);
                }
            }
            0x03..=0x05 => {
                read_test_uvar(bytes, &mut offset);
                read_test_uvar(bytes, &mut offset);
            }
            tag => panic!("unexpected term tag {tag}"),
        }
    }
    offsets
}

fn verify_cert(cert: &ModuleCert, session: &mut VerifierSession) -> VerifiedModule {
    verify_module_cert(
        &encode_module_cert(cert).unwrap(),
        session,
        &AxiomPolicy::normal(),
    )
    .unwrap()
}

fn recursor_artifact_hashes(cert: &ModuleCert) -> (Hash, Hash) {
    let recursor = cert
        .declarations()
        .iter()
        .find_map(|decl| match &decl.decl {
            DeclPayload::Inductive {
                recursor: Some(recursor),
                ..
            }
            | DeclPayload::InductiveConstrained {
                recursor: Some(recursor),
                ..
            } => Some(recursor),
            _ => None,
        })
        .unwrap();
    recursor_artifact_hashes_for_recursor(cert, recursor)
}

fn recursor_artifact_hashes_for(cert: &ModuleCert, name: &str) -> (Hash, Hash) {
    let recursor = cert
        .declarations()
        .iter()
        .find_map(|decl| match &decl.decl {
            DeclPayload::Inductive {
                name: decl_name,
                recursor: Some(recursor),
                ..
            }
            | DeclPayload::InductiveConstrained {
                name: decl_name,
                recursor: Some(recursor),
                ..
            } if cert.name_table()[*decl_name] == Name::from_dotted(name) => Some(recursor),
            DeclPayload::MutualInductiveBlock { inductives, .. } => inductives
                .iter()
                .find(|inductive| cert.name_table()[inductive.name] == Name::from_dotted(name))
                .and_then(|inductive| inductive.recursor.as_ref()),
            _ => None,
        })
        .unwrap();
    recursor_artifact_hashes_for_recursor(cert, recursor)
}

fn recursor_artifact_hashes_for_recursor(
    cert: &ModuleCert,
    recursor: &RecursorSpec,
) -> (Hash, Hash) {
    let level_hashes = compute_level_hashes(cert.level_table(), cert.name_table()).unwrap();
    let term_hashes = compute_term_hashes(cert.term_table(), &level_hashes).unwrap();

    (
        generated_recursor_signature_hash(Some(recursor), &term_hashes, cert.name_table()).unwrap(),
        generated_computation_rule_hash(Some(recursor)),
    )
}

fn remap_swapped_term_id(term: &mut TermId, lhs: TermId, rhs: TermId) {
    if *term == lhs {
        *term = rhs;
    } else if *term == rhs {
        *term = lhs;
    }
}

fn remap_swapped_term_ids_in_term(term: &mut TermNode, lhs: TermId, rhs: TermId) {
    match term {
        TermNode::Sort(_) | TermNode::BVar(_) | TermNode::Const { .. } => {}
        TermNode::App(fun, arg) => {
            remap_swapped_term_id(fun, lhs, rhs);
            remap_swapped_term_id(arg, lhs, rhs);
        }
        TermNode::Lam { ty, body } | TermNode::Pi { ty, body } => {
            remap_swapped_term_id(ty, lhs, rhs);
            remap_swapped_term_id(body, lhs, rhs);
        }
    }
}

fn remap_swapped_term_ids_in_decl(decl: &mut DeclPayload, lhs: TermId, rhs: TermId) {
    match decl {
        DeclPayload::Axiom { ty, .. } | DeclPayload::AxiomConstrained { ty, .. } => {
            remap_swapped_term_id(ty, lhs, rhs)
        }
        DeclPayload::Def { ty, value, .. } | DeclPayload::DefConstrained { ty, value, .. } => {
            remap_swapped_term_id(ty, lhs, rhs);
            remap_swapped_term_id(value, lhs, rhs);
        }
        DeclPayload::Theorem { ty, proof, .. }
        | DeclPayload::TheoremConstrained { ty, proof, .. } => {
            remap_swapped_term_id(ty, lhs, rhs);
            remap_swapped_term_id(proof, lhs, rhs);
        }
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
        } => {
            for binder in params.iter_mut().chain(indices) {
                remap_swapped_term_id(&mut binder.ty, lhs, rhs);
            }
            for constructor in constructors {
                remap_swapped_term_id(&mut constructor.ty, lhs, rhs);
            }
            if let Some(recursor) = recursor {
                remap_swapped_term_id(&mut recursor.ty, lhs, rhs);
            }
        }
        DeclPayload::MutualInductiveBlock { inductives, .. } => {
            for inductive in inductives {
                for binder in inductive.params.iter_mut().chain(&mut inductive.indices) {
                    remap_swapped_term_id(&mut binder.ty, lhs, rhs);
                }
                for constructor in &mut inductive.constructors {
                    remap_swapped_term_id(&mut constructor.ty, lhs, rhs);
                }
                if let Some(recursor) = &mut inductive.recursor {
                    remap_swapped_term_id(&mut recursor.ty, lhs, rhs);
                }
            }
        }
    }
}

fn swap_term_table_entries(cert: &mut ModuleCert, lhs: TermId, rhs: TermId) {
    cert.mutate_parts_for_test(|parts| {
        parts.term_table.swap(lhs, rhs);
        for term in &mut parts.term_table {
            remap_swapped_term_ids_in_term(term, lhs, rhs);
        }
        for decl in &mut parts.declarations {
            remap_swapped_term_ids_in_decl(&mut decl.decl, lhs, rhs);
        }
    });
}

fn remap_swapped_level_id(level: &mut LevelId, lhs: LevelId, rhs: LevelId) {
    if *level == lhs {
        *level = rhs;
    } else if *level == rhs {
        *level = lhs;
    }
}

fn remap_swapped_level_ids_in_level(level: &mut LevelNode, lhs: LevelId, rhs: LevelId) {
    match level {
        LevelNode::Zero | LevelNode::Param(_) => {}
        LevelNode::Succ(inner) => remap_swapped_level_id(inner, lhs, rhs),
        LevelNode::Max(left, right) | LevelNode::IMax(left, right) => {
            remap_swapped_level_id(left, lhs, rhs);
            remap_swapped_level_id(right, lhs, rhs);
        }
    }
}

fn remap_swapped_level_ids_in_term(term: &mut TermNode, lhs: LevelId, rhs: LevelId) {
    match term {
        TermNode::Sort(level) => remap_swapped_level_id(level, lhs, rhs),
        TermNode::Const { levels, .. } => {
            for level in levels {
                remap_swapped_level_id(level, lhs, rhs);
            }
        }
        TermNode::BVar(_) | TermNode::App(_, _) | TermNode::Lam { .. } | TermNode::Pi { .. } => {}
    }
}

fn remap_swapped_level_ids_in_decl(decl: &mut DeclPayload, lhs: LevelId, rhs: LevelId) {
    if let DeclPayload::Inductive { sort, .. } = decl {
        remap_swapped_level_id(sort, lhs, rhs);
    }
}

fn swap_level_table_entries(cert: &mut ModuleCert, lhs: LevelId, rhs: LevelId) {
    cert.mutate_parts_for_test(|parts| {
        parts.level_table.swap(lhs, rhs);
        for level in &mut parts.level_table {
            remap_swapped_level_ids_in_level(level, lhs, rhs);
        }
        for term in &mut parts.term_table {
            remap_swapped_level_ids_in_term(term, lhs, rhs);
        }
        for decl in &mut parts.declarations {
            remap_swapped_level_ids_in_decl(&mut decl.decl, lhs, rhs);
        }
    });
}

fn replace_level_refs(term: &mut TermNode, old: LevelId, new: LevelId) {
    match term {
        TermNode::Sort(level) => {
            if *level == old {
                *level = new;
            }
        }
        TermNode::Const { levels, .. } => {
            for level in levels {
                if *level == old {
                    *level = new;
                }
            }
        }
        TermNode::BVar(_) | TermNode::App(_, _) | TermNode::Lam { .. } | TermNode::Pi { .. } => {}
    }
}

fn rehash_cert_after_decl_change(cert: &mut ModuleCert) {
    let version = certificate_format_version(cert.header()).unwrap();
    let level_hashes = compute_level_hashes(cert.level_table(), cert.name_table()).unwrap();
    let term_hashes = compute_term_hashes(cert.term_table(), &level_hashes).unwrap();
    let term_table = cert.term_table().to_vec();
    let name_table = cert.name_table().to_vec();
    cert.mutate_parts_for_test(|parts| {
        for decl in &mut parts.declarations {
            decl.hashes = compute_decl_hashes(
                version,
                &decl.decl,
                &decl.dependencies,
                &decl.axiom_dependencies,
                DeclHashTables {
                    terms: &term_table,
                    level_hashes: &level_hashes,
                    term_hashes: &term_hashes,
                    names: &name_table,
                },
            )
            .unwrap();
        }
    });

    let mut previous_axioms: Vec<Vec<AxiomRef>> = Vec::new();
    let mut reports = Vec::new();
    for decl_index in 0..cert.declarations().len() {
        let decl = cert.declarations()[decl_index].decl.clone();
        let dependencies = expected_dependencies_for_decl(cert, &[], decl_index, &decl).unwrap();
        let (direct_axioms, transitive_axioms) = expected_axioms_for_decl(
            cert,
            &[],
            decl_index,
            &decl,
            &dependencies,
            &previous_axioms,
        )
        .unwrap();
        cert.mutate_parts_for_test(|parts| {
            parts.declarations[decl_index].dependencies = dependencies;
            parts.declarations[decl_index].axiom_dependencies = transitive_axioms.clone();
        });
        previous_axioms.push(transitive_axioms.clone());
        reports.push(DeclAxiomReport {
            decl_index,
            direct_axioms,
            transitive_axioms,
        });
    }
    let axiom_report = AxiomReport {
        module_axioms: union_axioms(
            reports
                .iter()
                .flat_map(|report| report.transitive_axioms.iter().cloned()),
        ),
        per_declaration: reports,
        core_features: Vec::new(),
    };
    cert.mutate_parts_for_test(|parts| parts.axiom_report = axiom_report);

    let term_table = cert.term_table().to_vec();
    let name_table = cert.name_table().to_vec();
    cert.mutate_parts_for_test(|parts| {
        for decl in &mut parts.declarations {
            decl.hashes = compute_decl_hashes(
                version,
                &decl.decl,
                &decl.dependencies,
                &decl.axiom_dependencies,
                DeclHashTables {
                    terms: &term_table,
                    level_hashes: &level_hashes,
                    term_hashes: &term_hashes,
                    names: &name_table,
                },
            )
            .unwrap();
        }
    });
    let export_block =
        build_export_block(cert.declarations(), cert.term_table(), &term_hashes).unwrap();
    let export_hash = hash_with_domain(MODULE_EXPORT_DOMAIN, &encode_export_block(&export_block));
    let axiom_report_hash = hash_with_domain(
        b"NPA-AXIOM-REPORT-0.1",
        &encode_axiom_report(cert.axiom_report()),
    );
    cert.mutate_parts_for_test(|parts| {
        parts.export_block = export_block;
        parts.hashes.export_hash = export_hash;
        parts.hashes.axiom_report_hash = axiom_report_hash;
    });
    let certificate_hash = hash_with_domain(
        version.module_certificate_domain(),
        &encode_module_cert_without_certificate_hash_for_header(cert).unwrap(),
    );
    cert.mutate_parts_for_test(|parts| parts.hashes.certificate_hash = certificate_hash);
}

#[derive(Clone, Copy)]
struct GoldenHashFixture<'a> {
    byte_len: usize,
    export_hash: &'a str,
    axiom_report_hash: &'a str,
    certificate_hash: &'a str,
}

fn golden_hash_fixture(label: &str) -> GoldenHashFixture<'static> {
    let fixture = include_str!("../tests/fixtures/golden_hashes.tsv");
    for (line_index, line) in fixture.lines().enumerate() {
        if line_index == 0 || line.trim().is_empty() {
            continue;
        }
        let fields: Vec<_> = line.split('\t').collect();
        assert_eq!(fields.len(), 5, "bad golden fixture line {line_index}");
        if fields[0] == label {
            return GoldenHashFixture {
                byte_len: fields[1].parse().unwrap(),
                export_hash: fields[2],
                axiom_report_hash: fields[3],
                certificate_hash: fields[4],
            };
        }
    }
    panic!("missing golden fixture for {label}");
}

fn assert_golden_cert(label: &str, cert: &ModuleCert) {
    let expected = golden_hash_fixture(label);
    assert_eq!(
        encode_module_cert(cert).unwrap().len(),
        expected.byte_len,
        "{label}"
    );
    assert_eq!(
        hash_hex(cert.hashes().export_hash),
        expected.export_hash,
        "{label}"
    );
    assert_eq!(
        hash_hex(cert.hashes().axiom_report_hash),
        expected.axiom_report_hash,
        "{label}"
    );
    assert_eq!(
        hash_hex(cert.hashes().certificate_hash),
        expected.certificate_hash,
        "{label}"
    );
}

#[test]
fn builds_encodes_decodes_and_verifies_id_certificate() {
    let cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let bytes = encode_module_cert(&cert).unwrap();
    let decoded = decode_module_cert(&bytes).unwrap();
    assert_eq!(decoded, cert);

    let mut session = VerifierSession::new();
    let verified = verify_module_cert(&bytes, &mut session, &AxiomPolicy::normal()).unwrap();

    assert_eq!(verified.module(), &Name::from_dotted("Test.Id"));
    assert_eq!(verified.declarations().len(), 1);
}

#[test]
fn golden_certificate_hashes_cover_core_shapes() {
    let mut session = VerifierSession::new();

    let id = build_module_cert(id_module("A", "x"), &[]).unwrap();
    assert_golden_cert("id", &id);
    verify_cert(&id, &mut session);

    let const_cert = build_module_cert(const_module(), &[]).unwrap();
    assert_golden_cert("const", &const_cert);
    verify_cert(&const_cert, &mut session);

    let nat_cert = build_module_cert(nat_module(), &[]).unwrap();
    assert_golden_cert("nat", &nat_cert);
    let nat_verified = verify_cert(&nat_cert, &mut session);

    let eq_cert = build_module_cert(eq_module(), &[]).unwrap();
    assert_golden_cert("eq", &eq_cert);
    let eq_verified = verify_cert(&eq_cert, &mut session);

    let add_cert =
        build_module_cert(nat_add_module(), std::slice::from_ref(&nat_verified)).unwrap();
    assert_golden_cert("nat_add", &add_cert);
    let add_verified = verify_cert(&add_cert, &mut session);

    let add_zero_cert = build_module_cert(
        add_zero_module(),
        &[nat_verified, eq_verified, add_verified],
    )
    .unwrap();
    assert_golden_cert("add_zero", &add_zero_cert);
    verify_cert(&add_zero_cert, &mut session);
}

#[test]
fn golden_v0_4_certificate_hashes_cover_opaque_surface_cases() {
    let cases = [
        ("v0_4_plain_id", build_v0_4_cert(id_module("A", "x"))),
        (
            "v0_4_opaque_body_direct",
            build_v0_4_cert(id_def_module_with_value_and_reducibility(
                id_value("A", "x"),
                Reducibility::Opaque,
            )),
        ),
        (
            "v0_4_opaque_body_beta",
            build_v0_4_cert(id_def_module_with_value_and_reducibility(
                id_value_with_beta_redex(),
                Reducibility::Opaque,
            )),
        ),
        (
            "v0_4_axiom_proof_p1",
            build_v0_4_cert(theorem_using_axiom_module("p1")),
        ),
        (
            "v0_4_axiom_proof_p2",
            build_v0_4_cert(theorem_using_axiom_module("p2")),
        ),
        (
            "v0_4_opaque_alias_interface",
            v0_4_opaque_alias_cert_with_interface_dependency(),
        ),
        (
            "v0_4_opaque_alias_implementation",
            v0_4_opaque_alias_cert_with_local_implementation_dependency(),
        ),
    ];

    for (label, cert) in cases {
        assert_golden_cert(label, &cert);
    }
}

#[test]
fn binder_names_do_not_affect_term_hashes() {
    let cert_a = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let cert_b = build_module_cert(id_module("B", "y"), &[]).unwrap();

    let value_a = match cert_a.declarations()[0].decl {
        DeclPayload::Def { value, .. } => value,
        _ => panic!("expected def"),
    };
    let value_b = match cert_b.declarations()[0].decl {
        DeclPayload::Def { value, .. } => value,
        _ => panic!("expected def"),
    };

    assert_eq!(term_hash(&cert_a, value_a), term_hash(&cert_b, value_b));
    assert_eq!(cert_a.hashes().export_hash, cert_b.hashes().export_hash);
}

#[test]
fn dependency_and_axiom_refs_sort_by_canonical_bytes() {
    fn encoded_global_ref(global_ref: &GlobalRef) -> Vec<u8> {
        let mut out = Vec::new();
        encode_global_ref_to(&mut out, global_ref);
        out
    }

    fn assert_global_refs_are_in_canonical_byte_order(refs: &[GlobalRef]) {
        for pair in refs.windows(2) {
            assert!(
                encoded_global_ref(&pair[0]) < encoded_global_ref(&pair[1]),
                "GlobalRef order must match canonical binary bytes"
            );
        }
    }

    let dep_255 = interface_dependency(GlobalRef::Local { decl_index: 255 }, [0x01; 32]);
    let dep_16384 = interface_dependency(GlobalRef::Local { decl_index: 16_384 }, [0x02; 32]);
    let deps = [dep_255, dep_16384]
        .into_iter()
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    assert!(matches!(
        deps[0].global_ref(),
        GlobalRef::Local { decl_index: 16_384 }
    ));
    assert_global_refs_are_in_canonical_byte_order(
        &deps
            .iter()
            .map(|dependency| dependency.global_ref().clone())
            .collect::<Vec<_>>(),
    );

    let axiom_255 = AxiomRef {
        global_ref: GlobalRef::Local { decl_index: 255 },
        name: 255,
        decl_interface_hash: [0x03; 32],
    };
    let axiom_16384 = AxiomRef {
        global_ref: GlobalRef::Local { decl_index: 16_384 },
        name: 16_384,
        decl_interface_hash: [0x04; 32],
    };
    let axioms = union_axioms([axiom_255, axiom_16384]);
    assert!(matches!(
        axioms[0].global_ref,
        GlobalRef::Local { decl_index: 16_384 }
    ));
    assert_global_refs_are_in_canonical_byte_order(
        &axioms
            .iter()
            .map(|axiom| axiom.global_ref.clone())
            .collect::<Vec<_>>(),
    );

    let mixed_deps = [
        interface_dependency(
            GlobalRef::Builtin {
                name: 1,
                decl_interface_hash: [0x05; 32],
            },
            [0x05; 32],
        ),
        interface_dependency(
            GlobalRef::LocalGenerated {
                decl_index: 0,
                name: 2,
            },
            [0x06; 32],
        ),
        interface_dependency(GlobalRef::Local { decl_index: 0 }, [0x07; 32]),
        interface_dependency(
            GlobalRef::Imported {
                import_index: 0,
                name: 3,
                decl_interface_hash: [0x08; 32],
            },
            [0x08; 32],
        ),
    ]
    .into_iter()
    .collect::<std::collections::BTreeSet<_>>()
    .into_iter()
    .map(|dependency| dependency.global_ref().clone())
    .collect::<Vec<_>>();
    assert!(matches!(
        mixed_deps.as_slice(),
        [
            GlobalRef::Imported { .. },
            GlobalRef::Local { .. },
            GlobalRef::LocalGenerated { .. },
            GlobalRef::Builtin { .. }
        ]
    ));
    assert_global_refs_are_in_canonical_byte_order(&mixed_deps);

    let mixed_axioms = union_axioms([
        AxiomRef {
            global_ref: GlobalRef::Builtin {
                name: 1,
                decl_interface_hash: [0x09; 32],
            },
            name: 1,
            decl_interface_hash: [0x09; 32],
        },
        AxiomRef {
            global_ref: GlobalRef::LocalGenerated {
                decl_index: 0,
                name: 2,
            },
            name: 2,
            decl_interface_hash: [0x0a; 32],
        },
        AxiomRef {
            global_ref: GlobalRef::Local { decl_index: 0 },
            name: 3,
            decl_interface_hash: [0x0b; 32],
        },
        AxiomRef {
            global_ref: GlobalRef::Imported {
                import_index: 0,
                name: 4,
                decl_interface_hash: [0x0c; 32],
            },
            name: 4,
            decl_interface_hash: [0x0c; 32],
        },
    ])
    .into_iter()
    .map(|axiom| axiom.global_ref)
    .collect::<Vec<_>>();
    assert!(matches!(
        mixed_axioms.as_slice(),
        [
            GlobalRef::Imported { .. },
            GlobalRef::Local { .. },
            GlobalRef::LocalGenerated { .. },
            GlobalRef::Builtin { .. }
        ]
    ));
    assert_global_refs_are_in_canonical_byte_order(&mixed_axioms);
}

#[test]
fn verified_module_can_be_imported_by_export_hash() {
    let id_cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let id_bytes = encode_module_cert(&id_cert).unwrap();
    let mut session = VerifierSession::new();
    let verified_id = verify_module_cert(&id_bytes, &mut session, &AxiomPolicy::normal()).unwrap();

    let use_id_cert = build_module_cert(use_id_module(), &[verified_id]).unwrap();
    assert_eq!(use_id_cert.imports().len(), 1);
    assert_eq!(
        use_id_cert.imports()[0].export_hash,
        id_cert.hashes().export_hash
    );

    let use_id_bytes = encode_module_cert(&use_id_cert).unwrap();
    let verified_use_id =
        verify_module_cert(&use_id_bytes, &mut session, &AxiomPolicy::normal()).unwrap();
    assert_eq!(verified_use_id.module(), &Name::from_dotted("Test.UseId"));
}

#[test]
fn verified_module_can_be_merged_as_high_trust_import() {
    let id_cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let id_bytes = encode_module_cert(&id_cert).unwrap();
    let verified_id = verify_module_cert(
        &id_bytes,
        &mut VerifierSession::new(),
        &AxiomPolicy::high_trust(),
    )
    .unwrap();
    let use_id_cert =
        build_module_cert(use_id_module(), std::slice::from_ref(&verified_id)).unwrap();
    let use_id_bytes = encode_module_cert(&use_id_cert).unwrap();

    let mut merged_session = VerifierSession::new();
    merged_session.register_verified_module_with_trust(verified_id, TrustMode::HighTrust);
    let verified_use_id = verify_module_cert(
        &use_id_bytes,
        &mut merged_session,
        &AxiomPolicy::high_trust(),
    )
    .unwrap();

    assert_eq!(verified_use_id.module(), &Name::from_dotted("Test.UseId"));
}

#[test]
fn duplicate_unused_imports_are_deduplicated_before_encoding() {
    let id_cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let id_bytes = encode_module_cert(&id_cert).unwrap();
    let mut session = VerifierSession::new();
    let verified_id = verify_module_cert(&id_bytes, &mut session, &AxiomPolicy::normal()).unwrap();

    let cert = build_module_cert(
        unary_inductive_module(),
        &[verified_id.clone(), verified_id],
    )
    .unwrap();
    assert_eq!(cert.imports().len(), 1);

    verify_module_cert(
        &encode_module_cert(&cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap();
}

#[test]
fn import_order_is_canonical_and_stable() {
    let mut session = VerifierSession::new();
    let alpha_cert = build_module_cert(named_axiom_module("Test.Alpha", "Alpha"), &[]).unwrap();
    let alpha = verify_module_cert(
        &encode_module_cert(&alpha_cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap();
    let beta_cert = build_module_cert(named_axiom_module("Test.Beta", "Beta"), &[]).unwrap();
    let beta = verify_module_cert(
        &encode_module_cert(&beta_cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap();

    let cert_ab =
        build_module_cert(use_two_axioms_module(), &[alpha.clone(), beta.clone()]).unwrap();
    let cert_ba = build_module_cert(use_two_axioms_module(), &[beta, alpha]).unwrap();

    assert_eq!(cert_ab.imports(), cert_ba.imports());
    assert_eq!(
        encode_module_cert(&cert_ab).unwrap(),
        encode_module_cert(&cert_ba).unwrap()
    );

    let mut noncanonical = cert_ab;
    noncanonical.mutate_parts_for_test(|parts| parts.imports.swap(0, 1));
    let certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&noncanonical),
    );
    noncanonical.mutate_parts_for_test(|parts| parts.hashes.certificate_hash = certificate_hash);
    let err = verify_module_cert(
        &encode_module_cert(&noncanonical).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap_err();
    assert!(matches!(
        err,
        CertError::NonCanonicalEncoding { object: "Imports" }
    ));
}

#[test]
fn declaration_order_is_canonical_and_stable() {
    let cert_ab = build_module_cert(ordered_axioms_module(&["A", "B"]), &[]).unwrap();
    let cert_ba = build_module_cert(ordered_axioms_module(&["B", "A"]), &[]).unwrap();

    assert_eq!(
        encode_module_cert(&cert_ab).unwrap(),
        encode_module_cert(&cert_ba).unwrap()
    );
    assert!(matches!(
        cert_ba.declarations()[0].decl,
        DeclPayload::Axiom { name, .. } if cert_ba.name_table()[name] == Name::from_dotted("A")
    ));
}

#[test]
fn declaration_names_are_committed_to_interface_and_export_hashes() {
    let p_cert = build_module_cert(named_axiom_module("Test.NamedAxiom", "P"), &[]).unwrap();
    let q_cert = build_module_cert(named_axiom_module("Test.NamedAxiom", "Q"), &[]).unwrap();

    assert_ne!(
        p_cert.declarations()[0].hashes.decl_interface_hash,
        q_cert.declarations()[0].hashes.decl_interface_hash
    );
    assert_ne!(p_cert.hashes().export_hash, q_cert.hashes().export_hash);
}

#[test]
fn rejects_unused_name_table_entry_even_if_rehashed() {
    let mut cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    cert.mutate_parts_for_test(|parts| parts.name_table.push(Name::from_dotted("zz.unused")));
    let certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&cert),
    );
    cert.mutate_parts_for_test(|parts| parts.hashes.certificate_hash = certificate_hash);

    let mut session = VerifierSession::new();
    let err = verify_module_cert(
        &encode_module_cert(&cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap_err();
    assert!(matches!(
        err,
        CertError::NonCanonicalEncoding {
            object: "NameTable"
        }
    ));
}

#[test]
fn verifier_rejects_noncanonical_declaration_order_even_if_rehashed() {
    let mut cert = build_module_cert(ordered_axioms_module(&["A", "B"]), &[]).unwrap();
    cert.mutate_parts_for_test(|parts| parts.declarations.swap(0, 1));
    let certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&cert),
    );
    cert.mutate_parts_for_test(|parts| parts.hashes.certificate_hash = certificate_hash);

    let mut session = VerifierSession::new();
    let err = verify_module_cert(
        &encode_module_cert(&cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap_err();
    assert!(matches!(
        err,
        CertError::NonCanonicalEncoding {
            object: "Declarations"
        }
    ));
}

#[test]
fn forward_source_dependency_is_canonicalized_before_verification() {
    let cert = build_module_cert(forward_axiom_dependency_module(), &[]).unwrap();
    assert!(matches!(
        cert.declarations()[0].decl,
        DeclPayload::Axiom { name, .. } if cert.name_table()[name] == Name::from_dotted("P")
    ));
    assert!(cert.declarations()[1]
        .dependencies
        .iter()
        .any(|dependency| matches!(dependency.global_ref(), GlobalRef::Local { decl_index: 0 })));

    let mut session = VerifierSession::new();
    verify_module_cert(
        &encode_module_cert(&cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap();
}

#[test]
fn build_rejects_source_names_with_empty_components() {
    let module_name_err = build_module_cert(
        CoreModule {
            name: Name::from_dotted("Test..Bad"),
            declarations: vec![],
        },
        &[],
    )
    .unwrap_err();
    assert!(matches!(
        module_name_err,
        CertError::NonCanonicalEncoding { object: "Name" }
    ));

    let decl_name_err = build_module_cert(
        CoreModule {
            name: Name::from_dotted("Test.Bad"),
            declarations: vec![Decl::Axiom {
                name: "A..B".to_owned(),
                universe_params: vec![],
                ty: Expr::sort(Level::zero()),
            }],
        },
        &[],
    )
    .unwrap_err();
    assert!(matches!(
        decl_name_err,
        CertError::NonCanonicalEncoding { object: "Name" }
    ));
}

#[test]
fn imported_axioms_are_reported_in_caller_certificate() {
    let p_cert = build_module_cert(axiom_module(), &[]).unwrap();
    let mut session = VerifierSession::new();
    let mut policy = AxiomPolicy::high_trust();
    policy.allowlisted_axioms.insert(Name::from_dotted("P"));
    let verified_p =
        verify_module_cert(&encode_module_cert(&p_cert).unwrap(), &mut session, &policy).unwrap();

    let use_p_cert = build_module_cert(use_axiom_module(), &[verified_p]).unwrap();
    assert_eq!(use_p_cert.axiom_report().module_axioms.len(), 1);
    let axiom = &use_p_cert.axiom_report().module_axioms[0];
    assert_eq!(use_p_cert.name_table()[axiom.name], Name::from_dotted("P"));
    assert!(matches!(
        axiom.global_ref,
        GlobalRef::Imported {
            import_index: 0,
            ..
        }
    ));

    verify_module_cert(
        &encode_module_cert(&use_p_cert).unwrap(),
        &mut session,
        &policy,
    )
    .unwrap();
}

#[test]
fn transitive_imported_axiom_provenance_points_to_original_import() {
    let p_cert = build_module_cert(axiom_module(), &[]).unwrap();
    let mut session = VerifierSession::new();
    let verified_p = verify_module_cert(
        &encode_module_cert(&p_cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap();

    let use_p_cert =
        build_module_cert(use_axiom_module(), std::slice::from_ref(&verified_p)).unwrap();
    let verified_use_p = verify_module_cert(
        &encode_module_cert(&use_p_cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap();

    let use_use_p_cert =
        build_module_cert(use_imported_use_p_module(), &[verified_use_p, verified_p]).unwrap();
    let p_import_index = use_use_p_cert
        .imports()
        .iter()
        .position(|import| import.module == Name::from_dotted("Test.Axiom"))
        .unwrap();
    let use_p_import_index = use_use_p_cert
        .imports()
        .iter()
        .position(|import| import.module == Name::from_dotted("Test.UseAxiom"))
        .unwrap();
    let axiom = use_use_p_cert
        .axiom_report()
        .module_axioms
        .iter()
        .find(|axiom| use_use_p_cert.name_table()[axiom.name] == Name::from_dotted("P"))
        .unwrap();

    assert!(matches!(
        axiom.global_ref,
        GlobalRef::Imported { import_index, .. } if import_index == p_import_index
    ));
    assert!(matches!(
        axiom.global_ref,
        GlobalRef::Imported { import_index, .. } if import_index != use_p_import_index
    ));
    verify_module_cert(
        &encode_module_cert(&use_use_p_cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap();
}

#[test]
fn transitive_imported_builtin_axioms_remain_builtin() {
    let eq_rec_alias_cert = build_module_cert(eq_rec_alias_module(), &[]).unwrap();
    let mut session = VerifierSession::new();
    let verified_eq_rec_alias = verify_module_cert(
        &encode_module_cert(&eq_rec_alias_cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap();

    let use_alias_cert =
        build_module_cert(use_imported_eq_rec_alias_module(), &[verified_eq_rec_alias]).unwrap();
    let axiom = use_alias_cert
        .axiom_report()
        .module_axioms
        .iter()
        .find(|axiom| use_alias_cert.name_table()[axiom.name] == Name::from_dotted("Eq.rec"))
        .expect("downstream module should report the builtin Eq.rec axiom");

    assert!(matches!(axiom.global_ref, GlobalRef::Builtin { .. }));
    assert!(matches!(
        use_alias_cert.declarations()[0]
            .axiom_dependencies
            .as_slice(),
        [AxiomRef {
            global_ref: GlobalRef::Builtin { .. },
            ..
        }]
    ));
    verify_module_cert(
        &encode_module_cert(&use_alias_cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap();
}

#[test]
fn current_builtin_eq_rec_can_coexist_with_imported_eq_shape() {
    let eq_cert = build_module_cert(eq_axiom_module_without_rec(), &[]).unwrap();
    let mut session = VerifierSession::new();
    let verified_eq = verify_module_cert(
        &encode_module_cert(&eq_cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap();

    let use_eq_rec_cert =
        build_module_cert(use_builtin_eq_rec_with_imported_eq_module(), &[verified_eq]).unwrap();
    let axiom = use_eq_rec_cert
        .axiom_report()
        .module_axioms
        .iter()
        .find(|axiom| use_eq_rec_cert.name_table()[axiom.name] == Name::from_dotted("Eq.rec"))
        .expect("current module should report the builtin Eq.rec axiom");

    assert!(matches!(axiom.global_ref, GlobalRef::Builtin { .. }));
    verify_module_cert(
        &encode_module_cert(&use_eq_rec_cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap();
}

#[test]
fn current_builtin_eq_rec_remains_builtin_when_import_exports_builtin_eq_rec() {
    let eq_cert = build_module_cert(eq_module(), &[]).unwrap();
    let mut session = VerifierSession::new();
    let verified_eq = verify_module_cert(
        &encode_module_cert(&eq_cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap();

    let use_eq_rec_cert =
        build_module_cert(use_builtin_eq_rec_with_imported_eq_module(), &[verified_eq]).unwrap();
    let axiom = use_eq_rec_cert
        .axiom_report()
        .module_axioms
        .iter()
        .find(|axiom| use_eq_rec_cert.name_table()[axiom.name] == Name::from_dotted("Eq.rec"))
        .expect("current module should report the builtin Eq.rec axiom");

    assert!(matches!(axiom.global_ref, GlobalRef::Builtin { .. }));
    verify_module_cert(
        &encode_module_cert(&use_eq_rec_cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap();
}

#[test]
fn imported_builtin_eq_rec_dependency_can_coexist_with_imported_eq_shape() {
    let eq_cert = build_module_cert(eq_module(), &[]).unwrap();
    let mut session = VerifierSession::new();
    let verified_eq = verify_module_cert(
        &encode_module_cert(&eq_cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap();

    let eq_rec_alias_cert =
        build_module_cert(eq_rec_alias_module(), std::slice::from_ref(&verified_eq)).unwrap();
    let verified_eq_rec_alias = verify_module_cert(
        &encode_module_cert(&eq_rec_alias_cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap();

    let use_alias_cert = build_module_cert(
        use_imported_eq_rec_alias_module(),
        &[verified_eq.clone(), verified_eq_rec_alias],
    )
    .unwrap();
    verify_module_cert(
        &encode_module_cert(&use_alias_cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap();
}

#[test]
fn import_export_name_matching_module_name_does_not_pull_unused_axioms() {
    let p_cert = build_module_cert(axiom_module(), &[]).unwrap();
    let mut session = VerifierSession::new();
    let verified_p = verify_module_cert(
        &encode_module_cert(&p_cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap();

    let use_p_cert =
        build_module_cert(use_axiom_module(), std::slice::from_ref(&verified_p)).unwrap();
    let verified_use_p = verify_module_cert(
        &encode_module_cert(&use_p_cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap();

    let mut module = unary_inductive_module();
    module.name = Name::from_dotted("use_p");
    let cert = build_module_cert(module, &[verified_use_p, verified_p]).unwrap();
    assert!(!cert.name_table().contains(&Name::from_dotted("P")));

    verify_module_cert(
        &encode_module_cert(&cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap();
}

#[test]
fn downstream_import_uses_export_block_not_hidden_certificate_body_deps() {
    let helper_cert = build_module_cert(hidden_proof_helper_module(), &[]).unwrap();
    let mut session = VerifierSession::new();
    let verified_helper = verify_module_cert(
        &encode_module_cert(&helper_cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap();

    let public_id_cert = build_module_cert(
        public_id_with_hidden_import_proof_module(),
        &[verified_helper],
    )
    .unwrap();
    let verified_public_id = verify_module_cert(
        &encode_module_cert(&public_id_cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap();

    let use_public_id_cert = build_module_cert(use_public_id_module(), &[verified_public_id])
        .expect("hidden theorem and opaque def imports must not be required downstream");
    assert_eq!(use_public_id_cert.imports().len(), 1);
    assert_eq!(
        use_public_id_cert.imports()[0].module,
        Name::from_dotted("Test.PublicIdWithHiddenProof")
    );
    verify_module_cert(
        &encode_module_cert(&use_public_id_cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .expect("verifier must rebuild import env from public export entries");
}

#[test]
fn opaque_theorem_proof_change_keeps_export_hash_when_axioms_do_not_change() {
    let cert_a = build_module_cert(id_theorem_module(id_value("A", "x")), &[]).unwrap();
    let cert_b = build_module_cert(id_theorem_module(id_value_with_beta_redex()), &[]).unwrap();

    assert_eq!(
        cert_a.declarations()[0].hashes.decl_interface_hash,
        cert_b.declarations()[0].hashes.decl_interface_hash
    );
    assert_ne!(
        cert_a.declarations()[0].hashes.decl_certificate_hash,
        cert_b.declarations()[0].hashes.decl_certificate_hash
    );
    assert_eq!(cert_a.hashes().export_hash, cert_b.hashes().export_hash);
    assert_eq!(
        cert_a.hashes().axiom_report_hash,
        cert_b.hashes().axiom_report_hash
    );
    assert_ne!(
        cert_a.hashes().certificate_hash,
        cert_b.hashes().certificate_hash
    );
}

#[test]
fn opaque_def_body_change_keeps_interface_and_export_hashes() {
    let cert_a = build_module_cert(
        id_def_module_with_value_and_reducibility(id_value("A", "x"), Reducibility::Opaque),
        &[],
    )
    .unwrap();
    let cert_b = build_module_cert(
        id_def_module_with_value_and_reducibility(id_value_with_beta_redex(), Reducibility::Opaque),
        &[],
    )
    .unwrap();

    assert_eq!(
        cert_a.declarations()[0].hashes.decl_interface_hash,
        cert_b.declarations()[0].hashes.decl_interface_hash
    );
    assert_ne!(
        cert_a.declarations()[0].hashes.decl_certificate_hash,
        cert_b.declarations()[0].hashes.decl_certificate_hash
    );
    assert_eq!(cert_a.hashes().export_hash, cert_b.hashes().export_hash);
    assert_ne!(
        cert_a.hashes().certificate_hash,
        cert_b.hashes().certificate_hash
    );
}

#[test]
fn transparent_def_body_change_changes_interface_and_export_hashes() {
    let cert_a = build_module_cert(id_def_module_with_value(id_value("A", "x")), &[]).unwrap();
    let cert_b =
        build_module_cert(id_def_module_with_value(id_value_with_beta_redex()), &[]).unwrap();

    assert_ne!(
        cert_a.declarations()[0].hashes.decl_interface_hash,
        cert_b.declarations()[0].hashes.decl_interface_hash
    );
    assert_ne!(
        cert_a.declarations()[0].hashes.decl_certificate_hash,
        cert_b.declarations()[0].hashes.decl_certificate_hash
    );
    assert_ne!(cert_a.hashes().export_hash, cert_b.hashes().export_hash);
    assert_ne!(
        cert_a.hashes().certificate_hash,
        cert_b.hashes().certificate_hash
    );
}

#[test]
fn import_certificate_rebind_matches_ordinary_rebuild_for_export_stable_provider() {
    let old_provider = build_module_cert(
        id_def_module_with_value_and_reducibility(id_value("A", "x"), Reducibility::Opaque),
        &[],
    )
    .unwrap();
    let new_provider = build_module_cert(
        id_def_module_with_value_and_reducibility(id_value_with_beta_redex(), Reducibility::Opaque),
        &[],
    )
    .unwrap();
    let policy = AxiomPolicy::normal();
    let old_verified = verify_module_cert_with_import_refs(
        &encode_module_cert(&old_provider).unwrap(),
        &[],
        &policy,
    )
    .unwrap();
    let new_verified = verify_module_cert_with_import_refs(
        &encode_module_cert(&new_provider).unwrap(),
        &[],
        &policy,
    )
    .unwrap();
    assert_eq!(old_verified.export_hash(), new_verified.export_hash());
    assert_ne!(
        old_verified.certificate_hash(),
        new_verified.certificate_hash()
    );

    let dependent = build_module_cert(use_id_module(), &[old_verified]).unwrap();
    let dependent_bytes = encode_module_cert(&dependent).unwrap();
    assert!(matches!(
        verify_module_cert_with_import_refs(&dependent_bytes, &[&new_verified], &policy),
        Err(CertError::ImportCertificateHashMismatch { .. })
    ));
    let expected = ModuleCertRebindExpectedIdentity {
        module: dependent.header().module.clone(),
        export_hash: dependent.hashes().export_hash,
        axiom_report_hash: dependent.hashes().axiom_report_hash,
        certificate_hash: dependent.hashes().certificate_hash,
    };

    let outcome = rebind_module_cert_import_certificate_hashes(
        &dependent_bytes,
        &expected,
        &[ModuleCertRebindImport {
            verified: &new_verified,
            origin: ModuleCertRebindImportOrigin::Local,
        }],
        &policy,
    )
    .unwrap();
    let ModuleCertImportRebindOutcome::Rebound {
        certificate,
        bytes,
        verified,
        changed_imports,
    } = outcome
    else {
        panic!("expected rebound certificate");
    };

    assert_eq!(changed_imports, vec![Name::from_dotted("Test.Id")]);
    assert_eq!(
        certificate.hashes().export_hash,
        dependent.hashes().export_hash
    );
    assert_eq!(
        certificate.hashes().axiom_report_hash,
        dependent.hashes().axiom_report_hash
    );
    assert_ne!(
        certificate.hashes().certificate_hash,
        dependent.hashes().certificate_hash
    );
    assert_eq!(
        verified.certificate_hash(),
        certificate.hashes().certificate_hash
    );
    let rebuilt = build_module_cert(use_id_module(), &[new_verified]).unwrap();
    assert_eq!(bytes, encode_module_cert(&rebuilt).unwrap());
}

#[test]
fn import_certificate_rebind_v0_4_preserves_payload_and_matches_ordinary_rebuild() {
    let build_v0_4 = |module, imports: &[&VerifiedModule]| {
        build_module_cert_from_import_refs_with_preferred_imports(
            module,
            imports,
            &std::collections::BTreeMap::new(),
        )
        .unwrap()
    };
    let old_provider = build_v0_4(
        id_def_module_with_value_and_reducibility(id_value("A", "x"), Reducibility::Opaque),
        &[],
    );
    let new_provider = build_v0_4(
        id_def_module_with_value_and_reducibility(id_value_with_beta_redex(), Reducibility::Opaque),
        &[],
    );
    let policy = AxiomPolicy::normal();
    let old_verified = verify_module_cert_with_import_refs(
        &encode_module_cert(&old_provider).unwrap(),
        &[],
        &policy,
    )
    .unwrap();
    let new_verified = verify_module_cert_with_import_refs(
        &encode_module_cert(&new_provider).unwrap(),
        &[],
        &policy,
    )
    .unwrap();
    assert_eq!(old_verified.export_hash(), new_verified.export_hash());
    assert_ne!(
        old_verified.certificate_hash(),
        new_verified.certificate_hash()
    );

    let dependent = build_v0_4(use_id_module(), &[&old_verified]);
    let dependent_bytes = encode_module_cert(&dependent).unwrap();
    let expected = ModuleCertRebindExpectedIdentity {
        module: dependent.header().module.clone(),
        export_hash: dependent.hashes().export_hash,
        axiom_report_hash: dependent.hashes().axiom_report_hash,
        certificate_hash: dependent.hashes().certificate_hash,
    };
    let outcome = rebind_module_cert_import_certificate_hashes(
        &dependent_bytes,
        &expected,
        &[ModuleCertRebindImport {
            verified: &new_verified,
            origin: ModuleCertRebindImportOrigin::Local,
        }],
        &policy,
    )
    .unwrap();
    let ModuleCertImportRebindOutcome::Rebound {
        certificate,
        bytes,
        verified,
        changed_imports,
    } = outcome
    else {
        panic!("expected v0.3 rebound certificate");
    };

    assert_eq!(certificate.header().format, FORMAT);
    assert_eq!(certificate.header().core_spec, CORE_SPEC);
    assert_eq!(changed_imports, vec![Name::from_dotted("Test.Id")]);
    assert_eq!(certificate.declarations(), dependent.declarations());
    assert_eq!(certificate.name_table(), dependent.name_table());
    assert_eq!(certificate.level_table(), dependent.level_table());
    assert_eq!(certificate.term_table(), dependent.term_table());
    assert_eq!(certificate.export_block(), dependent.export_block());
    assert_eq!(certificate.axiom_report(), dependent.axiom_report());
    assert_eq!(
        certificate.hashes().export_hash,
        dependent.hashes().export_hash
    );
    assert_eq!(
        certificate.hashes().axiom_report_hash,
        dependent.hashes().axiom_report_hash
    );
    assert_ne!(
        certificate.hashes().certificate_hash,
        dependent.hashes().certificate_hash
    );
    assert_eq!(
        verified.certificate_hash(),
        certificate.hashes().certificate_hash
    );

    let rebuilt = build_v0_4(use_id_module(), &[&new_verified]);
    assert_eq!(bytes, encode_module_cert(&rebuilt).unwrap());
}

#[test]
fn import_certificate_rebind_v0_4_rejects_stale_local_implementation_dependency() {
    let mut stale = v0_4_opaque_alias_cert_with_local_implementation_dependency();
    let (consumer, dependency_index) = first_local_dependency(&stale);
    let dependency = &stale.declarations()[consumer].dependencies[dependency_index];
    let global_ref = dependency.global_ref().clone();
    let interface_hash = dependency.decl_interface_hash();
    let mut stale_certificate_hash = dependency.decl_certificate_hash().unwrap();
    stale_certificate_hash[0] ^= 0x01;
    replace_first_local_dependency_with_raw_implementation(
        &mut stale,
        global_ref,
        interface_hash,
        stale_certificate_hash,
    );
    let expected = ModuleCertRebindExpectedIdentity {
        module: stale.header().module.clone(),
        export_hash: stale.hashes().export_hash,
        axiom_report_hash: stale.hashes().axiom_report_hash,
        certificate_hash: stale.hashes().certificate_hash,
    };

    let error = rebind_module_cert_import_certificate_hashes(
        &encode_module_cert(&stale).unwrap(),
        &expected,
        &[],
        &AxiomPolicy::normal(),
    )
    .unwrap_err();

    assert!(matches!(
        error,
        ModuleCertImportRebindError::Certificate(CertError::InvalidLocalImplementationDependency {
            reason: LocalImplementationDependencyErrorReason::CertificateHashMismatch,
            ..
        })
    ));
}

#[test]
fn import_certificate_rebind_returns_unchanged_after_live_verification() {
    let provider = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let policy = AxiomPolicy::normal();
    let verified_provider =
        verify_module_cert_with_import_refs(&encode_module_cert(&provider).unwrap(), &[], &policy)
            .unwrap();
    let dependent =
        build_module_cert(use_id_module(), std::slice::from_ref(&verified_provider)).unwrap();
    let bytes = encode_module_cert(&dependent).unwrap();
    let expected = ModuleCertRebindExpectedIdentity {
        module: dependent.header().module.clone(),
        export_hash: dependent.hashes().export_hash,
        axiom_report_hash: dependent.hashes().axiom_report_hash,
        certificate_hash: dependent.hashes().certificate_hash,
    };

    let outcome = rebind_module_cert_import_certificate_hashes(
        &bytes,
        &expected,
        &[ModuleCertRebindImport {
            verified: &verified_provider,
            origin: ModuleCertRebindImportOrigin::Local,
        }],
        &policy,
    )
    .unwrap();

    let ModuleCertImportRebindOutcome::Unchanged {
        certificate,
        verified,
    } = outcome
    else {
        panic!("expected unchanged certificate");
    };
    assert_eq!(certificate, dependent);
    assert_eq!(
        verified.certificate_hash(),
        dependent.hashes().certificate_hash
    );
}

#[test]
fn import_certificate_rebind_reports_local_export_change() {
    let old_provider = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let new_provider =
        build_module_cert(id_def_module_with_value(id_value_with_beta_redex()), &[]).unwrap();
    let policy = AxiomPolicy::normal();
    let old_verified = verify_module_cert_with_import_refs(
        &encode_module_cert(&old_provider).unwrap(),
        &[],
        &policy,
    )
    .unwrap();
    let new_verified = verify_module_cert_with_import_refs(
        &encode_module_cert(&new_provider).unwrap(),
        &[],
        &policy,
    )
    .unwrap();
    let dependent = build_module_cert(use_id_module(), &[old_verified]).unwrap();
    let bytes = encode_module_cert(&dependent).unwrap();
    let expected = ModuleCertRebindExpectedIdentity {
        module: dependent.header().module.clone(),
        export_hash: dependent.hashes().export_hash,
        axiom_report_hash: dependent.hashes().axiom_report_hash,
        certificate_hash: dependent.hashes().certificate_hash,
    };

    let outcome = rebind_module_cert_import_certificate_hashes(
        &bytes,
        &expected,
        &[ModuleCertRebindImport {
            verified: &new_verified,
            origin: ModuleCertRebindImportOrigin::Local,
        }],
        &policy,
    )
    .unwrap();

    assert_eq!(
        outcome,
        ModuleCertImportRebindOutcome::ExportChanged {
            module: Name::from_dotted("Test.Id"),
            expected: old_provider.hashes().export_hash,
            actual: new_provider.hashes().export_hash,
        }
    );
}

#[test]
fn import_certificate_rebind_prioritizes_external_identity_failure_in_any_import_order() {
    let old_local = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let new_local =
        build_module_cert(id_def_module_with_value(id_value_with_beta_redex()), &[]).unwrap();
    let policy = AxiomPolicy::normal();
    let old_verified_local =
        verify_module_cert_with_import_refs(&encode_module_cert(&old_local).unwrap(), &[], &policy)
            .unwrap();
    let new_verified_local =
        verify_module_cert_with_import_refs(&encode_module_cert(&new_local).unwrap(), &[], &policy)
            .unwrap();

    for external_module in ["A.External", "Z.External"] {
        let external_with_value = |value| CoreModule {
            name: Name::from_dotted(external_module),
            declarations: vec![Decl::Def {
                name: "external_id".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: id_type("A", "x"),
                value,
                reducibility: Reducibility::Opaque,
            }],
        };
        let old_external = build_module_cert(external_with_value(id_value("A", "x")), &[]).unwrap();
        let new_external =
            build_module_cert(external_with_value(id_value_with_beta_redex()), &[]).unwrap();
        assert_eq!(
            old_external.hashes().export_hash,
            new_external.hashes().export_hash
        );
        assert_ne!(
            old_external.hashes().certificate_hash,
            new_external.hashes().certificate_hash
        );
        let old_verified_external = verify_module_cert_with_import_refs(
            &encode_module_cert(&old_external).unwrap(),
            &[],
            &policy,
        )
        .unwrap();
        let new_verified_external = verify_module_cert_with_import_refs(
            &encode_module_cert(&new_external).unwrap(),
            &[],
            &policy,
        )
        .unwrap();
        let dependent = build_module_cert(
            use_id_module(),
            &[old_verified_local.clone(), old_verified_external],
        )
        .unwrap();
        let external_index = dependent
            .imports()
            .iter()
            .position(|import| import.module == Name::from_dotted(external_module))
            .unwrap();
        let local_index = dependent
            .imports()
            .iter()
            .position(|import| import.module == Name::from_dotted("Test.Id"))
            .unwrap();
        assert_eq!(
            external_index < local_index,
            external_module == "A.External"
        );
        let bytes = encode_module_cert(&dependent).unwrap();
        let expected = ModuleCertRebindExpectedIdentity {
            module: dependent.header().module.clone(),
            export_hash: dependent.hashes().export_hash,
            axiom_report_hash: dependent.hashes().axiom_report_hash,
            certificate_hash: dependent.hashes().certificate_hash,
        };

        let error = rebind_module_cert_import_certificate_hashes(
            &bytes,
            &expected,
            &[
                ModuleCertRebindImport {
                    verified: &new_verified_local,
                    origin: ModuleCertRebindImportOrigin::Local,
                },
                ModuleCertRebindImport {
                    verified: &new_verified_external,
                    origin: ModuleCertRebindImportOrigin::External,
                },
            ],
            &policy,
        )
        .unwrap_err();

        assert_eq!(
            error,
            ModuleCertImportRebindError::ExternalIdentityChanged {
                module: Name::from_dotted(external_module)
            }
        );
    }
}

#[test]
fn import_certificate_rebind_rejects_duplicate_certificate_module_before_mapped_duplicates() {
    let old_provider = build_module_cert(
        id_def_module_with_value_and_reducibility(id_value("A", "x"), Reducibility::Opaque),
        &[],
    )
    .unwrap();
    let new_provider = build_module_cert(
        id_def_module_with_value_and_reducibility(id_value_with_beta_redex(), Reducibility::Opaque),
        &[],
    )
    .unwrap();
    let policy = AxiomPolicy::normal();
    let old_verified = verify_module_cert_with_import_refs(
        &encode_module_cert(&old_provider).unwrap(),
        &[],
        &policy,
    )
    .unwrap();
    let new_verified = verify_module_cert_with_import_refs(
        &encode_module_cert(&new_provider).unwrap(),
        &[],
        &policy,
    )
    .unwrap();
    let mut dependent =
        build_module_cert(use_id_module(), std::slice::from_ref(&old_verified)).unwrap();
    dependent.mutate_parts_for_test(|parts| {
        parts.imports.push(ImportEntry {
            module: new_verified.module().clone(),
            export_hash: new_verified.export_hash(),
            certificate_hash: Some(new_verified.certificate_hash()),
        });
        parts.imports.sort_by_key(|import| {
            (
                import.module.clone(),
                import.export_hash,
                import.certificate_hash,
            )
        });
    });
    let certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&dependent),
    );
    dependent.mutate_parts_for_test(|parts| parts.hashes.certificate_hash = certificate_hash);
    let bytes = encode_module_cert(&dependent).unwrap();
    let expected = ModuleCertRebindExpectedIdentity {
        module: dependent.header().module.clone(),
        export_hash: dependent.hashes().export_hash,
        axiom_report_hash: dependent.hashes().axiom_report_hash,
        certificate_hash: dependent.hashes().certificate_hash,
    };

    let error = rebind_module_cert_import_certificate_hashes(
        &bytes,
        &expected,
        &[
            ModuleCertRebindImport {
                verified: &old_verified,
                origin: ModuleCertRebindImportOrigin::Local,
            },
            ModuleCertRebindImport {
                verified: &new_verified,
                origin: ModuleCertRebindImportOrigin::Local,
            },
        ],
        &policy,
    )
    .unwrap_err();

    assert_eq!(
        error,
        ModuleCertImportRebindError::DuplicateCertificateImport {
            module: Name::from_dotted("Test.Id")
        }
    );
}

#[test]
fn decl_interface_hash_def_payload_order_matches_certificate_contract() {
    let fixture = hash_contract_def_fixture();
    let hashes = compute_decl_hashes(
        CertificateFormatVersion::V0_4_0,
        &fixture.decl,
        &fixture.dependencies,
        &fixture.axiom_dependencies,
        DeclHashTables {
            terms: &fixture.term_table,
            level_hashes: &[],
            term_hashes: &fixture.term_hashes,
            names: &fixture.names,
        },
    )
    .unwrap();
    let DeclPayload::Def {
        name,
        universe_params,
        ty,
        value,
        reducibility,
    } = &fixture.decl
    else {
        panic!("expected def payload");
    };

    let mut expected = Vec::new();
    expected.push(0x01);
    append_name_id(&mut expected, &fixture.names, *name);
    append_name_ids(&mut expected, &fixture.names, universe_params);
    expected.extend_from_slice(&fixture.term_hashes[*ty]);
    encode_reducibility_to(&mut expected, *reducibility);
    encode_dependency_entries_to(&mut expected, &fixture.dependencies);
    encode_axiom_refs_to(&mut expected, &fixture.axiom_dependencies);
    expected.extend_from_slice(&fixture.term_hashes[*value]);
    assert_eq!(
        hashes.decl_interface_hash,
        hash_with_domain(b"NPA-DECL-IFACE-0.1", &expected)
    );

    let mut legacy_value_before_reducibility = Vec::new();
    legacy_value_before_reducibility.push(0x01);
    append_name_id(&mut legacy_value_before_reducibility, &fixture.names, *name);
    append_name_ids(
        &mut legacy_value_before_reducibility,
        &fixture.names,
        universe_params,
    );
    legacy_value_before_reducibility.extend_from_slice(&fixture.term_hashes[*ty]);
    legacy_value_before_reducibility.extend_from_slice(&fixture.term_hashes[*value]);
    encode_reducibility_to(&mut legacy_value_before_reducibility, *reducibility);
    encode_dependency_entries_to(&mut legacy_value_before_reducibility, &fixture.dependencies);
    encode_axiom_refs_to(
        &mut legacy_value_before_reducibility,
        &fixture.axiom_dependencies,
    );
    assert_ne!(
        hashes.decl_interface_hash,
        hash_with_domain(b"NPA-DECL-IFACE-0.1", &legacy_value_before_reducibility)
    );
}

#[test]
fn reducible_def_decl_certificate_hash_includes_value_hash_directly() {
    let fixture = hash_contract_def_fixture();
    let hashes = compute_decl_hashes(
        CertificateFormatVersion::V0_4_0,
        &fixture.decl,
        &fixture.dependencies,
        &fixture.axiom_dependencies,
        DeclHashTables {
            terms: &fixture.term_table,
            level_hashes: &[],
            term_hashes: &fixture.term_hashes,
            names: &fixture.names,
        },
    )
    .unwrap();
    let DeclPayload::Def { value, .. } = &fixture.decl else {
        panic!("expected def payload");
    };
    let value = *value;

    let mut expected = Vec::new();
    expected.extend_from_slice(&hashes.decl_interface_hash);
    expected.extend_from_slice(&fixture.term_hashes[value]);
    encode_dependency_entries_with_format_to(
        &mut expected,
        &fixture.dependencies,
        CertificateFormatVersion::V0_4_0,
    );
    encode_axiom_refs_to(&mut expected, &fixture.axiom_dependencies);
    assert_eq!(
        hashes.decl_certificate_hash,
        hash_with_domain(DECL_CERT_DOMAIN, &expected)
    );

    let mut changed_value_hash = Vec::new();
    changed_value_hash.extend_from_slice(&hashes.decl_interface_hash);
    changed_value_hash.extend_from_slice(&test_hash(0x21));
    encode_dependency_entries_with_format_to(
        &mut changed_value_hash,
        &fixture.dependencies,
        CertificateFormatVersion::V0_4_0,
    );
    encode_axiom_refs_to(&mut changed_value_hash, &fixture.axiom_dependencies);
    assert_ne!(
        hashes.decl_certificate_hash,
        hash_with_domain(DECL_CERT_DOMAIN, &changed_value_hash)
    );

    let mut legacy_without_direct_value_hash = Vec::new();
    legacy_without_direct_value_hash.extend_from_slice(&hashes.decl_interface_hash);
    encode_dependency_entries_with_format_to(
        &mut legacy_without_direct_value_hash,
        &fixture.dependencies,
        CertificateFormatVersion::V0_4_0,
    );
    encode_axiom_refs_to(
        &mut legacy_without_direct_value_hash,
        &fixture.axiom_dependencies,
    );
    assert_ne!(
        hashes.decl_certificate_hash,
        hash_with_domain(DECL_CERT_DOMAIN, &legacy_without_direct_value_hash)
    );
}

#[test]
fn local_transparent_dependency_change_propagates_to_dependents() {
    let cert_a =
        build_module_cert(local_transparent_alias_module(id_value("A", "x")), &[]).unwrap();
    let cert_b = build_module_cert(
        local_transparent_alias_module(id_value_with_beta_redex()),
        &[],
    )
    .unwrap();
    let alias_a = cert_a
        .declarations()
        .iter()
        .find(|decl| {
            matches!(
                &decl.decl,
                DeclPayload::Def { name, .. }
                    if cert_a.name_table()[*name] == Name::from_dotted("alias")
            )
        })
        .unwrap();
    let alias_b = cert_b
        .declarations()
        .iter()
        .find(|decl| {
            matches!(
                &decl.decl,
                DeclPayload::Def { name, .. }
                    if cert_b.name_table()[*name] == Name::from_dotted("alias")
            )
        })
        .unwrap();

    assert_ne!(
        alias_a.hashes.decl_interface_hash,
        alias_b.hashes.decl_interface_hash
    );
    assert_ne!(cert_a.hashes().export_hash, cert_b.hashes().export_hash);
}

#[test]
fn opaque_theorem_axiom_change_changes_export_hash() {
    let cert_p1 = build_module_cert(theorem_using_axiom_module("p1"), &[]).unwrap();
    let cert_p2 = build_module_cert(theorem_using_axiom_module("p2"), &[]).unwrap();

    assert_ne!(cert_p1.hashes().export_hash, cert_p2.hashes().export_hash);
    assert_ne!(
        cert_p1.axiom_report().per_declaration[3].transitive_axioms,
        cert_p2.axiom_report().per_declaration[3].transitive_axioms
    );
}

#[test]
fn axiom_policy_rejects_forbidden_and_sorry_axioms() {
    let cert = build_module_cert(axiom_module(), &[]).unwrap();
    let mut session = VerifierSession::new();
    let err = verify_module_cert(
        &encode_module_cert(&cert).unwrap(),
        &mut session,
        &AxiomPolicy::high_trust(),
    )
    .unwrap_err();
    assert!(matches!(err, CertError::ForbiddenAxiom { .. }));

    let sorry_cert =
        build_module_cert(named_axiom_module("Test.Sorry", "sorry.synthetic"), &[]).unwrap();
    let err = verify_module_cert(
        &encode_module_cert(&sorry_cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap_err();
    assert!(matches!(err, CertError::SorryDenied { .. }));
}

#[test]
fn axiom_policy_hashes_are_stable_for_builtin_profiles() {
    assert_eq!(
        hash_hex(AxiomPolicy::normal().policy_hash()),
        "b195e18703438ff970cd3219474b365bfccf147d27814c3a3ccca5fdbbffbe64"
    );
    assert_eq!(
        hash_hex(AxiomPolicy::high_trust().policy_hash()),
        "6a6d19b138e6b38b85067c3eee92667880ff77c52f091163b9647bfc2e85509d"
    );
}

#[test]
fn axiom_policy_canonical_bytes_sort_allowlist_and_change_by_policy() {
    let mut policy_ab = AxiomPolicy::high_trust();
    policy_ab.allowlisted_axioms.insert(Name::from_dotted("B"));
    policy_ab.allowlisted_axioms.insert(Name::from_dotted("A"));

    let mut policy_ba = AxiomPolicy::high_trust();
    policy_ba.allowlisted_axioms.insert(Name::from_dotted("A"));
    policy_ba.allowlisted_axioms.insert(Name::from_dotted("B"));

    assert_eq!(policy_ab.canonical_bytes(), policy_ba.canonical_bytes());
    assert_eq!(policy_ab.policy_hash(), policy_ba.policy_hash());

    let mut policy_abc = policy_ab.clone();
    policy_abc.allowlisted_axioms.insert(Name::from_dotted("C"));
    assert_ne!(policy_ab.policy_hash(), policy_abc.policy_hash());

    let mut allow_with_sorry = policy_ab.clone();
    allow_with_sorry.deny_sorry = false;
    assert_ne!(policy_ab.policy_hash(), allow_with_sorry.policy_hash());
    assert_ne!(
        AxiomPolicy::normal().policy_hash(),
        AxiomPolicy::high_trust().policy_hash()
    );
}

#[test]
fn axiom_policy_hash_is_not_certificate_identity() {
    let cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let encoded = encode_module_cert(&cert).unwrap();
    let certificate_hash = cert.hashes().certificate_hash;

    let _normal_policy_hash = AxiomPolicy::normal().policy_hash();
    let mut high_trust_with_axiom = AxiomPolicy::high_trust();
    high_trust_with_axiom
        .allowlisted_axioms
        .insert(Name::from_dotted("P"));
    let _high_trust_policy_hash = high_trust_with_axiom.policy_hash();

    assert_eq!(certificate_hash, cert.hashes().certificate_hash);
    assert_eq!(encoded, encode_module_cert(&cert).unwrap());
}

#[test]
fn axiom_policy_denies_sorry_axiom() {
    let sorry_cert =
        build_module_cert(named_axiom_module("Test.Sorry", "sorry.synthetic"), &[]).unwrap();
    let err = verify_module_cert(
        &encode_module_cert(&sorry_cert).unwrap(),
        &mut VerifierSession::new(),
        &AxiomPolicy::normal(),
    )
    .unwrap_err();
    assert!(matches!(err, CertError::SorryDenied { .. }));
}

#[test]
fn axiom_policy_rejects_custom_axiom_injection() {
    let cert = build_module_cert(axiom_module(), &[]).unwrap();
    let err = verify_module_cert(
        &encode_module_cert(&cert).unwrap(),
        &mut VerifierSession::new(),
        &AxiomPolicy::high_trust(),
    )
    .unwrap_err();
    assert!(matches!(
        err,
        CertError::ForbiddenAxiom { ref axiom } if axiom == &Name::from_dotted("P")
    ));
}

#[test]
fn axiom_policy_high_trust_allowlist_mismatch() {
    let cert = build_module_cert(axiom_module(), &[]).unwrap();
    let mut policy = AxiomPolicy::high_trust();
    policy.allowlisted_axioms.insert(Name::from_dotted("Q"));

    let err = verify_module_cert(
        &encode_module_cert(&cert).unwrap(),
        &mut VerifierSession::new(),
        &policy,
    )
    .unwrap_err();
    assert!(matches!(
        err,
        CertError::ForbiddenAxiom { ref axiom } if axiom == &Name::from_dotted("P")
    ));
}

#[test]
fn normal_mode_enforces_non_empty_axiom_allowlist() {
    let cert = build_module_cert(axiom_module(), &[]).unwrap();
    let bytes = encode_module_cert(&cert).unwrap();

    let mut policy = AxiomPolicy::normal();
    policy.allowlisted_axioms.insert(Name::from_dotted("Q"));
    let err = verify_module_cert(&bytes, &mut VerifierSession::new(), &policy).unwrap_err();
    assert!(matches!(
        err,
        CertError::ForbiddenAxiom { ref axiom } if axiom == &Name::from_dotted("P")
    ));

    let mut policy = AxiomPolicy::normal();
    policy.allowlisted_axioms.insert(Name::from_dotted("P"));
    verify_module_cert(&bytes, &mut VerifierSession::new(), &policy).unwrap();
}

#[test]
fn axiom_type_dependencies_are_reported_and_verified() {
    let cert = build_module_cert(theorem_using_axiom_module("p1"), &[]).unwrap();
    assert!(cert.declarations()[1]
        .dependencies
        .iter()
        .any(|dependency| matches!(dependency.global_ref(), GlobalRef::Local { decl_index: 0 })));
    assert!(cert.axiom_report().per_declaration[1]
        .transitive_axioms
        .iter()
        .any(|axiom| matches!(axiom.global_ref, GlobalRef::Local { decl_index: 0 })));
    let theorem_direct_axioms = cert.axiom_report().per_declaration[3]
        .direct_axioms
        .iter()
        .map(|axiom| cert.name_table()[axiom.name].as_dotted())
        .collect::<Vec<_>>();
    assert!(theorem_direct_axioms.iter().any(|name| name == "P"));
    assert!(theorem_direct_axioms.iter().any(|name| name == "p1"));

    let mut session = VerifierSession::new();
    verify_module_cert(
        &encode_module_cert(&cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap();
}

#[test]
fn inductive_certificate_round_trips_and_verifies() {
    let cert = build_module_cert(unary_inductive_module(), &[]).unwrap();
    let bytes = encode_module_cert(&cert).unwrap();
    let mut session = VerifierSession::new();
    let verified = verify_module_cert(&bytes, &mut session, &AxiomPolicy::normal()).unwrap();

    assert_eq!(verified.module(), &Name::from_dotted("Test.Unary"));
    assert!(matches!(
        verified.declarations().first().map(|decl| &decl.decl),
        Some(DeclPayload::Inductive { name, .. })
            if verified.name_table()[*name] == Name::from_dotted("Unary")
    ));
    assert!(cert.export_block().iter().any(|entry| {
        entry.kind == ExportKind::Constructor
            && cert.name_table()[entry.name] == Name::from_dotted("Unary.zero")
    }));
    assert!(cert.export_block().iter().any(|entry| {
        entry.kind == ExportKind::Constructor
            && cert.name_table()[entry.name] == Name::from_dotted("Unary.succ")
    }));
}

#[test]
fn indexed_inductive_certificate_round_trips_and_verifies() {
    let cert = build_module_cert(indexed_inductive_module(), &[]).unwrap();
    let bytes = encode_module_cert(&cert).unwrap();
    let mut session = VerifierSession::new();
    let verified = verify_module_cert(&bytes, &mut session, &AxiomPolicy::normal()).unwrap();

    assert_eq!(verified.module(), &Name::from_dotted("Test.Indexed"));
    for name in [
        "Vec", "Vec.nil", "Vec.cons", "Vec.rec", "Fin", "Fin.zero", "Fin.succ", "Fin.rec",
    ] {
        assert!(
            cert.export_block()
                .iter()
                .any(|entry| cert.name_table()[entry.name] == Name::from_dotted(name)),
            "{name} must be exported from indexed inductive fixture"
        );
    }
}

#[test]
fn mutual_inductive_even_odd_certificate_round_trips_and_verifies() {
    let cert = build_module_cert(even_odd_mutual_module(), &[]).unwrap();
    let bytes = encode_module_cert(&cert).unwrap();
    let mut session = VerifierSession::new();
    let verified = verify_module_cert(&bytes, &mut session, &AxiomPolicy::normal()).unwrap();

    assert_eq!(verified.module(), &Name::from_dotted("Test.EvenOdd"));
    assert!(matches!(
        verified.declarations().first().map(|decl| &decl.decl),
        Some(DeclPayload::MutualInductiveBlock { name, inductives, .. })
            if verified.name_table()[*name] == Name::from_dotted("EvenOdd")
                && inductives.len() == 2
    ));
    for name in [
        "Even",
        "Even.zero",
        "Even.succ",
        "Even.rec",
        "Odd",
        "Odd.succ",
        "Odd.rec",
    ] {
        assert!(
            cert.export_block()
                .iter()
                .any(|entry| cert.name_table()[entry.name] == Name::from_dotted(name)),
            "{name} must be exported from mutual inductive fixture"
        );
    }
}

#[test]
fn mutual_inductive_rejects_duplicate_generated_name() {
    let mut block = even_odd_mutual_block();
    block.inductives[1].recursor.as_mut().unwrap().name = "Even.rec".to_owned();
    let err = build_module_cert(
        CoreModule {
            name: Name::from_dotted("Test.BadEvenOdd"),
            declarations: vec![Decl::MutualInductiveBlock {
                name: block.name.clone(),
                universe_params: block.universe_params.clone(),
                data: Box::new(block),
            }],
        },
        &[],
    )
    .unwrap_err();

    assert!(
        matches!(
            err,
            CertError::DuplicateName { .. }
                | CertError::Kernel(npa_kernel::Error::DuplicateDecl(_))
                | CertError::InductiveGeneratedArtifactMismatch { .. }
        ),
        "{err:?}"
    );
}

#[test]
fn mutual_inductive_rejects_non_positive_occurrence() {
    let err =
        generate_mutual_inductive_artifacts_v1(&non_positive_even_odd_mutual_base()).unwrap_err();

    assert!(
        matches!(
            err,
            CertError::InductiveGeneratedArtifactMismatch { ref name }
                if name == &Name::from_dotted("BadEvenOdd")
        ),
        "{err:?}"
    );
}

#[test]
fn mutual_inductive_rejects_block_local_scope_mismatch_even_if_rehashed() {
    let mut cert = build_module_cert(even_odd_mutual_module(), &[]).unwrap();
    let even_name = cert
        .name_table()
        .iter()
        .position(|name| name == &Name::from_dotted("Even"))
        .unwrap();
    let odd_name = cert
        .name_table()
        .iter()
        .position(|name| name == &Name::from_dotted("Odd"))
        .unwrap();
    let mut changed = false;
    cert.mutate_parts_for_test(|parts| {
        for term in &mut parts.term_table {
            if let TermNode::Const {
                global_ref:
                    GlobalRef::LocalGenerated {
                        decl_index: 0,
                        name,
                    },
                levels,
            } = term
            {
                if *name == even_name && levels.is_empty() {
                    *name = odd_name;
                    changed = true;
                    break;
                }
            }
        }
    });
    assert!(changed, "Even local generated reference must exist");
    rehash_cert_after_decl_change(&mut cert);

    let mut session = VerifierSession::new();
    let err = verify_module_cert(
        &encode_module_cert(&cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap_err();
    assert!(
        matches!(
            err,
            CertError::InductiveGeneratedArtifactMismatch { .. }
                | CertError::Kernel(_)
                | CertError::NonCanonicalEncoding {
                    object: "TermTable"
                }
        ),
        "{err:?}"
    );
}

#[test]
fn inductive_nested_rose_certificate_round_trips_and_verifies() {
    let cert = build_module_cert(nested_rose_module(), &[]).unwrap();
    let encoded = encode_module_cert(&cert).unwrap();
    let decoded = decode_module_cert(&encoded).unwrap();

    assert_eq!(
        cert.hashes().certificate_hash,
        decoded.hashes().certificate_hash,
        "nested Rose certificate hash must be stable after canonical decode"
    );

    let mut session = VerifierSession::new();
    verify_module_cert(&encoded, &mut session, &AxiomPolicy::normal())
        .expect("approved nested Rose certificate must verify");

    let rose_decl = decoded
        .declarations()
        .iter()
        .find(|decl| matches!(decl.decl, DeclPayload::Inductive { name, .. } if decoded.name_table()[name] == Name::from_dotted("Rose")))
        .expect("Rose declaration must be present");
    let DeclPayload::Inductive {
        recursor: Some(recursor),
        ..
    } = &rose_decl.decl
    else {
        panic!("Rose must have a generated recursor");
    };
    assert_eq!(
        decoded.name_table()[recursor.name],
        Name::from_dotted("Rose.rec")
    );
    assert!(generated_recursor_signature_hash(
        Some(recursor),
        &(0..decoded.term_table().len())
            .map(|term| term_hash(&decoded, term))
            .collect::<Result<Vec<_>>>()
            .unwrap(),
        decoded.name_table(),
    )
    .is_ok());
    assert_ne!(generated_computation_rule_hash(Some(recursor)), [0; 32]);
}

#[test]
fn inductive_nested_positivity_rejects_unknown_and_negative_functors() {
    let err = generate_inductive_artifacts_v1(&rose_unknown_functor_base()).unwrap_err();
    assert!(matches!(
        err,
        CertError::InductiveGeneratedArtifactMismatch { .. }
    ));

    let err =
        generate_inductive_artifacts_v1(&rose_negative_arrow_base(Expr::bvar(2))).unwrap_err();
    assert!(matches!(
        err,
        CertError::InductiveGeneratedArtifactMismatch { .. }
    ));

    let u = Level::param("u");
    let err =
        generate_inductive_artifacts_v1(&rose_negative_arrow_base(rose_type(u, Expr::bvar(2))))
            .unwrap_err();
    assert!(matches!(
        err,
        CertError::InductiveGeneratedArtifactMismatch { .. }
    ));

    let err = generate_inductive_artifacts_v1(&rose_higher_order_negative_base()).unwrap_err();
    assert!(matches!(
        err,
        CertError::InductiveGeneratedArtifactMismatch { .. }
    ));
}

#[test]
fn mutual_inductive_generated_recursor_artifact_hashes_are_stable_and_scoped() {
    let cert = build_module_cert(even_odd_mutual_module(), &[]).unwrap();
    let decoded = decode_module_cert(&encode_module_cert(&cert).unwrap()).unwrap();
    assert_eq!(
        recursor_artifact_hashes_for(&cert, "Even"),
        recursor_artifact_hashes_for(&decoded, "Even")
    );
    assert_eq!(
        recursor_artifact_hashes_for(&cert, "Odd"),
        recursor_artifact_hashes_for(&decoded, "Odd")
    );

    let export_names = cert
        .export_block()
        .iter()
        .map(|entry| cert.name_table()[entry.name].clone())
        .collect::<Vec<_>>();
    let mut sorted_export_names = export_names.clone();
    sorted_export_names.sort();
    assert_eq!(export_names, sorted_export_names);

    let block_index = cert
        .declarations()
        .iter()
        .position(|decl| matches!(decl.decl, DeclPayload::MutualInductiveBlock { .. }))
        .unwrap();
    let (signature_hash, rule_hash) = recursor_artifact_hashes_for(&cert, "Even");

    let mut rules_changed = cert.clone();
    rules_changed.mutate_parts_for_test(|parts| match &mut parts.declarations[block_index].decl {
        DeclPayload::MutualInductiveBlock { inductives, .. } => {
            inductives[0].recursor.as_mut().unwrap().rules.major_index += 1;
        }
        _ => panic!("expected mutual inductive block"),
    });
    let (rules_changed_signature_hash, rules_changed_rule_hash) =
        recursor_artifact_hashes_for(&rules_changed, "Even");
    assert_eq!(signature_hash, rules_changed_signature_hash);
    assert_ne!(rule_hash, rules_changed_rule_hash);
}

#[test]
fn local_generated_constructor_can_be_referenced_after_inductive() {
    let cert = build_module_cert(unary_with_local_constructor_use_module(), &[]).unwrap();
    let def = &cert.declarations()[1];
    assert!(def
        .dependencies
        .iter()
        .any(|dependency| matches!(dependency.global_ref(), GlobalRef::LocalGenerated { .. })));

    let bytes = encode_module_cert(&cert).unwrap();
    let mut session = VerifierSession::new();
    verify_module_cert(&bytes, &mut session, &AxiomPolicy::normal()).unwrap();
}

#[test]
fn imported_constructor_can_be_referenced_from_downstream_certificate() {
    let unary_cert = build_module_cert(unary_inductive_module(), &[]).unwrap();
    let mut session = VerifierSession::new();
    let verified_unary = verify_module_cert(
        &encode_module_cert(&unary_cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap();

    let use_unary_cert =
        build_module_cert(use_imported_unary_constructor_module(), &[verified_unary]).unwrap();
    let def = &use_unary_cert.declarations()[0];
    assert!(def.dependencies.iter().any(|dependency| {
        matches!(
            dependency.global_ref(),
            GlobalRef::Imported { name, .. }
                if use_unary_cert.name_table()[*name] == Name::from_dotted("Unary.zero")
        )
    }));

    verify_module_cert(
        &encode_module_cert(&use_unary_cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap();
}

#[test]
fn imported_recursor_can_be_referenced_from_downstream_certificate() {
    let unary_cert = build_module_cert(unary_inductive_with_recursor_module(), &[]).unwrap();
    assert!(unary_cert.export_block().iter().any(|entry| {
        entry.kind == ExportKind::Recursor
            && unary_cert.name_table()[entry.name] == Name::from_dotted("Unary.rec")
    }));

    let mut session = VerifierSession::new();
    let verified_unary = verify_module_cert(
        &encode_module_cert(&unary_cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap();
    let use_rec_cert =
        build_module_cert(use_imported_unary_recursor_module(), &[verified_unary]).unwrap();
    assert!(use_rec_cert.declarations()[0]
        .dependencies
        .iter()
        .any(|dependency| {
            matches!(
                dependency.global_ref(),
                GlobalRef::Imported { name, .. }
                    if use_rec_cert.name_table()[*name] == Name::from_dotted("Unary.rec")
            )
        }));

    verify_module_cert(
        &encode_module_cert(&use_rec_cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap();
}

#[test]
fn generated_recursor_artifact_hashes_are_stable_and_scoped() {
    let cert = build_module_cert(unary_inductive_with_recursor_module(), &[]).unwrap();
    let decoded = decode_module_cert(&encode_module_cert(&cert).unwrap()).unwrap();
    let (signature_hash, rule_hash) = recursor_artifact_hashes(&cert);
    assert_eq!(
        (signature_hash, rule_hash),
        recursor_artifact_hashes(&decoded)
    );

    let inductive_index = cert
        .declarations()
        .iter()
        .position(|decl| matches!(decl.decl, DeclPayload::Inductive { .. }))
        .unwrap();
    let unary_term = cert
        .term_table()
        .iter()
        .position(|term| {
            matches!(
                term,
                TermNode::Const {
                    global_ref: GlobalRef::Local { decl_index },
                    levels
                } if *decl_index == inductive_index && levels.is_empty()
            )
        })
        .unwrap();

    let mut type_changed = cert.clone();
    type_changed.mutate_parts_for_test(|parts| {
        match &mut parts.declarations[inductive_index].decl {
            DeclPayload::Inductive {
                recursor: Some(recursor),
                ..
            } => recursor.ty = unary_term,
            _ => panic!("expected inductive with recursor"),
        }
    });
    let (type_changed_signature_hash, type_changed_rule_hash) =
        recursor_artifact_hashes(&type_changed);
    assert_ne!(signature_hash, type_changed_signature_hash);
    assert_eq!(rule_hash, type_changed_rule_hash);

    let mut rules_changed = cert.clone();
    rules_changed.mutate_parts_for_test(|parts| {
        match &mut parts.declarations[inductive_index].decl {
            DeclPayload::Inductive {
                recursor: Some(recursor),
                ..
            } => recursor.rules.major_index += 1,
            _ => panic!("expected inductive with recursor"),
        }
    });
    let (rules_changed_signature_hash, rules_changed_rule_hash) =
        recursor_artifact_hashes(&rules_changed);
    assert_eq!(signature_hash, rules_changed_signature_hash);
    assert_ne!(rule_hash, rules_changed_rule_hash);
}

#[test]
fn indexed_inductive_generated_recursor_artifact_hashes_are_stable_and_scoped() {
    let cert = build_module_cert(indexed_inductive_module(), &[]).unwrap();
    let decoded = decode_module_cert(&encode_module_cert(&cert).unwrap()).unwrap();
    assert_eq!(
        recursor_artifact_hashes_for(&cert, "Vec"),
        recursor_artifact_hashes_for(&decoded, "Vec")
    );

    let vec_index = cert
        .declarations()
        .iter()
        .position(|decl| {
            matches!(
                &decl.decl,
                DeclPayload::Inductive { name, .. }
                    | DeclPayload::InductiveConstrained { name, .. }
                    if cert.name_table()[*name] == Name::from_dotted("Vec")
            )
        })
        .unwrap();
    let (signature_hash, rule_hash) = recursor_artifact_hashes_for(&cert, "Vec");

    let mut rules_changed = cert.clone();
    rules_changed.mutate_parts_for_test(|parts| match &mut parts.declarations[vec_index].decl {
        DeclPayload::Inductive {
            recursor: Some(recursor),
            ..
        }
        | DeclPayload::InductiveConstrained {
            recursor: Some(recursor),
            ..
        } => recursor.rules.major_index += 1,
        _ => panic!("expected indexed inductive with recursor"),
    });
    let (rules_changed_signature_hash, rules_changed_rule_hash) =
        recursor_artifact_hashes_for(&rules_changed, "Vec");
    assert_eq!(signature_hash, rules_changed_signature_hash);
    assert_ne!(rule_hash, rules_changed_rule_hash);
}

#[test]
fn inductive_decl_interface_hash_commits_generated_recursor_artifact_hashes() {
    let cert = build_module_cert(unary_inductive_with_recursor_type_anchor_module(), &[]).unwrap();
    let inductive_index = cert
        .declarations()
        .iter()
        .position(|decl| matches!(decl.decl, DeclPayload::Inductive { .. }))
        .unwrap();
    let original_interface_hash = cert.declarations()[inductive_index]
        .hashes
        .decl_interface_hash;
    let unary_term = cert
        .term_table()
        .iter()
        .position(|term| {
            matches!(
                term,
                TermNode::Const {
                    global_ref: GlobalRef::Local { decl_index },
                    levels
                } if *decl_index == inductive_index && levels.is_empty()
            )
        })
        .unwrap();

    let mut signature_changed = cert.clone();
    signature_changed.mutate_parts_for_test(|parts| {
        match &mut parts.declarations[inductive_index].decl {
            DeclPayload::Inductive {
                recursor: Some(recursor),
                ..
            } => recursor.ty = unary_term,
            _ => panic!("expected inductive with recursor"),
        }
    });
    rehash_cert_after_decl_change(&mut signature_changed);

    let mut rules_changed = cert.clone();
    rules_changed.mutate_parts_for_test(|parts| {
        match &mut parts.declarations[inductive_index].decl {
            DeclPayload::Inductive {
                recursor: Some(recursor),
                ..
            } => recursor.rules.major_index += 1,
            _ => panic!("expected inductive with recursor"),
        }
    });
    rehash_cert_after_decl_change(&mut rules_changed);

    let signature_changed_interface_hash = signature_changed.declarations()[inductive_index]
        .hashes
        .decl_interface_hash;
    let rules_changed_interface_hash = rules_changed.declarations()[inductive_index]
        .hashes
        .decl_interface_hash;
    assert_ne!(original_interface_hash, signature_changed_interface_hash);
    assert_ne!(original_interface_hash, rules_changed_interface_hash);
    assert_ne!(
        signature_changed_interface_hash,
        rules_changed_interface_hash
    );
}

#[test]
fn rejects_tampered_inductive_generated_recursor_rules_even_if_rehashed() {
    let mut cert = build_module_cert(unary_inductive_with_recursor_module(), &[]).unwrap();
    cert.mutate_parts_for_test(|parts| match &mut parts.declarations[0].decl {
        DeclPayload::Inductive {
            recursor: Some(recursor),
            ..
        } => recursor.rules.major_index += 1,
        _ => panic!("expected inductive with recursor"),
    });
    rehash_cert_after_decl_change(&mut cert);

    let mut session = VerifierSession::new();
    let err = verify_module_cert(
        &encode_module_cert(&cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap_err();
    assert!(
        matches!(
            err,
            CertError::InductiveGeneratedArtifactMismatch { ref name }
                if name == &Name::from_dotted("Unary")
        ),
        "{err:?}"
    );
}

#[test]
fn rejects_tampered_inductive_generated_recursor_type_even_if_rehashed() {
    let mut cert =
        build_module_cert(unary_inductive_with_recursor_type_anchor_module(), &[]).unwrap();
    let inductive_index = cert
        .declarations()
        .iter()
        .position(|decl| matches!(decl.decl, DeclPayload::Inductive { .. }))
        .unwrap();
    let unary_term = cert
        .term_table()
        .iter()
        .position(|term| {
            matches!(
                term,
                TermNode::Const {
                    global_ref: GlobalRef::Local { decl_index },
                    levels
                } if *decl_index == inductive_index && levels.is_empty()
            )
        })
        .unwrap();
    cert.mutate_parts_for_test(
        |parts| match &mut parts.declarations[inductive_index].decl {
            DeclPayload::Inductive {
                recursor: Some(recursor),
                ..
            } => recursor.ty = unary_term,
            _ => panic!("expected inductive with recursor"),
        },
    );
    rehash_cert_after_decl_change(&mut cert);

    let mut session = VerifierSession::new();
    let err = verify_module_cert(
        &encode_module_cert(&cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap_err();
    assert!(
        matches!(
            err,
            CertError::InductiveGeneratedArtifactMismatch { ref name }
                if name == &Name::from_dotted("Unary")
        ),
        "{err:?}"
    );
}

#[test]
fn rejects_kernel_defeq_but_non_generated_recursor_type() {
    let cert = build_module_cert(unary_inductive_with_beta_recursor_module(), &[]).unwrap();

    let mut session = VerifierSession::new();
    let err = verify_module_cert(
        &encode_module_cert(&cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap_err();
    assert!(
        matches!(
            err,
            CertError::InductiveGeneratedArtifactMismatch { ref name }
                if name == &Name::from_dotted("Unary")
        ),
        "{err:?}"
    );
}

#[test]
fn parameterized_inductive_exports_full_type_telescope() {
    let cert = build_module_cert(box_inductive_module(), &[]).unwrap();
    let box_entry = cert
        .export_block()
        .iter()
        .find(|entry| {
            entry.kind == ExportKind::Inductive
                && cert.name_table()[entry.name] == Name::from_dotted("Box")
        })
        .unwrap();
    assert!(matches!(
        cert.term_table()[box_entry.ty],
        TermNode::Pi { .. }
    ));

    let mut session = VerifierSession::new();
    verify_module_cert(
        &encode_module_cert(&cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap();
}

#[test]
fn rejects_tampered_certificate_hash() {
    let cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let mut bytes = encode_module_cert(&cert).unwrap();
    let last = bytes.len() - 1;
    bytes[last] ^= 0x01;

    let mut session = VerifierSession::new();
    let err = verify_module_cert(&bytes, &mut session, &AxiomPolicy::normal()).unwrap_err();
    assert!(matches!(
        err,
        CertError::HashMismatch {
            object: HashObject::ModuleCertificate,
            ..
        }
    ));
}

#[test]
fn rejects_tampered_decl_interface_hash() {
    let mut cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let actual = cert.declarations()[0].hashes.decl_interface_hash;
    cert.mutate_parts_for_test(|parts| parts.declarations[0].hashes.decl_interface_hash[0] ^= 1);
    let expected = cert.declarations()[0].hashes.decl_interface_hash;

    let mut session = VerifierSession::new();
    let err = verify_module_cert(
        &encode_module_cert(&cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap_err();
    assert!(matches!(
        err,
        CertError::HashMismatch {
            object: HashObject::DeclInterface,
            expected: found_expected,
            actual: found_actual,
        } if found_expected == expected && found_actual == actual
    ));
}

#[test]
fn rejects_inductive_wrapper_universe_mismatch() {
    let mut module = nat_module();
    match &mut module.declarations[0] {
        Decl::Inductive {
            universe_params, ..
        } => universe_params.push("u".to_owned()),
        _ => panic!("expected inductive"),
    }

    let err = build_module_cert(module, &[]).unwrap_err();
    assert!(matches!(
        err,
        CertError::InductiveWrapperMismatch {
            name
        } if name == Name::from_dotted("Nat")
    ));
}

#[test]
fn rejects_inductive_wrapper_type_mismatch() {
    let mut module = nat_module();
    match &mut module.declarations[0] {
        Decl::Inductive { ty, .. } => *ty = Expr::sort(Level::zero()),
        _ => panic!("expected inductive"),
    }

    let err = build_module_cert(module, &[]).unwrap_err();
    assert!(matches!(
        err,
        CertError::InductiveWrapperMismatch {
            name
        } if name == Name::from_dotted("Nat")
    ));
}

#[test]
fn rejects_inductive_wrapper_name_mismatch() {
    let mut module = nat_module();
    match &mut module.declarations[0] {
        Decl::Inductive { name, .. } => *name = "BadNat".to_owned(),
        _ => panic!("expected inductive"),
    }

    let err = build_module_cert(module, &[]).unwrap_err();
    assert!(matches!(
        err,
        CertError::InductiveWrapperMismatch {
            name
        } if name == Name::from_dotted("BadNat")
    ));
}

#[test]
fn rejects_tampered_decl_certificate_hash() {
    let mut cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    cert.mutate_parts_for_test(|parts| parts.declarations[0].hashes.decl_certificate_hash[0] ^= 1);

    let mut session = VerifierSession::new();
    let err = verify_module_cert(
        &encode_module_cert(&cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap_err();
    assert!(matches!(
        err,
        CertError::HashMismatch {
            object: HashObject::DeclCertificate,
            ..
        }
    ));
}

#[test]
fn rejects_tampered_theorem_proof_body_even_if_certificate_rehashed() {
    let mut cert = build_module_cert(two_id_theorems_module(), &[]).unwrap();
    cert.mutate_parts_for_test(|parts| match &mut parts.declarations[1].decl {
        DeclPayload::Theorem { proof, ty, .. } => *proof = *ty,
        _ => panic!("expected theorem"),
    });
    let certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&cert),
    );
    cert.mutate_parts_for_test(|parts| parts.hashes.certificate_hash = certificate_hash);

    let mut session = VerifierSession::new();
    let err = verify_module_cert(
        &encode_module_cert(&cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap_err();
    assert!(matches!(
        err,
        CertError::HashMismatch {
            object: HashObject::DeclCertificate,
            ..
        }
    ));
}

fn p8h13_mutation_artifact_hash(seed: &[u8], label: &str, bytes: &[u8]) -> Hash {
    let mut payload = Vec::new();
    payload.extend(seed);
    payload.push(0);
    payload.extend(label.as_bytes());
    payload.push(0);
    payload.extend(bytes);
    hash_with_domain(b"NPA-P8H13-CERT-MUTATION-0.1", &payload)
}

#[test]
fn mutation_p8h13_fixture_records_hashes_and_rejects_core_mutation_classes() {
    const SEED: &[u8] = b"p8h13-cert-mutation-seed-0001";
    let mut artifact_hashes = Vec::new();

    let mut proof_cert = build_module_cert(two_id_theorems_module(), &[]).unwrap();
    proof_cert.mutate_parts_for_test(|parts| match &mut parts.declarations[1].decl {
        DeclPayload::Theorem { proof, ty, .. } => *proof = *ty,
        _ => panic!("expected theorem"),
    });
    rehash_cert_after_decl_change(&mut proof_cert);
    let proof_bytes = encode_module_cert(&proof_cert).unwrap();
    artifact_hashes.push(p8h13_mutation_artifact_hash(
        SEED,
        "proof_term",
        &proof_bytes,
    ));
    let err = verify_module_cert(
        &proof_bytes,
        &mut VerifierSession::new(),
        &AxiomPolicy::normal(),
    )
    .unwrap_err();
    assert!(matches!(err, CertError::Kernel(_)));

    let mut axiom_report_cert = build_module_cert(axiom_module(), &[]).unwrap();
    axiom_report_cert.mutate_parts_for_test(|parts| parts.axiom_report.module_axioms.clear());
    let axiom_report_hash = hash_with_domain(
        b"NPA-AXIOM-REPORT-0.1",
        &encode_axiom_report(axiom_report_cert.axiom_report()),
    );
    axiom_report_cert
        .mutate_parts_for_test(|parts| parts.hashes.axiom_report_hash = axiom_report_hash);
    let certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&axiom_report_cert),
    );
    axiom_report_cert
        .mutate_parts_for_test(|parts| parts.hashes.certificate_hash = certificate_hash);
    let axiom_report_bytes = encode_module_cert(&axiom_report_cert).unwrap();
    artifact_hashes.push(p8h13_mutation_artifact_hash(
        SEED,
        "axiom_report",
        &axiom_report_bytes,
    ));
    let err = verify_module_cert(
        &axiom_report_bytes,
        &mut VerifierSession::new(),
        &AxiomPolicy::normal(),
    )
    .unwrap_err();
    assert!(matches!(err, CertError::AxiomReportMismatch { .. }));

    let id_cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let id_bytes = encode_module_cert(&id_cert).unwrap();
    let mut session = VerifierSession::new();
    let verified_id = verify_module_cert(&id_bytes, &mut session, &AxiomPolicy::normal()).unwrap();
    let mut import_hash_cert = build_module_cert(use_id_module(), &[verified_id]).unwrap();
    import_hash_cert.mutate_parts_for_test(|parts| parts.imports[0].export_hash[0] ^= 1);
    let certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&import_hash_cert),
    );
    import_hash_cert
        .mutate_parts_for_test(|parts| parts.hashes.certificate_hash = certificate_hash);
    let import_hash_bytes = encode_module_cert(&import_hash_cert).unwrap();
    artifact_hashes.push(p8h13_mutation_artifact_hash(
        SEED,
        "import_hash",
        &import_hash_bytes,
    ));
    let err =
        verify_module_cert(&import_hash_bytes, &mut session, &AxiomPolicy::normal()).unwrap_err();
    assert!(matches!(err, CertError::ImportHashMismatch { .. }));

    let mut noncanonical_table_cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let duplicate = noncanonical_table_cert.term_table()[0].clone();
    noncanonical_table_cert.mutate_parts_for_test(|parts| parts.term_table.push(duplicate));
    let certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&noncanonical_table_cert),
    );
    noncanonical_table_cert
        .mutate_parts_for_test(|parts| parts.hashes.certificate_hash = certificate_hash);
    let noncanonical_table_bytes = encode_module_cert(&noncanonical_table_cert).unwrap();
    artifact_hashes.push(p8h13_mutation_artifact_hash(
        SEED,
        "noncanonical_term_table",
        &noncanonical_table_bytes,
    ));
    let err = verify_module_cert(
        &noncanonical_table_bytes,
        &mut VerifierSession::new(),
        &AxiomPolicy::normal(),
    )
    .unwrap_err();
    assert!(matches!(
        err,
        CertError::NonCanonicalEncoding {
            object: "TermTable"
        }
    ));

    let unique_hashes = artifact_hashes
        .iter()
        .copied()
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(unique_hashes.len(), artifact_hashes.len());
    assert!(unique_hashes.iter().all(|hash| *hash != [0; 32]));
    let repeated_hashes = [
        ("proof_term", proof_bytes.as_slice()),
        ("axiom_report", axiom_report_bytes.as_slice()),
        ("import_hash", import_hash_bytes.as_slice()),
        (
            "noncanonical_term_table",
            noncanonical_table_bytes.as_slice(),
        ),
    ]
    .into_iter()
    .map(|(label, bytes)| p8h13_mutation_artifact_hash(SEED, label, bytes))
    .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(unique_hashes, repeated_hashes);
}

#[test]
fn rejects_non_minimal_uleb128_in_canonical_binary() {
    let cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let mut bytes = encode_module_cert(&cert).unwrap();
    bytes[0] |= 0x80;
    bytes.insert(1, 0x00);

    let err = decode_module_cert(&bytes).unwrap_err();
    assert!(matches!(
        err,
        CertError::NonCanonicalEncoding { object: "uvar" }
    ));
}

#[test]
fn rejects_invalid_utf8_in_canonical_binary_string() {
    let cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let mut bytes = encode_module_cert(&cert).unwrap();
    bytes[1] = 0xff;

    let err = decode_module_cert(&bytes).unwrap_err();
    assert!(matches!(
        err,
        CertError::NonCanonicalEncoding { object: "string" }
    ));
}

#[test]
fn rejects_name_component_count_larger_than_remaining_input() {
    let mut bytes = Vec::new();
    append_test_string(&mut bytes, FORMAT);
    append_test_string(&mut bytes, CORE_SPEC);
    encode_uvar_to(&mut bytes, u64::MAX);

    let err = decode_module_cert(&bytes).unwrap_err();
    assert!(matches!(
        err,
        CertError::StructuralLimitExceeded {
            kind: StructuralLimitKind::NestedVectorEntries,
            limit: MAX_NESTED_VECTOR_ENTRIES,
            observed: usize::MAX,
        }
    ));
}

#[test]
fn rejects_empty_name_in_canonical_binary() {
    let mut bytes = Vec::new();
    append_test_string(&mut bytes, FORMAT);
    append_test_string(&mut bytes, CORE_SPEC);
    encode_uvar_to(&mut bytes, 0);

    let err = decode_module_cert(&bytes).unwrap_err();
    assert!(matches!(
        err,
        CertError::NonCanonicalEncoding { object: "Name" }
    ));
}

#[test]
fn rejects_empty_name_component_in_canonical_binary() {
    let mut bytes = Vec::new();
    append_test_string(&mut bytes, FORMAT);
    append_test_string(&mut bytes, CORE_SPEC);
    encode_uvar_to(&mut bytes, 1);
    encode_uvar_to(&mut bytes, 0);

    let err = decode_module_cert(&bytes).unwrap_err();
    assert!(matches!(
        err,
        CertError::NonCanonicalEncoding { object: "Name" }
    ));
}

#[test]
fn rejects_dotted_name_component_in_canonical_binary() {
    let mut bytes = Vec::new();
    append_test_string(&mut bytes, FORMAT);
    append_test_string(&mut bytes, CORE_SPEC);
    encode_uvar_to(&mut bytes, 1);
    append_test_string(&mut bytes, "Test.Id");

    let err = decode_module_cert(&bytes).unwrap_err();
    assert!(matches!(
        err,
        CertError::NonCanonicalEncoding { object: "Name" }
    ));
}

#[test]
fn v0_4_rejects_retired_let_tag_before_reading_former_children() {
    let mut cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    cert.mutate_parts_for_test(|parts| parts.term_table.push(TermNode::BVar(0)));
    let bytes = encode_module_cert(&cert).unwrap();
    let offsets = term_tag_offsets(&bytes);
    let reachable_offset = offsets[0];
    let unreachable_offset = *offsets.last().unwrap();
    assert_ne!(reachable_offset, unreachable_offset);

    let mut reachable = bytes.clone();
    reachable[reachable_offset] = 0x06;
    let mut unreachable = bytes.clone();
    unreachable[unreachable_offset] = 0x06;
    let mut tag_only = bytes[..reachable_offset].to_vec();
    tag_only.push(0x06);
    let mut one_former_child = tag_only.clone();
    one_former_child.push(0x00);
    let mut two_former_children = one_former_child.clone();
    two_former_children.push(0x00);
    let mut oversized_tail = tag_only.clone();
    oversized_tail.extend([0xff; 9]);
    oversized_tail.push(0x01);

    let rows = v0_4_fixture_rows("retired_tag");
    assert_eq!(rows.len(), 6);
    for fields in rows {
        let case_id = fields[0];
        assert_eq!(fields[6], "unsupported_encoding:0x06", "{case_id}");
        let malformed = match case_id {
            "retired_06_reachable" => &reachable,
            "retired_06_unused" => &unreachable,
            "retired_06_tag_only" => &tag_only,
            "retired_06_one_child" => &one_former_child,
            "retired_06_two_children" => &two_former_children,
            "retired_06_oversized_tail" => &oversized_tail,
            _ => panic!("unmapped retired-tag fixture: {case_id}"),
        };
        let result = decode_module_cert(malformed);
        assert!(
            matches!(result, Err(CertError::UnsupportedEncoding { tag: 0x06 })),
            "{case_id}: {result:?}"
        );
    }
}

#[test]
fn rejects_export_block_that_was_rehashed_but_not_derived_from_declarations() {
    let mut cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    cert.mutate_parts_for_test(|parts| parts.export_block.clear());
    let export_hash = hash_with_domain(
        MODULE_EXPORT_DOMAIN,
        &encode_export_block(cert.export_block()),
    );
    cert.mutate_parts_for_test(|parts| parts.hashes.export_hash = export_hash);
    let certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&cert),
    );
    cert.mutate_parts_for_test(|parts| parts.hashes.certificate_hash = certificate_hash);

    let mut session = VerifierSession::new();
    let err = verify_module_cert(
        &encode_module_cert(&cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap_err();
    assert!(matches!(
        err,
        CertError::HashMismatch {
            object: HashObject::ExportBlock,
            ..
        }
    ));
}

#[test]
fn rejects_axiom_report_that_was_rehashed_but_is_incomplete() {
    let mut cert = build_module_cert(axiom_module(), &[]).unwrap();
    cert.mutate_parts_for_test(|parts| parts.axiom_report.module_axioms.clear());
    let axiom_report_hash = hash_with_domain(
        b"NPA-AXIOM-REPORT-0.1",
        &encode_axiom_report(cert.axiom_report()),
    );
    cert.mutate_parts_for_test(|parts| parts.hashes.axiom_report_hash = axiom_report_hash);
    let certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&cert),
    );
    cert.mutate_parts_for_test(|parts| parts.hashes.certificate_hash = certificate_hash);

    let bytes = encode_module_cert(&cert).unwrap();
    let mut session = VerifierSession::new();
    let err = verify_module_cert(&bytes, &mut session, &AxiomPolicy::normal()).unwrap_err();
    assert!(matches!(err, CertError::AxiomReportMismatch { .. }));
}

#[test]
fn rejects_noncanonical_term_table_even_if_bytes_round_trip() {
    let mut cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let duplicate = cert.term_table()[0].clone();
    cert.mutate_parts_for_test(|parts| parts.term_table.push(duplicate));
    let certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&cert),
    );
    cert.mutate_parts_for_test(|parts| parts.hashes.certificate_hash = certificate_hash);

    let bytes = encode_module_cert(&cert).unwrap();
    let mut session = VerifierSession::new();
    let err = verify_module_cert(&bytes, &mut session, &AxiomPolicy::normal()).unwrap_err();
    assert!(matches!(
        err,
        CertError::NonCanonicalEncoding {
            object: "TermTable"
        }
    ));
}

#[test]
fn rejects_term_table_ordered_by_hash_instead_of_structural_key() {
    let mut cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let sort = cert
        .term_table()
        .iter()
        .position(|term| matches!(term, TermNode::Sort(_)))
        .unwrap();
    let bvar = cert
        .term_table()
        .iter()
        .position(|term| matches!(term, TermNode::BVar(0)))
        .unwrap();
    assert!(sort < bvar);

    swap_term_table_entries(&mut cert, sort, bvar);
    rehash_cert_after_decl_change(&mut cert);

    let bytes = encode_module_cert(&cert).unwrap();
    let mut session = VerifierSession::new();
    let err = verify_module_cert(&bytes, &mut session, &AxiomPolicy::normal()).unwrap_err();
    assert!(matches!(
        err,
        CertError::NonCanonicalEncoding {
            object: "TermTable"
        }
    ));
}

#[test]
fn rejects_level_table_ordered_by_hash_instead_of_structural_key() {
    let mut cert = build_module_cert(eq_module(), &[]).unwrap();
    let u = cert
        .name_table()
        .iter()
        .position(|name| *name == Name::from_dotted("u"))
        .unwrap();
    let zero = cert
        .level_table()
        .iter()
        .position(|level| matches!(level, LevelNode::Zero))
        .unwrap();
    let param = cert
        .level_table()
        .iter()
        .position(|level| matches!(level, LevelNode::Param(name) if *name == u))
        .unwrap();
    assert!(zero < param);

    swap_level_table_entries(&mut cert, zero, param);
    rehash_cert_after_decl_change(&mut cert);

    let bytes = encode_module_cert(&cert).unwrap();
    let mut session = VerifierSession::new();
    let err = verify_module_cert(&bytes, &mut session, &AxiomPolicy::normal()).unwrap_err();
    assert!(matches!(
        err,
        CertError::NonCanonicalEncoding {
            object: "LevelTable"
        }
    ));
}

#[test]
fn rejects_unreachable_term_table_entry_even_if_rehashed() {
    let mut cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let last = cert.term_table().len() - 1;
    cert.mutate_parts_for_test(|parts| parts.term_table.push(TermNode::App(last, last)));
    let certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&cert),
    );
    cert.mutate_parts_for_test(|parts| parts.hashes.certificate_hash = certificate_hash);

    let bytes = encode_module_cert(&cert).unwrap();
    let mut session = VerifierSession::new();
    let err = verify_module_cert(&bytes, &mut session, &AxiomPolicy::normal()).unwrap_err();
    assert!(matches!(
        err,
        CertError::NonCanonicalEncoding {
            object: "TermTable"
        }
    ));
}

#[test]
fn rejects_non_normalized_level_table_entry_even_if_rehashed() {
    let mut cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let u = cert
        .name_table()
        .iter()
        .position(|name| *name == Name::from_dotted("u"))
        .unwrap();
    assert_eq!(cert.level_table(), [LevelNode::Param(u)]);

    cert.mutate_parts_for_test(|parts| {
        parts.level_table = vec![LevelNode::Zero, LevelNode::Param(u), LevelNode::Max(0, 1)];
        for term in &mut parts.term_table {
            replace_level_refs(term, 0, 2);
        }
    });
    rehash_cert_after_decl_change(&mut cert);

    let bytes = encode_module_cert(&cert).unwrap();
    let mut session = VerifierSession::new();
    let err = verify_module_cert(&bytes, &mut session, &AxiomPolicy::normal()).unwrap_err();
    assert!(matches!(
        err,
        CertError::NonCanonicalEncoding {
            object: "LevelTable"
        }
    ));
}

#[test]
fn rejects_unreachable_level_table_entry_even_if_rehashed() {
    let mut cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let last = cert.level_table().len() - 1;
    cert.mutate_parts_for_test(|parts| parts.level_table.push(LevelNode::Succ(last)));
    let certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&cert),
    );
    cert.mutate_parts_for_test(|parts| parts.hashes.certificate_hash = certificate_hash);

    let bytes = encode_module_cert(&cert).unwrap();
    let mut session = VerifierSession::new();
    let err = verify_module_cert(&bytes, &mut session, &AxiomPolicy::normal()).unwrap_err();
    assert!(matches!(
        err,
        CertError::NonCanonicalEncoding {
            object: "LevelTable"
        }
    ));
}

#[test]
fn rejects_root_term_with_out_of_scope_bvar() {
    let mut cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let bvar_zero = cert
        .term_table()
        .iter()
        .position(|term| matches!(term, TermNode::BVar(0)))
        .unwrap();
    cert.mutate_parts_for_test(|parts| match &mut parts.declarations[0].decl {
        DeclPayload::Def { value, .. } => *value = bvar_zero,
        _ => panic!("expected def"),
    });
    let certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&cert),
    );
    cert.mutate_parts_for_test(|parts| parts.hashes.certificate_hash = certificate_hash);

    let bytes = encode_module_cert(&cert).unwrap();
    let mut session = VerifierSession::new();
    let err = verify_module_cert(&bytes, &mut session, &AxiomPolicy::normal()).unwrap_err();
    assert!(matches!(err, CertError::InvalidBVar { index: 0 }));
}

#[test]
fn normal_mode_allows_missing_import_certificate_hash_but_high_trust_rejects_it() {
    let id_cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let id_bytes = encode_module_cert(&id_cert).unwrap();
    let mut session = VerifierSession::new();
    let verified_id = verify_module_cert(&id_bytes, &mut session, &AxiomPolicy::normal()).unwrap();

    let mut use_id_cert = build_module_cert(use_id_module(), &[verified_id]).unwrap();
    use_id_cert.mutate_parts_for_test(|parts| parts.imports[0].certificate_hash = None);
    let certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&use_id_cert),
    );
    use_id_cert.mutate_parts_for_test(|parts| parts.hashes.certificate_hash = certificate_hash);
    let use_id_bytes = encode_module_cert(&use_id_cert).unwrap();

    verify_module_cert(&use_id_bytes, &mut session, &AxiomPolicy::normal()).unwrap();

    let err =
        verify_module_cert(&use_id_bytes, &mut session, &AxiomPolicy::high_trust()).unwrap_err();
    assert!(matches!(
        err,
        CertError::MissingImportCertificateHash { .. }
    ));
}

#[test]
fn high_trust_rejects_import_verified_only_in_normal_mode() {
    let id_cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let id_bytes = encode_module_cert(&id_cert).unwrap();
    let mut session = VerifierSession::new();
    let verified_id =
        verify_module_cert(&id_bytes, &mut session, &AxiomPolicy::high_trust()).unwrap();

    let mut use_id_cert =
        build_module_cert(use_id_module(), std::slice::from_ref(&verified_id)).unwrap();
    use_id_cert.mutate_parts_for_test(|parts| parts.imports[0].certificate_hash = None);
    let certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&use_id_cert),
    );
    use_id_cert.mutate_parts_for_test(|parts| parts.hashes.certificate_hash = certificate_hash);
    let verified_use_id = verify_module_cert(
        &encode_module_cert(&use_id_cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap();

    let downstream_cert = build_module_cert(
        use_imported_use_id_module(),
        &[verified_use_id, verified_id],
    )
    .unwrap();
    let err = verify_module_cert(
        &encode_module_cert(&downstream_cert).unwrap(),
        &mut session,
        &AxiomPolicy::high_trust(),
    )
    .unwrap_err();
    assert!(matches!(
        err,
        CertError::ImportNotVerifiedInSession { module }
            if module == Name::from_dotted("Test.UseId")
    ));
}

#[test]
fn rejects_import_certificate_hash_mismatch() {
    let id_cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let id_bytes = encode_module_cert(&id_cert).unwrap();
    let mut session = VerifierSession::new();
    let verified_id =
        verify_module_cert(&id_bytes, &mut session, &AxiomPolicy::high_trust()).unwrap();

    let mut use_id_cert = build_module_cert(use_id_module(), &[verified_id]).unwrap();
    use_id_cert.mutate_parts_for_test(|parts| {
        parts.imports[0].certificate_hash.as_mut().unwrap()[0] ^= 1;
    });
    let certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&use_id_cert),
    );
    use_id_cert.mutate_parts_for_test(|parts| parts.hashes.certificate_hash = certificate_hash);

    let err = verify_module_cert(
        &encode_module_cert(&use_id_cert).unwrap(),
        &mut session,
        &AxiomPolicy::high_trust(),
    )
    .unwrap_err();
    assert!(matches!(
        err,
        CertError::ImportCertificateHashMismatch { .. }
    ));
}

#[test]
fn normal_mode_rejects_present_import_certificate_hash_mismatch() {
    let id_cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let id_bytes = encode_module_cert(&id_cert).unwrap();
    let mut session = VerifierSession::new();
    let verified_id = verify_module_cert(&id_bytes, &mut session, &AxiomPolicy::normal()).unwrap();

    let mut use_id_cert = build_module_cert(use_id_module(), &[verified_id]).unwrap();
    use_id_cert.mutate_parts_for_test(|parts| {
        parts.imports[0].certificate_hash.as_mut().unwrap()[0] ^= 1;
    });
    let certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&use_id_cert),
    );
    use_id_cert.mutate_parts_for_test(|parts| parts.hashes.certificate_hash = certificate_hash);

    let err = verify_module_cert(
        &encode_module_cert(&use_id_cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap_err();
    assert!(matches!(
        err,
        CertError::ImportCertificateHashMismatch { .. }
    ));
}

#[test]
fn rejects_import_export_hash_mismatch() {
    let id_cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let id_bytes = encode_module_cert(&id_cert).unwrap();
    let mut session = VerifierSession::new();
    let verified_id = verify_module_cert(&id_bytes, &mut session, &AxiomPolicy::normal()).unwrap();

    let mut use_id_cert = build_module_cert(use_id_module(), &[verified_id]).unwrap();
    use_id_cert.mutate_parts_for_test(|parts| parts.imports[0].export_hash[0] ^= 1);
    let certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&use_id_cert),
    );
    use_id_cert.mutate_parts_for_test(|parts| parts.hashes.certificate_hash = certificate_hash);

    let err = verify_module_cert(
        &encode_module_cert(&use_id_cert).unwrap(),
        &mut session,
        &AxiomPolicy::normal(),
    )
    .unwrap_err();
    assert!(matches!(err, CertError::ImportHashMismatch { .. }));
}

#[test]
fn high_trust_rechecks_import_axiom_policy_even_when_unused() {
    let p_cert = build_module_cert(axiom_module(), &[]).unwrap();
    let mut session = VerifierSession::new();
    let mut allow_p = AxiomPolicy::high_trust();
    allow_p.allowlisted_axioms.insert(Name::from_dotted("P"));
    let verified_p = verify_module_cert(
        &encode_module_cert(&p_cert).unwrap(),
        &mut session,
        &allow_p,
    )
    .unwrap();

    let id_cert = build_module_cert(id_module("A", "x"), &[verified_p]).unwrap();
    assert!(id_cert.axiom_report().module_axioms.is_empty());

    let err = verify_module_cert(
        &encode_module_cert(&id_cert).unwrap(),
        &mut session,
        &AxiomPolicy::high_trust(),
    )
    .unwrap_err();
    assert!(matches!(err, CertError::ForbiddenAxiom { .. }));

    verify_module_cert(
        &encode_module_cert(&id_cert).unwrap(),
        &mut session,
        &allow_p,
    )
    .unwrap();
}

#[test]
fn high_trust_rejects_import_not_verified_in_current_session() {
    let id_cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let mut build_session = VerifierSession::new();
    let verified_id = verify_module_cert(
        &encode_module_cert(&id_cert).unwrap(),
        &mut build_session,
        &AxiomPolicy::normal(),
    )
    .unwrap();
    let use_id_cert = build_module_cert(use_id_module(), &[verified_id]).unwrap();

    let mut fresh_session = VerifierSession::new();
    let err = verify_module_cert(
        &encode_module_cert(&use_id_cert).unwrap(),
        &mut fresh_session,
        &AxiomPolicy::high_trust(),
    )
    .unwrap_err();
    assert!(matches!(err, CertError::ImportNotVerifiedInSession { .. }));
}

#[test]
fn term_materialization_current_lane_is_measurement_independent() {
    for module in [
        id_module("A", "x"),
        id_def_module_with_value(id_value_with_beta_redex()),
    ] {
        let cert = build_module_cert(module, &[]).unwrap();
        let bytes = encode_module_cert(&cert).unwrap();
        let expected =
            verify_module_cert_with_import_refs(&bytes, &[], &AxiomPolicy::normal()).unwrap();

        for kernel_options in [
            KernelExecutionOptions::memo_off(),
            KernelExecutionOptions::ephemeral_memo(),
        ] {
            let legacy_sink = KernelWorkCounterSink::default();
            let legacy = crate::verify::verify_module_cert_with_import_refs_legacy_for_test(
                &bytes,
                &[],
                &AxiomPolicy::normal(),
                kernel_options,
                Some(legacy_sink.clone()),
            )
            .unwrap();
            let legacy_work = legacy_sink.snapshot();
            let mut forward_work = KernelWorkCounters::default();
            let mut term = CertificateTermMaterializationObservation::default();
            let observed = verify_module_cert_with_import_refs_and_kernel_options_and_observations(
                &bytes,
                &[],
                &AxiomPolicy::normal(),
                kernel_options,
                CertificateVerificationObservationSinks::new()
                    .with_kernel(&mut forward_work)
                    .with_term(&mut term),
            )
            .unwrap();

            assert_eq!(observed, expected);
            assert_eq!(observed, legacy);
            assert_eq!(observed.certificate_hash(), cert.hashes().certificate_hash);
            assert_eq!(forward_work.logical_fuel, legacy_work.logical_fuel);
            assert_eq!(forward_work.successful_fuel, legacy_work.successful_fuel);
            assert_eq!(forward_work.exhausted_fuel, legacy_work.exhausted_fuel);
            assert_eq!(forward_work.fuel, legacy_work.fuel);
            assert_eq!(
                term.unique_nodes_materialized,
                cert.term_table().len() as u64
            );
            assert!(term.root_requests > 0);
            assert_eq!(term.materialization_slots, cert.term_table().len() as u64);
            assert!(term.materialization_charged_bytes > 0);
            assert_eq!(term.materialization_capacity_stops, 0);
            assert_eq!(term.materialization_legacy_fallbacks, 0);
            assert!(!term.overflowed);
        }
    }
}

#[test]
fn term_materialization_import_plan_replays_differentially() {
    let provider_cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let provider_bytes = encode_module_cert(&provider_cert).unwrap();
    let provider =
        verify_module_cert_with_import_refs(&provider_bytes, &[], &AxiomPolicy::normal()).unwrap();
    let consumer_cert =
        build_module_cert(use_id_module(), std::slice::from_ref(&provider)).unwrap();
    let consumer_bytes = encode_module_cert(&consumer_cert).unwrap();
    let imports = [&provider];
    for policy in [AxiomPolicy::normal(), AxiomPolicy::high_trust()] {
        for kernel_options in [
            KernelExecutionOptions::memo_off(),
            KernelExecutionOptions::ephemeral_memo(),
        ] {
            let legacy_sink = KernelWorkCounterSink::default();
            let legacy = crate::verify::verify_module_cert_with_import_refs_legacy_for_test(
                &consumer_bytes,
                &imports,
                &policy,
                kernel_options,
                Some(legacy_sink.clone()),
            )
            .unwrap();
            let legacy_work = legacy_sink.snapshot();
            let mut forward_work = KernelWorkCounters::default();
            let mut term = CertificateTermMaterializationObservation::default();
            let observed = verify_module_cert_with_import_refs_and_kernel_options_and_observations(
                &consumer_bytes,
                &imports,
                &policy,
                kernel_options,
                CertificateVerificationObservationSinks::new()
                    .with_kernel(&mut forward_work)
                    .with_term(&mut term),
            )
            .unwrap();

            assert_eq!(observed, legacy);
            assert_eq!(observed.export_hash(), consumer_cert.hashes().export_hash);
            assert_eq!(forward_work.logical_fuel, legacy_work.logical_fuel);
            assert_eq!(forward_work.successful_fuel, legacy_work.successful_fuel);
            assert_eq!(forward_work.exhausted_fuel, legacy_work.exhausted_fuel);
            assert_eq!(forward_work.fuel, legacy_work.fuel);
            assert!(
                term.unique_nodes_materialized
                    >= u64::try_from(consumer_cert.term_table().len()).unwrap()
            );
            assert!(term.root_requests > 0);
            assert!(term.materialization_charged_bytes > 0);
            assert_eq!(term.materialization_capacity_stops, 0);
            assert_eq!(term.materialization_legacy_fallbacks, 0);
        }
    }
}

#[test]
fn term_materialization_post_materialization_error_is_differential() {
    let mut cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let bvar_zero = cert
        .term_table()
        .iter()
        .position(|term| matches!(term, TermNode::BVar(0)))
        .unwrap();
    let mut parts = cert.into_parts();
    match &mut parts.declarations[0].decl {
        DeclPayload::Def { value, .. } => *value = bvar_zero,
        _ => panic!("expected def"),
    }
    let unhashed = ModuleCert::from_parts(parts);
    let certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&unhashed),
    );
    let mut parts = unhashed.into_parts();
    parts.hashes.certificate_hash = certificate_hash;
    cert = ModuleCert::from_parts(parts);
    let bytes = encode_module_cert(&cert).unwrap();

    for kernel_options in [
        KernelExecutionOptions::memo_off(),
        KernelExecutionOptions::ephemeral_memo(),
    ] {
        let legacy_sink = KernelWorkCounterSink::default();
        let legacy = crate::verify::verify_module_cert_with_import_refs_legacy_for_test(
            &bytes,
            &[],
            &AxiomPolicy::normal(),
            kernel_options,
            Some(legacy_sink.clone()),
        )
        .unwrap_err();
        let mut forward_work = KernelWorkCounters::default();
        let mut term = CertificateTermMaterializationObservation::default();
        let forward = verify_module_cert_with_import_refs_and_kernel_options_and_observations(
            &bytes,
            &[],
            &AxiomPolicy::normal(),
            kernel_options,
            CertificateVerificationObservationSinks::new()
                .with_kernel(&mut forward_work)
                .with_term(&mut term),
        )
        .unwrap_err();

        assert_eq!(forward, legacy);
        let legacy_work = legacy_sink.snapshot();
        assert_eq!(forward_work.logical_fuel, legacy_work.logical_fuel);
        assert_eq!(forward_work.fuel, legacy_work.fuel);
        // The malformed declaration is rejected by the existing structural
        // preflight before either conversion lane starts.
        assert_eq!(term, CertificateTermMaterializationObservation::default());
    }
}

#[test]
fn term_materialization_does_not_observe_pre_materialization_decode_failure() {
    let cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let mut bytes = encode_module_cert(&cert).unwrap();
    bytes.push(0);
    let mut term = CertificateTermMaterializationObservation::default();

    let result = verify_module_cert_with_import_refs_and_kernel_options_and_observations(
        &bytes,
        &[],
        &AxiomPolicy::normal(),
        npa_kernel::KernelExecutionOptions::default(),
        CertificateVerificationObservationSinks::new().with_term(&mut term),
    );

    assert!(result.is_err());
    assert_eq!(term, CertificateTermMaterializationObservation::default());
}

fn term_materialization_verified_pair() -> (VerifiedModule, VerifiedModule) {
    let provider_cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let provider = verify_module_cert_with_import_refs(
        &encode_module_cert(&provider_cert).unwrap(),
        &[],
        &AxiomPolicy::normal(),
    )
    .unwrap();
    let consumer_cert =
        build_module_cert(use_id_module(), std::slice::from_ref(&provider)).unwrap();
    let consumer = verify_module_cert_with_import_refs(
        &encode_module_cert(&consumer_cert).unwrap(),
        &[&provider],
        &AxiomPolicy::normal(),
    )
    .unwrap();
    (provider, consumer)
}

#[derive(Clone)]
struct TestCertificateImportView {
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
}

impl TestCertificateImportView {
    fn from_verified(module: &VerifiedModule) -> Self {
        Self {
            module: module.module().clone(),
            imports: module.imports().to_vec(),
            name_table: module.name_table().to_vec(),
            level_table: module.level_table().to_vec(),
            term_table: module.term_table().to_vec(),
            declarations: module.declarations().to_vec(),
            export_hash: module.export_hash(),
            certificate_hash: module.certificate_hash(),
            export_block: module.export_block().to_vec(),
            axiom_report: module.axiom_report().clone(),
            structural_closure: module.structural_closure().clone(),
        }
    }

    fn from_cert(module: &ModuleCert) -> Self {
        Self {
            module: module.header().module.clone(),
            imports: module.imports().to_vec(),
            name_table: module.name_table().to_vec(),
            level_table: module.level_table().to_vec(),
            term_table: module.term_table().to_vec(),
            declarations: module.declarations().to_vec(),
            export_hash: module.hashes().export_hash,
            certificate_hash: module.hashes().certificate_hash,
            export_block: module.export_block().to_vec(),
            axiom_report: module.axiom_report().clone(),
            structural_closure: StructuralClosureSummary::default(),
        }
    }
}

impl crate::local_authoring::CertificateImportView for TestCertificateImportView {
    fn module(&self) -> &Name {
        &self.module
    }

    fn imports(&self) -> &[ImportEntry] {
        &self.imports
    }

    fn name_table(&self) -> &[Name] {
        &self.name_table
    }

    fn level_table(&self) -> &[LevelNode] {
        &self.level_table
    }

    fn term_table(&self) -> &[TermNode] {
        &self.term_table
    }

    fn declarations(&self) -> &[DeclCert] {
        &self.declarations
    }

    fn export_hash(&self) -> Hash {
        self.export_hash
    }

    fn certificate_hash(&self) -> Hash {
        self.certificate_hash
    }

    fn export_block(&self) -> &[ExportEntry] {
        &self.export_block
    }

    fn axiom_report(&self) -> &AxiomReport {
        &self.axiom_report
    }

    fn structural_closure(&self) -> &StructuralClosureSummary {
        &self.structural_closure
    }
}

#[test]
fn verified_module_projection_uses_one_table() {
    let (provider, consumer) = term_materialization_verified_pair();
    let mut env = Env::with_builtins().unwrap();
    let mut observation = CertificateTermMaterializationObservation::default();
    add_verified_module_referenced_imports_to_env_observed_for_test(
        &mut env,
        &consumer,
        &[&provider],
        &mut observation,
    )
    .unwrap();
    assert!(env.decl("id").is_some());
    assert_eq!(
        observation.materialization_slots,
        provider.term_table().len() as u64
    );
    assert!(observation.unique_nodes_materialized > 0);
    assert_eq!(observation.materialization_legacy_fallbacks, 0);
    assert_eq!(observation.materialization_capacity_stops, 0);

    let projected = verified_module_to_kernel_decls(&consumer).unwrap();
    assert_eq!(projected.len(), consumer.declarations().len());
}

#[test]
fn imported_materialization_exact_identity_diamond() {
    let (provider, _) = term_materialization_verified_pair();
    let entry = &provider.export_block()[0];
    let name = provider.name_table()[entry.name].clone();
    let imports: [&dyn crate::local_authoring::CertificateImportView; 2] = [&provider, &provider];
    let exports = [
        (0, name.clone(), entry.decl_interface_hash),
        (1, name, entry.decl_interface_hash),
    ];
    let mut env = Env::with_builtins().unwrap();
    let mut observation = CertificateTermMaterializationObservation::default();
    add_selected_import_exports_to_env_observed_for_test(
        &mut env,
        &imports,
        &exports,
        &mut observation,
    )
    .unwrap();
    assert!(env.decl("id").is_some());
    assert_eq!(
        observation.materialization_slots,
        provider.term_table().len() as u64
    );
    assert_eq!(observation.materialization_legacy_fallbacks, 0);

    let mut alternate_identity = TestCertificateImportView::from_verified(&provider);
    alternate_identity.certificate_hash[0] ^= 1;
    let imports: [&dyn crate::local_authoring::CertificateImportView; 2] =
        [&provider, &alternate_identity];
    let exports = [
        (0, Name::from_dotted("id"), entry.decl_interface_hash),
        (1, Name::from_dotted("id"), entry.decl_interface_hash),
    ];
    let mut env = Env::with_builtins().unwrap();
    let mut observation = CertificateTermMaterializationObservation::default();
    let error = add_selected_import_exports_to_env_observed_for_test(
        &mut env,
        &imports,
        &exports,
        &mut observation,
    )
    .unwrap_err();
    assert!(matches!(
        error,
        CertError::Kernel(npa_kernel::Error::DuplicateDecl(ref name)) if name == "id"
    ));
    assert!(env.decl("id").is_some());
    assert_eq!(
        observation.materialization_slots,
        2 * provider.term_table().len() as u64
    );
    assert_eq!(observation.materialization_legacy_fallbacks, 0);
}

#[test]
fn imported_materialization_sparse_export() {
    let provider_module = CoreModule {
        name: Name::from_dotted("Test.SparseProvider"),
        declarations: vec![
            Decl::Def {
                name: "first".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: id_type("A", "x"),
                value: id_value("A", "x"),
                reducibility: Reducibility::Reducible,
            },
            Decl::Def {
                name: "second".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: id_type("B", "y"),
                value: id_value_with_beta_redex(),
                reducibility: Reducibility::Reducible,
            },
        ],
    };
    let cert = build_module_cert(provider_module, &[]).unwrap();
    let provider = verify_module_cert_with_import_refs(
        &encode_module_cert(&cert).unwrap(),
        &[],
        &AxiomPolicy::normal(),
    )
    .unwrap();
    let entry = provider
        .export_block()
        .iter()
        .find(|entry| provider.name_table()[entry.name] == Name::from_dotted("first"))
        .unwrap();
    let imports: [&dyn crate::local_authoring::CertificateImportView; 1] = [&provider];
    let exports = [(0, Name::from_dotted("first"), entry.decl_interface_hash)];
    let mut env = Env::with_builtins().unwrap();
    let mut observation = CertificateTermMaterializationObservation::default();
    add_selected_import_exports_to_env_observed_for_test(
        &mut env,
        &imports,
        &exports,
        &mut observation,
    )
    .unwrap();
    assert!(env.decl("first").is_some());
    assert!(env.decl("second").is_none());
    assert!(observation.unique_nodes_materialized < provider.term_table().len() as u64);
    assert_eq!(
        observation.materialization_slots,
        provider.term_table().len() as u64
    );
}

#[test]
fn term_materialization_aggregate_operation_budget() {
    let provider_cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let provider = verify_module_cert_with_import_refs(
        &encode_module_cert(&provider_cert).unwrap(),
        &[],
        &AxiomPolicy::normal(),
    )
    .unwrap();
    let consumer_cert =
        build_module_cert(use_id_module(), std::slice::from_ref(&provider)).unwrap();
    let consumer = verify_module_cert_with_import_refs(
        &encode_module_cert(&consumer_cert).unwrap(),
        &[&provider],
        &AxiomPolicy::normal(),
    )
    .unwrap();

    let mut probe_budget = TermMaterializationBudgetV1::new();
    let mut probe_observation = CertificateTermMaterializationObservation::default();
    assert!(select_current_term_conversion_with_budget_for_test(
        &consumer_cert,
        &mut probe_budget,
        Some(&mut probe_observation),
    ));
    let current_charge = probe_budget.admitted_bytes();
    assert!(current_charge > 0);

    let prefix = TERM_MATERIALIZATION_CHARGED_BYTE_LIMIT - current_charge - 1;
    for observed in [false, true] {
        let mut budget = TermMaterializationBudgetV1::with_admitted_bytes_for_test(prefix);
        let mut observation = CertificateTermMaterializationObservation::default();
        assert!(select_current_term_conversion_with_budget_for_test(
            &consumer_cert,
            &mut budget,
            observed.then_some(&mut observation),
        ));
        assert_eq!(
            budget.admitted_bytes(),
            TERM_MATERIALIZATION_CHARGED_BYTE_LIMIT - 1
        );

        let mut env = Env::with_builtins().unwrap();
        add_verified_module_referenced_imports_to_env_with_budget_and_optional_observation_for_test(
            &mut env,
            &consumer,
            &[&provider],
            &mut budget,
            observed.then_some(&mut observation),
        )
        .unwrap();
        assert!(env.decl("id").is_some());
        assert_eq!(
            budget.admitted_bytes(),
            TERM_MATERIALIZATION_CHARGED_BYTE_LIMIT - 1
        );
        if observed {
            assert_eq!(observation.materialization_capacity_stops, 1);
            assert_eq!(observation.materialization_legacy_fallbacks, 1);
            assert_eq!(observation.materialization_charged_bytes, current_charge);
        } else {
            assert_eq!(
                observation,
                CertificateTermMaterializationObservation::default()
            );
        }
    }
}

#[test]
fn imported_materialization_production_matrix() {
    verified_module_projection_uses_one_table();
    imported_materialization_exact_identity_diamond();
    imported_materialization_sparse_export();

    let (provider, _) = term_materialization_verified_pair();
    let entry = &provider.export_block()[0];
    let imports: [&dyn crate::local_authoring::CertificateImportView; 1] = [&provider];
    let exports = [(
        0,
        provider.name_table()[entry.name].clone(),
        entry.decl_interface_hash,
    )];
    let mut env = Env::with_builtins().unwrap();
    let mut exhausted = TermMaterializationBudgetV1::exhausted_for_test();
    let mut observation = CertificateTermMaterializationObservation::default();
    add_selected_import_exports_to_env_with_budget_for_test(
        &mut env,
        &imports,
        &exports,
        &mut exhausted,
        &mut observation,
    )
    .unwrap();
    assert!(env.decl("id").is_some());
    assert_eq!(observation.materialization_capacity_stops, 1);
    assert_eq!(observation.materialization_legacy_fallbacks, 1);
    assert_eq!(observation.materialization_charged_bytes, 0);
    assert_eq!(
        exhausted.admitted_bytes(),
        TERM_MATERIALIZATION_CHARGED_BYTE_LIMIT
    );
}

#[test]
fn selected_export_borrowed_scratch_preflight_boundary() {
    let (provider, _) = term_materialization_verified_pair();
    let entry = &provider.export_block()[0];
    let name = provider.name_table()[entry.name].clone();
    let imports: [&dyn crate::local_authoring::CertificateImportView; 1] = [&provider];
    let exports = [
        (0, name.clone(), entry.decl_interface_hash),
        (0, name, entry.decl_interface_hash),
    ];
    let mut env = Env::with_builtins().unwrap();
    let mut exhausted = TermMaterializationBudgetV1::exhausted_for_test();
    let mut observation = CertificateTermMaterializationObservation::default();

    add_selected_import_exports_to_env_with_budget_for_test(
        &mut env,
        &imports,
        &exports,
        &mut exhausted,
        &mut observation,
    )
    .unwrap();

    // The raw duplicate request count is conservatively fitted before the
    // borrowed selection scratch is reserved. At the exact operation limit,
    // the planned lane therefore stops without a commit or Env effect and the
    // unchanged legacy lane still deduplicates to the accepted declaration.
    assert!(env.decl("id").is_some());
    assert_eq!(observation.materialization_capacity_stops, 1);
    assert_eq!(observation.materialization_legacy_fallbacks, 1);
    assert_eq!(observation.materialization_charged_bytes, 0);
    assert_eq!(
        exhausted.admitted_bytes(),
        TERM_MATERIALIZATION_CHARGED_BYTE_LIMIT
    );
}

#[test]
fn current_term_materialization_verifier_differential() {
    term_materialization_current_lane_is_measurement_independent();
    term_materialization_post_materialization_error_is_differential();
}

#[test]
fn current_term_materialization_production_matrix() {
    current_term_materialization_verifier_differential();
    term_materialization_does_not_observe_pre_materialization_decode_failure();
}

#[test]
fn imported_materialization_action_order_differential() {
    let provider_cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let provider = verify_module_cert_with_import_refs(
        &encode_module_cert(&provider_cert).unwrap(),
        &[],
        &AxiomPolicy::normal(),
    )
    .unwrap();
    let consumer_cert =
        build_module_cert(use_id_module(), std::slice::from_ref(&provider)).unwrap();
    let consumer_view = TestCertificateImportView::from_cert(&consumer_cert);

    let mut bad_builtin_provider = TestCertificateImportView::from_verified(&provider);
    let nat_name = bad_builtin_provider.name_table.len();
    bad_builtin_provider
        .name_table
        .push(Name::from_dotted("Nat"));
    bad_builtin_provider.term_table[0] = TermNode::Const {
        global_ref: GlobalRef::Builtin {
            name: nat_name,
            decl_interface_hash: test_hash(0xff),
        },
        levels: Vec::new(),
    };
    let bad_imports: [&dyn crate::local_authoring::CertificateImportView; 1] =
        [&bad_builtin_provider];
    let mut planned_env = Env::with_builtins().unwrap();
    planned_env
        .add_axiom("id", Vec::new(), Expr::sort(Level::zero()))
        .unwrap();
    let mut planned_observation = CertificateTermMaterializationObservation::default();
    let mut planned_budget = TermMaterializationBudgetV1::new();
    let planned_error = imported_materialization_action_order_with_budget_for_test(
        &mut planned_env,
        &consumer_view,
        &bad_imports,
        &mut planned_budget,
        Some(&mut planned_observation),
    )
    .unwrap_err();
    let mut legacy_env = Env::with_builtins().unwrap();
    legacy_env
        .add_axiom("id", Vec::new(), Expr::sort(Level::zero()))
        .unwrap();
    let legacy_error = add_root_referenced_imports_to_env_legacy_for_test(
        &mut legacy_env,
        &consumer_view,
        &bad_imports,
    )
    .unwrap_err();
    assert_eq!(planned_error, legacy_error);
    assert!(matches!(
        planned_error,
        CertError::UnknownDependency { name } if name == Name::from_dotted("Nat")
    ));
    assert_eq!(planned_observation.materialization_legacy_fallbacks, 0);
    assert_eq!(planned_observation.materialization_capacity_stops, 0);

    let ordinary_imports: [&dyn crate::local_authoring::CertificateImportView; 1] = [&provider];
    let mut planned_env = Env::with_builtins().unwrap();
    planned_env
        .add_axiom("id", Vec::new(), Expr::sort(Level::zero()))
        .unwrap();
    let mut planned_observation = CertificateTermMaterializationObservation::default();
    let mut planned_budget = TermMaterializationBudgetV1::new();
    let planned_error = imported_materialization_action_order_with_budget_for_test(
        &mut planned_env,
        &consumer_view,
        &ordinary_imports,
        &mut planned_budget,
        Some(&mut planned_observation),
    )
    .unwrap_err();
    let mut legacy_env = Env::with_builtins().unwrap();
    legacy_env
        .add_axiom("id", Vec::new(), Expr::sort(Level::zero()))
        .unwrap();
    let legacy_error = add_root_referenced_imports_to_env_legacy_for_test(
        &mut legacy_env,
        &consumer_view,
        &ordinary_imports,
    )
    .unwrap_err();
    assert_eq!(planned_error, legacy_error);
    assert_eq!(planned_observation.materialization_legacy_fallbacks, 0);
    assert_eq!(planned_observation.materialization_capacity_stops, 0);

    let mut cyclic_provider = TestCertificateImportView::from_verified(&provider);
    let entry = cyclic_provider.export_block[0].clone();
    cyclic_provider.imports.push(ImportEntry {
        module: cyclic_provider.module.clone(),
        export_hash: cyclic_provider.export_hash,
        certificate_hash: Some(cyclic_provider.certificate_hash),
    });
    cyclic_provider.term_table[0] = TermNode::Const {
        global_ref: GlobalRef::Imported {
            import_index: 0,
            name: entry.name,
            decl_interface_hash: entry.decl_interface_hash,
        },
        levels: Vec::new(),
    };
    let cyclic_imports: [&dyn crate::local_authoring::CertificateImportView; 1] =
        [&cyclic_provider];
    let mut env = Env::with_builtins().unwrap();
    let mut budget = TermMaterializationBudgetV1::new();
    let mut observation = CertificateTermMaterializationObservation::default();
    let error = imported_materialization_action_order_with_budget_for_test(
        &mut env,
        &consumer_view,
        &cyclic_imports,
        &mut budget,
        Some(&mut observation),
    )
    .unwrap_err();
    assert!(matches!(error, CertError::DependencyCycle { .. }));
    assert_eq!(observation.materialization_legacy_fallbacks, 1);
    assert_eq!(observation.materialization_capacity_stops, 0);

    let mut env = Env::with_builtins().unwrap();
    let mut exhausted = TermMaterializationBudgetV1::exhausted_for_test();
    let mut observation = CertificateTermMaterializationObservation::default();
    imported_materialization_action_order_with_budget_for_test(
        &mut env,
        &consumer_view,
        &ordinary_imports,
        &mut exhausted,
        Some(&mut observation),
    )
    .unwrap();
    assert!(env.decl("id").is_some());
    assert_eq!(observation.materialization_capacity_stops, 1);
    assert_eq!(observation.materialization_legacy_fallbacks, 1);
}

#[test]
fn term_materialization_fuel_differential() {
    let cert =
        build_module_cert(id_def_module_with_value(id_value_with_beta_redex()), &[]).unwrap();
    let root = match &cert.declarations()[0].decl {
        DeclPayload::Def { value, .. } => *value,
        _ => unreachable!(),
    };
    let legacy_left = expr_from_term(&cert, root).unwrap();
    let legacy_right = expr_from_term(&cert, root).unwrap();
    let mut budget = TermMaterializationBudgetV1::new();
    let MaterializationAttempt::Ready(table) =
        KernelExprMaterialization::for_current_module(&cert, &[root], &mut budget, None)
    else {
        panic!("current fixture must materialize");
    };
    let materialized = table.root_expr(root, None).unwrap();

    fn run(
        options: KernelExecutionOptions,
        lhs: &Expr,
        rhs: &Expr,
        fuel: usize,
    ) -> (npa_kernel::Result<bool>, usize, KernelWorkCounters) {
        let sink = KernelWorkCounterSink::default();
        let env = Env::with_execution_options_and_work_counter_sink(options, sink.clone());
        let mut remaining = fuel;
        let result = env.is_defeq_with_fuel_metered(&Ctx::new(), &[], lhs, rhs, &mut remaining);
        (result, remaining, sink.snapshot())
    }

    for options in [
        KernelExecutionOptions::memo_off(),
        KernelExecutionOptions::ephemeral_memo(),
    ] {
        let exact = (0..=4_096)
            .find(|fuel| run(options, &legacy_left, &legacy_right, *fuel).0 == Ok(true))
            .expect("small fixture must have a bounded success threshold");
        assert!(exact > 0);
        for fuel in [exact - 1, exact, exact + 1] {
            let legacy = run(options, &legacy_left, &legacy_right, fuel);
            let forward = run(options, &materialized, &legacy_right, fuel);
            assert_eq!(forward.0, legacy.0, "fuel={fuel}, options={options:?}");
            assert_eq!(forward.1, legacy.1, "fuel={fuel}, options={options:?}");
            assert_eq!(forward.2.logical_fuel, legacy.2.logical_fuel);
            assert_eq!(forward.2.successful_fuel, legacy.2.successful_fuel);
            assert_eq!(forward.2.exhausted_fuel, legacy.2.exhausted_fuel);
            if fuel < exact {
                assert!(matches!(
                    forward.0,
                    Err(npa_kernel::Error::ResourceLimit {
                        kind: ResourceLimitKind::Conversion
                    })
                ));
            } else {
                assert_eq!(forward.0, Ok(true));
            }
        }
    }
}

#[test]
fn term_materialization_diagnostic_differential() {
    let cert =
        build_module_cert(id_def_module_with_value(id_value_with_beta_redex()), &[]).unwrap();
    let root = match &cert.declarations()[0].decl {
        DeclPayload::Def { value, .. } => *value,
        _ => unreachable!(),
    };
    let legacy_left = expr_from_term(&cert, root).unwrap();
    let legacy_right = expr_from_term(&cert, root).unwrap();
    let mut current_budget = TermMaterializationBudgetV1::new();
    let MaterializationAttempt::Ready(current_table) =
        KernelExprMaterialization::for_current_module(&cert, &[root], &mut current_budget, None)
    else {
        panic!("current fixture must materialize");
    };
    let current = current_table.root_expr(root, None).unwrap();
    let mut selected_budget = TermMaterializationBudgetV1::new();
    let MaterializationAttempt::Ready(selected_table) =
        KernelExprMaterialization::for_selected_roots(&cert, &[root], &mut selected_budget, None)
    else {
        panic!("selected import fixture must materialize");
    };
    let selected = selected_table.root_expr(root, None).unwrap();

    fn report_json(error: &npa_kernel::DiagnosedKernelError) -> String {
        let context = error.context().expect("fuel error must carry context");
        let conversion = context
            .conversion()
            .expect("fuel error must carry conversion context");
        let (resource, path, path_truncated, overflowed) = if let Some(fuel) = context.kernel_fuel()
        {
            (
                format!("\"{}\"", fuel.resource.as_str()),
                fuel.comparison_path
                    .steps
                    .iter()
                    .map(|step| format!("\"{}\"", step.as_str()))
                    .collect::<Vec<_>>()
                    .join(","),
                fuel.comparison_path.truncated,
                fuel.overflowed,
            )
        } else {
            ("null".to_owned(), String::new(), false, false)
        };
        format!(
            "{{\"error\":\"conversion_resource_limit\",\"phase\":\"{}\",\"outcome\":\"{}\",\"lhs_head\":\"{}\",\"rhs_head\":\"{}\",\"depth\":{},\"resource\":{},\"path\":[{}],\"path_truncated\":{},\"overflowed\":{}}}",
            context.phase().as_str(),
            conversion.outcome().as_str(),
            conversion.lhs_head().as_str(),
            conversion.rhs_head().as_str(),
            conversion.depth(),
            resource,
            path,
            path_truncated,
            overflowed,
        )
    }

    let env = Env::new();
    let legacy = env
        .is_defeq_diagnosed_with_fuel(&Ctx::new(), &[], &legacy_left, &legacy_right, 0)
        .unwrap_err();
    assert!(matches!(
        legacy.error(),
        npa_kernel::Error::ResourceLimit {
            kind: ResourceLimitKind::Conversion
        }
    ));
    let legacy_json = report_json(&legacy);
    assert!(legacy_json.contains("\"phase\":\"definitional_equality\""));
    assert!(legacy_json.contains("\"resource\":null"));
    for candidate in [&current, &selected] {
        let diagnosed = env
            .is_defeq_diagnosed_with_fuel(&Ctx::new(), &[], candidate, &legacy_right, 0)
            .unwrap_err();
        assert_eq!(diagnosed, legacy);
        assert_eq!(report_json(&diagnosed), legacy_json);
    }
}

#[test]
fn term_materialization_identity_differential() {
    term_materialization_current_lane_is_measurement_independent();
    term_materialization_import_plan_replays_differentially();
}

#[test]
fn term_materialization_observation_failure_matrix() {
    term_materialization_does_not_observe_pre_materialization_decode_failure();
    term_materialization_post_materialization_error_is_differential();

    let provider_cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let provider = verify_module_cert_with_import_refs(
        &encode_module_cert(&provider_cert).unwrap(),
        &[],
        &AxiomPolicy::normal(),
    )
    .unwrap();
    let consumer_cert =
        build_module_cert(use_id_module(), std::slice::from_ref(&provider)).unwrap();
    let consumer_view = TestCertificateImportView::from_cert(&consumer_cert);
    let ordinary_imports: [&dyn crate::local_authoring::CertificateImportView; 1] = [&provider];

    let mut exhausted = TermMaterializationBudgetV1::exhausted_for_test();
    let mut stop_observation = CertificateTermMaterializationObservation::default();
    let mut env = Env::with_builtins().unwrap();
    imported_materialization_action_order_with_budget_for_test(
        &mut env,
        &consumer_view,
        &ordinary_imports,
        &mut exhausted,
        Some(&mut stop_observation),
    )
    .unwrap();
    assert_eq!(stop_observation.materialization_capacity_stops, 1);
    assert_eq!(stop_observation.materialization_legacy_fallbacks, 1);
    assert_eq!(stop_observation.materialization_charged_bytes, 0);

    let mut env = Env::with_builtins().unwrap();
    env.add_axiom("id", Vec::new(), Expr::sort(Level::zero()))
        .unwrap();
    let mut failure_budget = TermMaterializationBudgetV1::new();
    let mut failure_observation = CertificateTermMaterializationObservation::default();
    assert!(imported_materialization_action_order_with_budget_for_test(
        &mut env,
        &consumer_view,
        &ordinary_imports,
        &mut failure_budget,
        Some(&mut failure_observation),
    )
    .is_err());
    assert!(failure_observation.unique_nodes_materialized > 0);
    assert!(failure_observation.materialization_charged_bytes > 0);
    assert_eq!(failure_observation.materialization_capacity_stops, 0);
    assert_eq!(failure_observation.materialization_legacy_fallbacks, 0);

    let mut off_budget = TermMaterializationBudgetV1::new();
    let mut env = Env::with_builtins().unwrap();
    imported_materialization_action_order_with_budget_for_test(
        &mut env,
        &consumer_view,
        &ordinary_imports,
        &mut off_budget,
        None,
    )
    .unwrap();
    assert!(env.decl("id").is_some());
}

#[test]
fn certificate_observation_sink_bundle_matrix() {
    let cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let bytes = encode_module_cert(&cert).unwrap();
    let empty = verify_module_cert_with_import_refs_and_kernel_options_and_observations(
        &bytes,
        &[],
        &AxiomPolicy::normal(),
        KernelExecutionOptions::default(),
        CertificateVerificationObservationSinks::new(),
    )
    .unwrap();

    let mut term_only = CertificateTermMaterializationObservation::default();
    let term_observed = verify_module_cert_with_import_refs_and_kernel_options_and_observations(
        &bytes,
        &[],
        &AxiomPolicy::normal(),
        KernelExecutionOptions::default(),
        CertificateVerificationObservationSinks::new().with_term(&mut term_only),
    )
    .unwrap();

    let mut kernel_with_term = KernelWorkCounters::default();
    let mut term_with_kernel = CertificateTermMaterializationObservation::default();
    let kernel_term_observed =
        verify_module_cert_with_import_refs_and_kernel_options_and_observations(
            &bytes,
            &[],
            &AxiomPolicy::normal(),
            KernelExecutionOptions::default(),
            CertificateVerificationObservationSinks::new()
                .with_kernel(&mut kernel_with_term)
                .with_term(&mut term_with_kernel),
        )
        .unwrap();

    let mut kernel_full = KernelWorkCounters::default();
    let mut term_full = CertificateTermMaterializationObservation::default();
    let mut payload_full = CertificatePayloadObservation::default();
    let full_observed = verify_module_cert_with_import_refs_and_kernel_options_and_observations(
        &bytes,
        &[],
        &AxiomPolicy::normal(),
        KernelExecutionOptions::default(),
        CertificateVerificationObservationSinks::new()
            .with_kernel(&mut kernel_full)
            .with_term(&mut term_full)
            .with_payload(&mut payload_full),
    )
    .unwrap();

    assert_eq!(term_observed, empty);
    assert_eq!(kernel_term_observed, empty);
    assert_eq!(full_observed, empty);
    assert_eq!(term_only, term_with_kernel);
    assert_eq!(term_only, term_full);
    assert_eq!(kernel_with_term, kernel_full);
    assert!(kernel_full.infer_calls > 0);
    assert!(term_full.unique_nodes_materialized > 0);
    assert_eq!(term_full.root_requests, term_full.owned_root_handoffs);
    assert!(!term_full.overflowed);
    assert!(payload_full.payloads_frozen > 0);
    assert!(payload_full.payload_unique_bytes > 0);
    assert!(!payload_full.overflowed);
}

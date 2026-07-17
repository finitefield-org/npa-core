use std::{fs, path::PathBuf, process::Command};

use npa_cert::{
    build_module_cert, encode_module_cert, term_hash, verify_module_cert, AxiomPolicy, CoreModule,
    DeclPayload, ModuleCert, Name, TermNode, VerifierSession,
};
use npa_checker_ref::{
    check_certificate, ReferenceCheckReason, ReferenceCheckResult, ReferenceCheckerPolicy,
    ReferenceImportStore, ReferenceTrustMode,
};
use npa_kernel::{Decl, Expr, Level};
use sha2::{Digest, Sha256};

fn id_type() -> Expr {
    Expr::pi(
        "A",
        Expr::sort(Level::param("u")),
        Expr::pi("x", Expr::bvar(0), Expr::bvar(1)),
    )
}

fn id_proof() -> Expr {
    Expr::lam(
        "A",
        Expr::sort(Level::param("u")),
        Expr::lam("x", Expr::bvar(0), Expr::bvar(0)),
    )
}

fn provider(proof: Expr) -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Audit.Provider"),
        declarations: vec![Decl::Theorem {
            name: "Audit.Provider.id".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: id_type(),
            proof,
        }],
    }
}

fn consumer() -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Audit.Consumer"),
        declarations: vec![Decl::Theorem {
            name: "Audit.Consumer.id".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: id_type(),
            proof: Expr::konst("Audit.Provider.id", vec![Level::param("u")]),
        }],
    }
}

fn hash_with_domain(domain: &[u8], payload: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(domain);
    hasher.update(payload);
    hasher.finalize().into()
}

fn recompute_module_certificate_hash(cert: &mut ModuleCert) {
    let encoded = encode_module_cert(cert).unwrap();
    let payload = &encoded[..encoded.len() - 32];
    cert.hashes.certificate_hash = hash_with_domain(b"NPA-MODULE-CERT-0.2.0", payload);
}

fn semantically_invalid_provider(mut cert: ModuleCert) -> ModuleCert {
    let bvar_zero = cert
        .term_table
        .iter()
        .position(|term| matches!(term, TermNode::BVar(0)))
        .expect("identity certificate contains bvar 0");
    let bvar_one = cert
        .term_table
        .iter()
        .position(|term| matches!(term, TermNode::BVar(1)))
        .expect("identity certificate contains bvar 1");
    let inner_lambda = cert
        .term_table
        .iter()
        .position(|term| {
            matches!(
                term,
                TermNode::Lam { ty, body } if *ty == bvar_zero && *body == bvar_zero
            )
        })
        .expect("identity certificate contains its inner lambda");
    match &mut cert.term_table[inner_lambda] {
        TermNode::Lam { body, .. } => *body = bvar_one,
        term => panic!("expected inner identity lambda, got {term:?}"),
    }
    let proof = match cert.declarations[0].decl {
        DeclPayload::Theorem { proof, .. } => proof,
        ref decl => panic!("expected identity theorem, got {decl:?}"),
    };
    let mut payload = Vec::new();
    payload.extend(cert.declarations[0].hashes.decl_interface_hash);
    payload.extend(term_hash(&cert, proof).unwrap());
    payload.push(0); // Empty dependency vector.
    cert.declarations[0].hashes.decl_certificate_hash =
        hash_with_domain(b"NPA-DECL-CERT-0.1", &payload);
    recompute_module_certificate_hash(&mut cert);
    cert
}

fn unchecked_import_fixture(pin_bad_certificate: bool) -> (ModuleCert, ModuleCert, Vec<u8>) {
    let good_cert = build_module_cert(provider(id_proof()), &[]).unwrap();
    let good_bytes = encode_module_cert(&good_cert).unwrap();
    let mut session = VerifierSession::new();
    let good = verify_module_cert(&good_bytes, &mut session, &AxiomPolicy::normal()).unwrap();

    let bad_cert = semantically_invalid_provider(good_cert.clone());
    let mut leaf_cert = build_module_cert(consumer(), &[good]).unwrap();
    leaf_cert.imports[0].certificate_hash =
        pin_bad_certificate.then_some(bad_cert.hashes.certificate_hash);
    recompute_module_certificate_hash(&mut leaf_cert);
    let leaf_bytes = encode_module_cert(&leaf_cert).unwrap();
    (good_cert, bad_cert, leaf_bytes)
}

fn temp_dir(name: &str) -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "npa-checker-ref-unchecked-import-{name}-{}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&path);
    fs::create_dir_all(&path).unwrap();
    path
}

fn run_cli(dir: &std::path::Path, policy: Option<&std::path::Path>) -> std::process::Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_npa-checker-ref"));
    command.args([
        "--cert",
        dir.join("leaf.npcert").to_str().unwrap(),
        "--import-dir",
        dir.join("imports").to_str().unwrap(),
    ]);
    if let Some(policy) = policy {
        command.args(["--policy", policy.to_str().unwrap()]);
    }
    command.args(["--output", "json"]);
    command.output().unwrap()
}

fn write_cli_fixture(dir: &std::path::Path, bad_cert: &ModuleCert, leaf_bytes: &[u8]) {
    let import_dir = dir.join("imports");
    fs::create_dir_all(&import_dir).unwrap();
    fs::write(
        import_dir.join("provider.npcert"),
        encode_module_cert(bad_cert).unwrap(),
    )
    .unwrap();
    fs::write(dir.join("leaf.npcert"), leaf_bytes).unwrap();
}

#[test]
fn normal_mode_leaf_accepts_semantically_unchecked_import() {
    let (good_cert, bad_cert, leaf_bytes) = unchecked_import_fixture(false);
    let bad_bytes = encode_module_cert(&bad_cert).unwrap();
    assert_eq!(good_cert.hashes.export_hash, bad_cert.hashes.export_hash);
    assert_ne!(
        good_cert.hashes.certificate_hash,
        bad_cert.hashes.certificate_hash
    );
    assert!(matches!(
        check_certificate(
            &bad_bytes,
            &ReferenceImportStore::default(),
            &ReferenceCheckerPolicy::default(),
        ),
        ReferenceCheckResult::Rejected(_)
    ));

    let unchecked =
        ReferenceImportStore::from_source_free_certificates([bad_bytes.as_slice()]).unwrap();

    assert!(matches!(
        check_certificate(&leaf_bytes, &unchecked, &ReferenceCheckerPolicy::default()),
        ReferenceCheckResult::Checked(_)
    ));
}

#[test]
fn cli_normal_mode_accepts_leaf_with_semantically_unchecked_import() {
    let (_, bad_cert, leaf_bytes) = unchecked_import_fixture(false);
    let dir = temp_dir("normal");
    write_cli_fixture(&dir, &bad_cert, &leaf_bytes);

    let output = run_cli(&dir, None);
    let stdout = String::from_utf8(output.stdout).unwrap();

    assert_eq!(output.status.code(), Some(0), "{stdout}");
    assert!(stdout.contains("\"status\":\"checked\""), "{stdout}");
    assert!(stdout.contains("\"module\":\"Audit.Consumer\""), "{stdout}");
    let _ = fs::remove_dir_all(dir);
}

#[test]
fn cli_high_trust_rejects_leaf_with_semantically_unchecked_import() {
    let (_, bad_cert, leaf_bytes) = unchecked_import_fixture(true);
    let bad_bytes = encode_module_cert(&bad_cert).unwrap();
    let unchecked =
        ReferenceImportStore::from_source_free_certificates([bad_bytes.as_slice()]).unwrap();
    let policy = ReferenceCheckerPolicy {
        trust_mode: ReferenceTrustMode::HighTrust,
        ..ReferenceCheckerPolicy::default()
    };
    let ReferenceCheckResult::Rejected(error) = check_certificate(&leaf_bytes, &unchecked, &policy)
    else {
        panic!("high-trust mode must reject an unchecked import");
    };
    assert_eq!(error.reason, Some(ReferenceCheckReason::UncheckedImport));

    let dir = temp_dir("high-trust");
    write_cli_fixture(&dir, &bad_cert, &leaf_bytes);
    let policy_path = dir.join("policy.json");
    fs::write(&policy_path, r#"{"trust_mode":"high_trust"}"#).unwrap();

    let output = run_cli(&dir, Some(&policy_path));
    let stdout = String::from_utf8(output.stdout).unwrap();

    assert_eq!(output.status.code(), Some(1), "{stdout}");
    assert!(stdout.contains("\"status\":\"failed\""), "{stdout}");
    assert!(stdout.contains("\"kind\":\"import_not_found\""), "{stdout}");
    assert!(stdout.contains("\"section\":\"imports\""), "{stdout}");
    let _ = fs::remove_dir_all(dir);
}

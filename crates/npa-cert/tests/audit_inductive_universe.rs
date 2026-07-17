use npa_cert::{
    build_module_cert, decode_module_cert, generate_inductive_artifacts_v1,
    precheck_core_decl_candidate, verify_module_cert, AxiomPolicy, CertError, CoreDeclCandidate,
    CoreModule, Name, ProducerLimits, VerifierSession,
};
use npa_kernel::{
    ConstructorDecl, Decl, Env, Error, Expr, InductiveDecl, Level, MutualInductiveBlock,
    Reducibility,
};

const SMALL_UNIVERSE_CERTIFICATE: &[u8] = include_bytes!(
    "../../../testdata/certificates/security/inductive-constructor-universe-bound-v0.1.npcert"
);
const MUTUAL_SMALL_UNIVERSE_CERTIFICATE: &[u8] = include_bytes!(
    "../../../testdata/certificates/security/mutual-inductive-constructor-universe-bound-v0.2.npcert"
);

fn universe_code_inductive() -> InductiveDecl {
    let type0 = Level::succ(Level::zero());
    let base = InductiveDecl::new(
        "Audit.Code",
        vec![],
        vec![],
        vec![],
        type0.clone(),
        vec![ConstructorDecl::new(
            "Audit.Code.mk",
            Expr::pi("A", Expr::sort(type0), Expr::konst("Audit.Code", vec![])),
        )],
        None,
    );
    generate_inductive_artifacts_v1(&base).unwrap()
}

fn small_universe_module() -> CoreModule {
    let type0 = Level::succ(Level::zero());
    let type1 = Level::succ(type0.clone());
    let code = Expr::konst("Audit.Code", vec![]);
    let motive = Expr::lam("_", code.clone(), Expr::sort(type0.clone()));
    let minor = Expr::lam("A", Expr::sort(type0.clone()), Expr::bvar(0));
    let el_ty = Expr::pi("code", code.clone(), Expr::sort(type0.clone()));
    let el_value = Expr::lam(
        "code",
        code.clone(),
        Expr::apps(
            Expr::konst("Audit.Code.rec", vec![type1]),
            vec![motive, minor, Expr::bvar(0)],
        ),
    );
    let decoded_type = Expr::app(
        Expr::konst("Audit.Universe.El", vec![]),
        Expr::app(Expr::konst("Audit.Code.mk", vec![]), Expr::bvar(1)),
    );
    CoreModule {
        name: Name::from_dotted("Audit.Universe"),
        declarations: vec![
            Decl::Inductive {
                name: "Audit.Code".to_owned(),
                universe_params: vec![],
                ty: Expr::sort(type0.clone()),
                data: Box::new(universe_code_inductive()),
            },
            Decl::Def {
                name: "Audit.Universe.El".to_owned(),
                universe_params: vec![],
                ty: el_ty,
                value: el_value,
                reducibility: Reducibility::Reducible,
            },
            Decl::Theorem {
                name: "Audit.Universe.decode_mk".to_owned(),
                universe_params: vec![],
                ty: Expr::pi(
                    "A",
                    Expr::sort(type0.clone()),
                    Expr::pi("x", Expr::bvar(0), decoded_type),
                ),
                proof: Expr::lam(
                    "A",
                    Expr::sort(type0),
                    Expr::lam("x", Expr::bvar(0), Expr::bvar(0)),
                ),
            },
        ],
    }
}

fn mutual_small_universe_module() -> CoreModule {
    let type0 = Level::succ(Level::zero());
    let block = MutualInductiveBlock::new(
        "Audit.Mutual",
        vec![],
        vec![
            InductiveDecl::new(
                "Audit.Mutual.Code",
                vec![],
                vec![],
                vec![],
                type0.clone(),
                vec![ConstructorDecl::new(
                    "Audit.Mutual.Code.mk",
                    Expr::pi(
                        "A",
                        Expr::sort(type0.clone()),
                        Expr::konst("Audit.Mutual.Code", vec![]),
                    ),
                )],
                None,
            ),
            InductiveDecl::new(
                "Audit.Mutual.Unit",
                vec![],
                vec![],
                vec![],
                type0,
                vec![ConstructorDecl::new(
                    "Audit.Mutual.Unit.mk",
                    Expr::konst("Audit.Mutual.Unit", vec![]),
                )],
                None,
            ),
        ],
    );
    CoreModule {
        name: Name::from_dotted("Audit.Mutual"),
        declarations: vec![Decl::MutualInductiveBlock {
            name: block.name.clone(),
            universe_params: block.universe_params.clone(),
            data: Box::new(block),
        }],
    }
}

fn assert_universe_bound_error(error: CertError) {
    assert_eq!(
        error,
        CertError::Kernel(Error::ConstructorUniverseBoundViolation {
            inductive: "Audit.Code".to_owned(),
            constructor: "Audit.Code.mk".to_owned(),
            field_index: 0,
            field_level: Level::succ(Level::succ(Level::zero())),
            inductive_sort: Level::succ(Level::zero()),
        })
    );
}

fn assert_mutual_universe_bound_error(error: CertError) {
    assert_eq!(
        error,
        CertError::Kernel(Error::ConstructorUniverseBoundViolation {
            inductive: "Audit.Mutual.Code".to_owned(),
            constructor: "Audit.Mutual.Code.mk".to_owned(),
            field_index: 0,
            field_level: Level::succ(Level::succ(Level::zero())),
            inductive_sort: Level::succ(Level::zero()),
        })
    );
}

#[test]
fn certificate_generation_rejects_small_universe_with_decoding_rule() {
    let error = build_module_cert(small_universe_module(), &[]).unwrap_err();
    assert_universe_bound_error(error);
}

#[test]
fn certificate_generation_rejects_mutual_small_universe() {
    let error = build_module_cert(mutual_small_universe_module(), &[]).unwrap_err();
    assert_mutual_universe_bound_error(error);
}

#[test]
fn producer_candidate_api_rejects_inductive_exploit_fail_closed() {
    let declaration = small_universe_module()
        .declarations
        .into_iter()
        .next()
        .unwrap();
    let candidate = CoreDeclCandidate { declaration };
    let limits = ProducerLimits {
        max_declarations: 1,
        max_expr_nodes: 10_000,
        max_level_nodes: 10_000,
        max_name_components: 16,
        max_reduction_steps: 10_000,
        max_conversion_steps: 10_000,
    };

    let error = precheck_core_decl_candidate(&Env::new(), &candidate, &limits).unwrap_err();
    assert!(matches!(
        error,
        CertError::Kernel(Error::InvalidInductive(message))
            if message.contains("inductive candidate precheck is not part")
    ));
}

#[test]
fn verifier_rejects_frozen_axiom_free_small_universe_in_every_policy_mode() {
    let decoded = decode_module_cert(SMALL_UNIVERSE_CERTIFICATE).unwrap();
    assert!(decoded.axiom_report.module_axioms.is_empty());

    for policy in [AxiomPolicy::normal(), AxiomPolicy::high_trust()] {
        let error = verify_module_cert(
            SMALL_UNIVERSE_CERTIFICATE,
            &mut VerifierSession::new(),
            &policy,
        )
        .unwrap_err();
        assert_universe_bound_error(error);
    }
}

#[test]
fn verifier_rejects_frozen_axiom_free_mutual_small_universe_in_every_policy_mode() {
    let decoded = decode_module_cert(MUTUAL_SMALL_UNIVERSE_CERTIFICATE).unwrap();
    assert!(decoded.axiom_report.module_axioms.is_empty());

    for policy in [AxiomPolicy::normal(), AxiomPolicy::high_trust()] {
        let error = verify_module_cert(
            MUTUAL_SMALL_UNIVERSE_CERTIFICATE,
            &mut VerifierSession::new(),
            &policy,
        )
        .unwrap_err();
        assert_mutual_universe_bound_error(error);
    }
}

use super::*;
use npa_kernel::{
    eq, eq_inductive, eq_rec_type, eq_refl, eq_refl_type, nat, nat_inductive, nat_succ, nat_zero,
    prop, type0, Binder, ConstructorDecl, Decl, Expr, InductiveDecl, Level, MutualInductiveBlock,
    RecursorDecl, Reducibility, UniverseConstraint,
};

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

fn legacy_bytes_from_current_cert(mut cert: ModuleCert) -> Vec<u8> {
    cert.header.format = LEGACY_FORMAT.to_owned();
    cert.header.core_spec = LEGACY_CORE_SPEC.to_owned();
    cert.hashes.export_hash = hash_with_domain(
        LEGACY_MODULE_EXPORT_DOMAIN,
        &encode_export_block_legacy(&cert.export_block),
    );
    cert.hashes.certificate_hash = hash_with_domain(
        LEGACY_MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash_for_header(&cert).unwrap(),
    );
    encode_module_cert(&cert).unwrap()
}

fn previous_bytes_from_current_cert(mut cert: ModuleCert) -> Vec<u8> {
    cert.header.format = PREVIOUS_FORMAT.to_owned();
    cert.header.core_spec = PREVIOUS_CORE_SPEC.to_owned();
    cert.hashes.export_hash = hash_with_domain(
        PREVIOUS_MODULE_EXPORT_DOMAIN,
        &encode_export_block_previous(&cert.export_block),
    );
    cert.hashes.certificate_hash = hash_with_domain(
        PREVIOUS_MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash_for_header(&cert).unwrap(),
    );
    encode_module_cert(&cert).unwrap()
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
    for name in &mut cert.name_table {
        if name.as_dotted() == "w" {
            *name = Name::from_dotted("z?meta");
        }
    }
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
    assert_eq!(import_offsets.len(), decoded.imports.len());
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
        cert.name_table
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
        empty.declarations[0].hashes.decl_interface_hash,
        constrained.declarations[0].hashes.decl_interface_hash
    );
    assert_ne!(empty.hashes.export_hash, constrained.hashes.export_hash);
    assert_ne!(
        empty.hashes.certificate_hash,
        constrained.hashes.certificate_hash
    );
}

#[test]
fn constrained_export_entries_encode_universe_constraints_in_current_format() {
    let cert = build_module_cert(constrained_axiom_module(vec![max_u_v_le_w()]), &[]).unwrap();

    assert_eq!(cert.header.format, FORMAT);
    assert_eq!(cert.header.core_spec, CORE_SPEC);
    assert_eq!(
        cert.hashes.export_hash,
        hash_with_domain(
            MODULE_EXPORT_DOMAIN,
            &encode_export_block(&cert.export_block)
        )
    );
    assert_eq!(
        cert.hashes.certificate_hash,
        hash_with_domain(
            MODULE_CERT_DOMAIN,
            &encode_module_cert_without_certificate_hash(&cert)
        )
    );
    assert_eq!(cert.export_block.len(), 1);
    assert_eq!(cert.export_block[0].universe_constraints.len(), 1);

    let bytes = encode_module_cert(&cert).unwrap();
    let decoded = decode_module_cert(&bytes).unwrap();
    assert_eq!(
        decoded.export_block[0].universe_constraints,
        cert.export_block[0].universe_constraints
    );

    let mut session = VerifierSession::new();
    verify_module_cert(&bytes, &mut session, &AxiomPolicy::normal()).unwrap();
}

#[test]
fn previous_constrained_public_exports_remain_readable() {
    let cert = build_module_cert(constrained_axiom_module(vec![max_u_v_le_w()]), &[]).unwrap();
    let bytes = previous_bytes_from_current_cert(cert);
    let decoded = decode_module_cert(&bytes).unwrap();

    assert_eq!(decoded.header.format, PREVIOUS_FORMAT);
    assert_eq!(decoded.header.core_spec, PREVIOUS_CORE_SPEC);
    assert_eq!(decoded.export_block[0].universe_constraints.len(), 1);

    let mut session = VerifierSession::new();
    let verified = verify_module_cert(&bytes, &mut session, &AxiomPolicy::normal()).unwrap();
    assert_eq!(verified.export_block()[0].universe_constraints.len(), 1);
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
    stripped_export.export_block[0].universe_constraints.clear();
    let stripped_decls = verified_module_to_kernel_decls(&stripped_export).unwrap();
    assert!(matches!(&stripped_decls[0], Decl::Axiom { .. }));
}

#[test]
fn legacy_unconstrained_public_exports_remain_readable() {
    let cert = build_module_cert(constrained_axiom_module(vec![]), &[]).unwrap();
    let bytes = legacy_bytes_from_current_cert(cert);
    let decoded = decode_module_cert(&bytes).unwrap();

    assert_eq!(decoded.header.format, LEGACY_FORMAT);
    assert_eq!(decoded.header.core_spec, LEGACY_CORE_SPEC);
    assert!(decoded.export_block[0].universe_constraints.is_empty());

    let mut session = VerifierSession::new();
    let verified = verify_module_cert(&bytes, &mut session, &AxiomPolicy::normal()).unwrap();
    assert!(verified.export_block()[0].universe_constraints.is_empty());
}

#[test]
fn legacy_constrained_public_exports_require_format_upgrade() {
    let cert = build_module_cert(constrained_axiom_module(vec![max_u_v_le_w()]), &[]).unwrap();
    let bytes = legacy_bytes_from_current_cert(cert);

    let err = verify_module_cert(&bytes, &mut VerifierSession::new(), &AxiomPolicy::normal())
        .unwrap_err();

    assert!(matches!(
        err,
        CertError::ConstrainedExportRequiresFormatUpgrade { name }
            if name == Name::from_dotted("List.map")
    ));
}

#[test]
fn universe_constraints_fast_verifier_accepts_canonical_constraint_bytes() {
    let cert = build_module_cert(
        constrained_axiom_module(height_order_regression_constraints()),
        &[],
    )
    .unwrap();
    assert!(matches!(
        cert.declarations[0].decl,
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
    } = cert.declarations[0].decl.clone()
    else {
        panic!("expected unconstrained axiom payload");
    };
    cert.declarations[0].decl = DeclPayload::AxiomConstrained {
        name,
        universe_params,
        universe_constraints: Vec::new(),
        ty,
    };
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
    let dependencies = vec![DependencyEntry {
        global_ref: dependency_ref.clone(),
        decl_interface_hash: test_hash(0x31),
    }];
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

fn first_term_tag_offset(bytes: &[u8]) -> usize {
    let mut offset = 0;
    skip_test_string(bytes, &mut offset);
    skip_test_string(bytes, &mut offset);
    skip_test_name(bytes, &mut offset);
    skip_test_imports(bytes, &mut offset);
    skip_test_name_table(bytes, &mut offset);
    skip_test_level_table(bytes, &mut offset);
    let term_len = read_test_uvar(bytes, &mut offset);
    assert!(term_len > 0);
    offset
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
        .declarations
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
        .declarations
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
            } if cert.name_table[*decl_name] == Name::from_dotted(name) => Some(recursor),
            DeclPayload::MutualInductiveBlock { inductives, .. } => inductives
                .iter()
                .find(|inductive| cert.name_table[inductive.name] == Name::from_dotted(name))
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
    let level_hashes = compute_level_hashes(&cert.level_table, &cert.name_table).unwrap();
    let term_hashes = compute_term_hashes(&cert.term_table, &level_hashes).unwrap();

    (
        generated_recursor_signature_hash(Some(recursor), &term_hashes, &cert.name_table).unwrap(),
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
        TermNode::Let { ty, value, body } => {
            remap_swapped_term_id(ty, lhs, rhs);
            remap_swapped_term_id(value, lhs, rhs);
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
    cert.term_table.swap(lhs, rhs);
    for term in &mut cert.term_table {
        remap_swapped_term_ids_in_term(term, lhs, rhs);
    }
    for decl in &mut cert.declarations {
        remap_swapped_term_ids_in_decl(&mut decl.decl, lhs, rhs);
    }
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
        TermNode::BVar(_)
        | TermNode::App(_, _)
        | TermNode::Lam { .. }
        | TermNode::Pi { .. }
        | TermNode::Let { .. } => {}
    }
}

fn remap_swapped_level_ids_in_decl(decl: &mut DeclPayload, lhs: LevelId, rhs: LevelId) {
    if let DeclPayload::Inductive { sort, .. } = decl {
        remap_swapped_level_id(sort, lhs, rhs);
    }
}

fn swap_level_table_entries(cert: &mut ModuleCert, lhs: LevelId, rhs: LevelId) {
    cert.level_table.swap(lhs, rhs);
    for level in &mut cert.level_table {
        remap_swapped_level_ids_in_level(level, lhs, rhs);
    }
    for term in &mut cert.term_table {
        remap_swapped_level_ids_in_term(term, lhs, rhs);
    }
    for decl in &mut cert.declarations {
        remap_swapped_level_ids_in_decl(&mut decl.decl, lhs, rhs);
    }
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
        TermNode::BVar(_)
        | TermNode::App(_, _)
        | TermNode::Lam { .. }
        | TermNode::Pi { .. }
        | TermNode::Let { .. } => {}
    }
}

fn rehash_cert_after_decl_change(cert: &mut ModuleCert) {
    let level_hashes = compute_level_hashes(&cert.level_table, &cert.name_table).unwrap();
    let term_hashes = compute_term_hashes(&cert.term_table, &level_hashes).unwrap();
    for decl in &mut cert.declarations {
        decl.hashes = compute_decl_hashes(
            &decl.decl,
            &decl.dependencies,
            &decl.axiom_dependencies,
            &cert.term_table,
            &level_hashes,
            &term_hashes,
            &cert.name_table,
        )
        .unwrap();
    }

    let mut previous_axioms: Vec<Vec<AxiomRef>> = Vec::new();
    let mut reports = Vec::new();
    for decl_index in 0..cert.declarations.len() {
        let decl = cert.declarations[decl_index].decl.clone();
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
        cert.declarations[decl_index].dependencies = dependencies;
        cert.declarations[decl_index].axiom_dependencies = transitive_axioms.clone();
        previous_axioms.push(transitive_axioms.clone());
        reports.push(DeclAxiomReport {
            decl_index,
            direct_axioms,
            transitive_axioms,
        });
    }
    cert.axiom_report = AxiomReport {
        module_axioms: union_axioms(
            reports
                .iter()
                .flat_map(|report| report.transitive_axioms.iter().cloned()),
        ),
        per_declaration: reports,
        core_features: Vec::new(),
    };

    for decl in &mut cert.declarations {
        decl.hashes = compute_decl_hashes(
            &decl.decl,
            &decl.dependencies,
            &decl.axiom_dependencies,
            &cert.term_table,
            &level_hashes,
            &term_hashes,
            &cert.name_table,
        )
        .unwrap();
    }
    cert.export_block =
        build_export_block(&cert.declarations, &cert.term_table, &term_hashes).unwrap();
    cert.hashes.export_hash = hash_with_domain(
        MODULE_EXPORT_DOMAIN,
        &encode_export_block(&cert.export_block),
    );
    cert.hashes.axiom_report_hash = hash_with_domain(
        b"NPA-AXIOM-REPORT-0.1",
        &encode_axiom_report(&cert.axiom_report),
    );
    cert.hashes.certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(cert),
    );
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
        hash_hex(cert.hashes.export_hash),
        expected.export_hash,
        "{label}"
    );
    assert_eq!(
        hash_hex(cert.hashes.axiom_report_hash),
        expected.axiom_report_hash,
        "{label}"
    );
    assert_eq!(
        hash_hex(cert.hashes.certificate_hash),
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

    assert_eq!(verified.module, Name::from_dotted("Test.Id"));
    assert_eq!(verified.declarations.len(), 1);
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
fn binder_names_do_not_affect_term_hashes() {
    let cert_a = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let cert_b = build_module_cert(id_module("B", "y"), &[]).unwrap();

    let value_a = match cert_a.declarations[0].decl {
        DeclPayload::Def { value, .. } => value,
        _ => panic!("expected def"),
    };
    let value_b = match cert_b.declarations[0].decl {
        DeclPayload::Def { value, .. } => value,
        _ => panic!("expected def"),
    };

    assert_eq!(term_hash(&cert_a, value_a), term_hash(&cert_b, value_b));
    assert_eq!(cert_a.hashes.export_hash, cert_b.hashes.export_hash);
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

    let dep_255 = DependencyEntry {
        global_ref: GlobalRef::Local { decl_index: 255 },
        decl_interface_hash: [0x01; 32],
    };
    let dep_16384 = DependencyEntry {
        global_ref: GlobalRef::Local { decl_index: 16_384 },
        decl_interface_hash: [0x02; 32],
    };
    let deps = [dep_255, dep_16384]
        .into_iter()
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    assert!(matches!(
        deps[0].global_ref,
        GlobalRef::Local { decl_index: 16_384 }
    ));
    assert_global_refs_are_in_canonical_byte_order(
        &deps
            .iter()
            .map(|dependency| dependency.global_ref.clone())
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
        DependencyEntry {
            global_ref: GlobalRef::Builtin {
                name: 1,
                decl_interface_hash: [0x05; 32],
            },
            decl_interface_hash: [0x05; 32],
        },
        DependencyEntry {
            global_ref: GlobalRef::LocalGenerated {
                decl_index: 0,
                name: 2,
            },
            decl_interface_hash: [0x06; 32],
        },
        DependencyEntry {
            global_ref: GlobalRef::Local { decl_index: 0 },
            decl_interface_hash: [0x07; 32],
        },
        DependencyEntry {
            global_ref: GlobalRef::Imported {
                import_index: 0,
                name: 3,
                decl_interface_hash: [0x08; 32],
            },
            decl_interface_hash: [0x08; 32],
        },
    ]
    .into_iter()
    .collect::<std::collections::BTreeSet<_>>()
    .into_iter()
    .map(|dependency| dependency.global_ref)
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
    assert_eq!(use_id_cert.imports.len(), 1);
    assert_eq!(
        use_id_cert.imports[0].export_hash,
        id_cert.hashes.export_hash
    );

    let use_id_bytes = encode_module_cert(&use_id_cert).unwrap();
    let verified_use_id =
        verify_module_cert(&use_id_bytes, &mut session, &AxiomPolicy::normal()).unwrap();
    assert_eq!(verified_use_id.module, Name::from_dotted("Test.UseId"));
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

    assert_eq!(verified_use_id.module, Name::from_dotted("Test.UseId"));
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
    assert_eq!(cert.imports.len(), 1);

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

    assert_eq!(cert_ab.imports, cert_ba.imports);
    assert_eq!(
        encode_module_cert(&cert_ab).unwrap(),
        encode_module_cert(&cert_ba).unwrap()
    );

    let mut noncanonical = cert_ab;
    noncanonical.imports.swap(0, 1);
    noncanonical.hashes.certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&noncanonical),
    );
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
        cert_ba.declarations[0].decl,
        DeclPayload::Axiom { name, .. } if cert_ba.name_table[name] == Name::from_dotted("A")
    ));
}

#[test]
fn declaration_names_are_committed_to_interface_and_export_hashes() {
    let p_cert = build_module_cert(named_axiom_module("Test.NamedAxiom", "P"), &[]).unwrap();
    let q_cert = build_module_cert(named_axiom_module("Test.NamedAxiom", "Q"), &[]).unwrap();

    assert_ne!(
        p_cert.declarations[0].hashes.decl_interface_hash,
        q_cert.declarations[0].hashes.decl_interface_hash
    );
    assert_ne!(p_cert.hashes.export_hash, q_cert.hashes.export_hash);
}

#[test]
fn rejects_unused_name_table_entry_even_if_rehashed() {
    let mut cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    cert.name_table.push(Name::from_dotted("zz.unused"));
    cert.hashes.certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&cert),
    );

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
    cert.declarations.swap(0, 1);
    cert.hashes.certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&cert),
    );

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
        cert.declarations[0].decl,
        DeclPayload::Axiom { name, .. } if cert.name_table[name] == Name::from_dotted("P")
    ));
    assert!(cert.declarations[1]
        .dependencies
        .iter()
        .any(|dependency| matches!(dependency.global_ref, GlobalRef::Local { decl_index: 0 })));

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
    assert_eq!(use_p_cert.axiom_report.module_axioms.len(), 1);
    let axiom = &use_p_cert.axiom_report.module_axioms[0];
    assert_eq!(use_p_cert.name_table[axiom.name], Name::from_dotted("P"));
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
        .imports
        .iter()
        .position(|import| import.module == Name::from_dotted("Test.Axiom"))
        .unwrap();
    let use_p_import_index = use_use_p_cert
        .imports
        .iter()
        .position(|import| import.module == Name::from_dotted("Test.UseAxiom"))
        .unwrap();
    let axiom = use_use_p_cert
        .axiom_report
        .module_axioms
        .iter()
        .find(|axiom| use_use_p_cert.name_table[axiom.name] == Name::from_dotted("P"))
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
        .axiom_report
        .module_axioms
        .iter()
        .find(|axiom| use_alias_cert.name_table[axiom.name] == Name::from_dotted("Eq.rec"))
        .expect("downstream module should report the builtin Eq.rec axiom");

    assert!(matches!(axiom.global_ref, GlobalRef::Builtin { .. }));
    assert!(matches!(
        use_alias_cert.declarations[0].axiom_dependencies.as_slice(),
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
        .axiom_report
        .module_axioms
        .iter()
        .find(|axiom| use_eq_rec_cert.name_table[axiom.name] == Name::from_dotted("Eq.rec"))
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
        .axiom_report
        .module_axioms
        .iter()
        .find(|axiom| use_eq_rec_cert.name_table[axiom.name] == Name::from_dotted("Eq.rec"))
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
    assert!(!cert.name_table.contains(&Name::from_dotted("P")));

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
    assert_eq!(use_public_id_cert.imports.len(), 1);
    assert_eq!(
        use_public_id_cert.imports[0].module,
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
        cert_a.declarations[0].hashes.decl_interface_hash,
        cert_b.declarations[0].hashes.decl_interface_hash
    );
    assert_ne!(
        cert_a.declarations[0].hashes.decl_certificate_hash,
        cert_b.declarations[0].hashes.decl_certificate_hash
    );
    assert_eq!(cert_a.hashes.export_hash, cert_b.hashes.export_hash);
    assert_eq!(
        cert_a.hashes.axiom_report_hash,
        cert_b.hashes.axiom_report_hash
    );
    assert_ne!(
        cert_a.hashes.certificate_hash,
        cert_b.hashes.certificate_hash
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
        cert_a.declarations[0].hashes.decl_interface_hash,
        cert_b.declarations[0].hashes.decl_interface_hash
    );
    assert_ne!(
        cert_a.declarations[0].hashes.decl_certificate_hash,
        cert_b.declarations[0].hashes.decl_certificate_hash
    );
    assert_eq!(cert_a.hashes.export_hash, cert_b.hashes.export_hash);
    assert_ne!(
        cert_a.hashes.certificate_hash,
        cert_b.hashes.certificate_hash
    );
}

#[test]
fn transparent_def_body_change_changes_interface_and_export_hashes() {
    let cert_a = build_module_cert(id_def_module_with_value(id_value("A", "x")), &[]).unwrap();
    let cert_b =
        build_module_cert(id_def_module_with_value(id_value_with_beta_redex()), &[]).unwrap();

    assert_ne!(
        cert_a.declarations[0].hashes.decl_interface_hash,
        cert_b.declarations[0].hashes.decl_interface_hash
    );
    assert_ne!(
        cert_a.declarations[0].hashes.decl_certificate_hash,
        cert_b.declarations[0].hashes.decl_certificate_hash
    );
    assert_ne!(cert_a.hashes.export_hash, cert_b.hashes.export_hash);
    assert_ne!(
        cert_a.hashes.certificate_hash,
        cert_b.hashes.certificate_hash
    );
}

#[test]
fn decl_interface_hash_def_payload_order_matches_certificate_contract() {
    let fixture = hash_contract_def_fixture();
    let hashes = compute_decl_hashes(
        &fixture.decl,
        &fixture.dependencies,
        &fixture.axiom_dependencies,
        &fixture.term_table,
        &[],
        &fixture.term_hashes,
        &fixture.names,
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
        &fixture.decl,
        &fixture.dependencies,
        &fixture.axiom_dependencies,
        &fixture.term_table,
        &[],
        &fixture.term_hashes,
        &fixture.names,
    )
    .unwrap();
    let DeclPayload::Def { value, .. } = &fixture.decl else {
        panic!("expected def payload");
    };
    let value = *value;

    let mut expected = Vec::new();
    expected.extend_from_slice(&hashes.decl_interface_hash);
    expected.extend_from_slice(&fixture.term_hashes[value]);
    encode_dependency_entries_to(&mut expected, &fixture.dependencies);
    encode_axiom_refs_to(&mut expected, &fixture.axiom_dependencies);
    assert_eq!(
        hashes.decl_certificate_hash,
        hash_with_domain(b"NPA-DECL-CERT-0.1", &expected)
    );

    let mut changed_value_hash = Vec::new();
    changed_value_hash.extend_from_slice(&hashes.decl_interface_hash);
    changed_value_hash.extend_from_slice(&test_hash(0x21));
    encode_dependency_entries_to(&mut changed_value_hash, &fixture.dependencies);
    encode_axiom_refs_to(&mut changed_value_hash, &fixture.axiom_dependencies);
    assert_ne!(
        hashes.decl_certificate_hash,
        hash_with_domain(b"NPA-DECL-CERT-0.1", &changed_value_hash)
    );

    let mut legacy_without_direct_value_hash = Vec::new();
    legacy_without_direct_value_hash.extend_from_slice(&hashes.decl_interface_hash);
    encode_dependency_entries_to(&mut legacy_without_direct_value_hash, &fixture.dependencies);
    encode_axiom_refs_to(
        &mut legacy_without_direct_value_hash,
        &fixture.axiom_dependencies,
    );
    assert_ne!(
        hashes.decl_certificate_hash,
        hash_with_domain(b"NPA-DECL-CERT-0.1", &legacy_without_direct_value_hash)
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
        .declarations
        .iter()
        .find(|decl| {
            matches!(
                &decl.decl,
                DeclPayload::Def { name, .. }
                    if cert_a.name_table[*name] == Name::from_dotted("alias")
            )
        })
        .unwrap();
    let alias_b = cert_b
        .declarations
        .iter()
        .find(|decl| {
            matches!(
                &decl.decl,
                DeclPayload::Def { name, .. }
                    if cert_b.name_table[*name] == Name::from_dotted("alias")
            )
        })
        .unwrap();

    assert_ne!(
        alias_a.hashes.decl_interface_hash,
        alias_b.hashes.decl_interface_hash
    );
    assert_ne!(cert_a.hashes.export_hash, cert_b.hashes.export_hash);
}

#[test]
fn opaque_theorem_axiom_change_changes_export_hash() {
    let cert_p1 = build_module_cert(theorem_using_axiom_module("p1"), &[]).unwrap();
    let cert_p2 = build_module_cert(theorem_using_axiom_module("p2"), &[]).unwrap();

    assert_ne!(cert_p1.hashes.export_hash, cert_p2.hashes.export_hash);
    assert_ne!(
        cert_p1.axiom_report.per_declaration[3].transitive_axioms,
        cert_p2.axiom_report.per_declaration[3].transitive_axioms
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
    let certificate_hash = cert.hashes.certificate_hash;

    let _normal_policy_hash = AxiomPolicy::normal().policy_hash();
    let mut high_trust_with_axiom = AxiomPolicy::high_trust();
    high_trust_with_axiom
        .allowlisted_axioms
        .insert(Name::from_dotted("P"));
    let _high_trust_policy_hash = high_trust_with_axiom.policy_hash();

    assert_eq!(certificate_hash, cert.hashes.certificate_hash);
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
    assert!(cert.declarations[1]
        .dependencies
        .iter()
        .any(|dependency| matches!(dependency.global_ref, GlobalRef::Local { decl_index: 0 })));
    assert!(cert.axiom_report.per_declaration[1]
        .transitive_axioms
        .iter()
        .any(|axiom| matches!(axiom.global_ref, GlobalRef::Local { decl_index: 0 })));
    let theorem_direct_axioms = cert.axiom_report.per_declaration[3]
        .direct_axioms
        .iter()
        .map(|axiom| cert.name_table[axiom.name].as_dotted())
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

    assert_eq!(verified.module, Name::from_dotted("Test.Unary"));
    assert!(matches!(
        verified.declarations.first().map(|decl| &decl.decl),
        Some(DeclPayload::Inductive { name, .. })
            if verified.name_table[*name] == Name::from_dotted("Unary")
    ));
    assert!(cert.export_block.iter().any(|entry| {
        entry.kind == ExportKind::Constructor
            && cert.name_table[entry.name] == Name::from_dotted("Unary.zero")
    }));
    assert!(cert.export_block.iter().any(|entry| {
        entry.kind == ExportKind::Constructor
            && cert.name_table[entry.name] == Name::from_dotted("Unary.succ")
    }));
}

#[test]
fn indexed_inductive_certificate_round_trips_and_verifies() {
    let cert = build_module_cert(indexed_inductive_module(), &[]).unwrap();
    let bytes = encode_module_cert(&cert).unwrap();
    let mut session = VerifierSession::new();
    let verified = verify_module_cert(&bytes, &mut session, &AxiomPolicy::normal()).unwrap();

    assert_eq!(verified.module, Name::from_dotted("Test.Indexed"));
    for name in [
        "Vec", "Vec.nil", "Vec.cons", "Vec.rec", "Fin", "Fin.zero", "Fin.succ", "Fin.rec",
    ] {
        assert!(
            cert.export_block
                .iter()
                .any(|entry| cert.name_table[entry.name] == Name::from_dotted(name)),
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

    assert_eq!(verified.module, Name::from_dotted("Test.EvenOdd"));
    assert!(matches!(
        verified.declarations.first().map(|decl| &decl.decl),
        Some(DeclPayload::MutualInductiveBlock { name, inductives, .. })
            if verified.name_table[*name] == Name::from_dotted("EvenOdd")
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
            cert.export_block
                .iter()
                .any(|entry| cert.name_table[entry.name] == Name::from_dotted(name)),
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
        .name_table
        .iter()
        .position(|name| name == &Name::from_dotted("Even"))
        .unwrap();
    let odd_name = cert
        .name_table
        .iter()
        .position(|name| name == &Name::from_dotted("Odd"))
        .unwrap();
    let mut changed = false;
    for term in &mut cert.term_table {
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
        cert.hashes.certificate_hash, decoded.hashes.certificate_hash,
        "nested Rose certificate hash must be stable after canonical decode"
    );

    let mut session = VerifierSession::new();
    verify_module_cert(&encoded, &mut session, &AxiomPolicy::normal())
        .expect("approved nested Rose certificate must verify");

    let rose_decl = decoded
        .declarations
        .iter()
        .find(|decl| matches!(decl.decl, DeclPayload::Inductive { name, .. } if decoded.name_table[name] == Name::from_dotted("Rose")))
        .expect("Rose declaration must be present");
    let DeclPayload::Inductive {
        recursor: Some(recursor),
        ..
    } = &rose_decl.decl
    else {
        panic!("Rose must have a generated recursor");
    };
    assert_eq!(
        decoded.name_table[recursor.name],
        Name::from_dotted("Rose.rec")
    );
    assert!(generated_recursor_signature_hash(
        Some(recursor),
        &(0..decoded.term_table.len())
            .map(|term| term_hash(&decoded, term))
            .collect::<Result<Vec<_>>>()
            .unwrap(),
        &decoded.name_table,
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
        .export_block
        .iter()
        .map(|entry| cert.name_table[entry.name].clone())
        .collect::<Vec<_>>();
    let mut sorted_export_names = export_names.clone();
    sorted_export_names.sort();
    assert_eq!(export_names, sorted_export_names);

    let block_index = cert
        .declarations
        .iter()
        .position(|decl| matches!(decl.decl, DeclPayload::MutualInductiveBlock { .. }))
        .unwrap();
    let (signature_hash, rule_hash) = recursor_artifact_hashes_for(&cert, "Even");

    let mut rules_changed = cert.clone();
    match &mut rules_changed.declarations[block_index].decl {
        DeclPayload::MutualInductiveBlock { inductives, .. } => {
            inductives[0].recursor.as_mut().unwrap().rules.major_index += 1;
        }
        _ => panic!("expected mutual inductive block"),
    }
    let (rules_changed_signature_hash, rules_changed_rule_hash) =
        recursor_artifact_hashes_for(&rules_changed, "Even");
    assert_eq!(signature_hash, rules_changed_signature_hash);
    assert_ne!(rule_hash, rules_changed_rule_hash);
}

#[test]
fn local_generated_constructor_can_be_referenced_after_inductive() {
    let cert = build_module_cert(unary_with_local_constructor_use_module(), &[]).unwrap();
    let def = &cert.declarations[1];
    assert!(def
        .dependencies
        .iter()
        .any(|dependency| matches!(dependency.global_ref, GlobalRef::LocalGenerated { .. })));

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
    let def = &use_unary_cert.declarations[0];
    assert!(def.dependencies.iter().any(|dependency| {
        matches!(
            dependency.global_ref,
            GlobalRef::Imported { name, .. }
                if use_unary_cert.name_table[name] == Name::from_dotted("Unary.zero")
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
    assert!(unary_cert.export_block.iter().any(|entry| {
        entry.kind == ExportKind::Recursor
            && unary_cert.name_table[entry.name] == Name::from_dotted("Unary.rec")
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
    assert!(use_rec_cert.declarations[0]
        .dependencies
        .iter()
        .any(|dependency| {
            matches!(
                dependency.global_ref,
                GlobalRef::Imported { name, .. }
                    if use_rec_cert.name_table[name] == Name::from_dotted("Unary.rec")
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
        .declarations
        .iter()
        .position(|decl| matches!(decl.decl, DeclPayload::Inductive { .. }))
        .unwrap();
    let unary_term = cert
        .term_table
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
    match &mut type_changed.declarations[inductive_index].decl {
        DeclPayload::Inductive {
            recursor: Some(recursor),
            ..
        } => recursor.ty = unary_term,
        _ => panic!("expected inductive with recursor"),
    }
    let (type_changed_signature_hash, type_changed_rule_hash) =
        recursor_artifact_hashes(&type_changed);
    assert_ne!(signature_hash, type_changed_signature_hash);
    assert_eq!(rule_hash, type_changed_rule_hash);

    let mut rules_changed = cert.clone();
    match &mut rules_changed.declarations[inductive_index].decl {
        DeclPayload::Inductive {
            recursor: Some(recursor),
            ..
        } => recursor.rules.major_index += 1,
        _ => panic!("expected inductive with recursor"),
    }
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
        .declarations
        .iter()
        .position(|decl| {
            matches!(
                &decl.decl,
                DeclPayload::Inductive { name, .. }
                    | DeclPayload::InductiveConstrained { name, .. }
                    if cert.name_table[*name] == Name::from_dotted("Vec")
            )
        })
        .unwrap();
    let (signature_hash, rule_hash) = recursor_artifact_hashes_for(&cert, "Vec");

    let mut rules_changed = cert.clone();
    match &mut rules_changed.declarations[vec_index].decl {
        DeclPayload::Inductive {
            recursor: Some(recursor),
            ..
        }
        | DeclPayload::InductiveConstrained {
            recursor: Some(recursor),
            ..
        } => recursor.rules.major_index += 1,
        _ => panic!("expected indexed inductive with recursor"),
    }
    let (rules_changed_signature_hash, rules_changed_rule_hash) =
        recursor_artifact_hashes_for(&rules_changed, "Vec");
    assert_eq!(signature_hash, rules_changed_signature_hash);
    assert_ne!(rule_hash, rules_changed_rule_hash);
}

#[test]
fn inductive_decl_interface_hash_commits_generated_recursor_artifact_hashes() {
    let cert = build_module_cert(unary_inductive_with_recursor_type_anchor_module(), &[]).unwrap();
    let inductive_index = cert
        .declarations
        .iter()
        .position(|decl| matches!(decl.decl, DeclPayload::Inductive { .. }))
        .unwrap();
    let original_interface_hash = cert.declarations[inductive_index]
        .hashes
        .decl_interface_hash;
    let unary_term = cert
        .term_table
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
    match &mut signature_changed.declarations[inductive_index].decl {
        DeclPayload::Inductive {
            recursor: Some(recursor),
            ..
        } => recursor.ty = unary_term,
        _ => panic!("expected inductive with recursor"),
    }
    rehash_cert_after_decl_change(&mut signature_changed);

    let mut rules_changed = cert.clone();
    match &mut rules_changed.declarations[inductive_index].decl {
        DeclPayload::Inductive {
            recursor: Some(recursor),
            ..
        } => recursor.rules.major_index += 1,
        _ => panic!("expected inductive with recursor"),
    }
    rehash_cert_after_decl_change(&mut rules_changed);

    let signature_changed_interface_hash = signature_changed.declarations[inductive_index]
        .hashes
        .decl_interface_hash;
    let rules_changed_interface_hash = rules_changed.declarations[inductive_index]
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
    match &mut cert.declarations[0].decl {
        DeclPayload::Inductive {
            recursor: Some(recursor),
            ..
        } => recursor.rules.major_index += 1,
        _ => panic!("expected inductive with recursor"),
    }
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
        .declarations
        .iter()
        .position(|decl| matches!(decl.decl, DeclPayload::Inductive { .. }))
        .unwrap();
    let unary_term = cert
        .term_table
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
    match &mut cert.declarations[inductive_index].decl {
        DeclPayload::Inductive {
            recursor: Some(recursor),
            ..
        } => recursor.ty = unary_term,
        _ => panic!("expected inductive with recursor"),
    }
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
        .export_block
        .iter()
        .find(|entry| {
            entry.kind == ExportKind::Inductive
                && cert.name_table[entry.name] == Name::from_dotted("Box")
        })
        .unwrap();
    assert!(matches!(cert.term_table[box_entry.ty], TermNode::Pi { .. }));

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
    let actual = cert.declarations[0].hashes.decl_interface_hash;
    cert.declarations[0].hashes.decl_interface_hash[0] ^= 0x01;
    let expected = cert.declarations[0].hashes.decl_interface_hash;

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
    cert.declarations[0].hashes.decl_certificate_hash[0] ^= 0x01;

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
    match &mut cert.declarations[1].decl {
        DeclPayload::Theorem { proof, ty, .. } => *proof = *ty,
        _ => panic!("expected theorem"),
    }
    cert.hashes.certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&cert),
    );

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
    match &mut proof_cert.declarations[1].decl {
        DeclPayload::Theorem { proof, ty, .. } => *proof = *ty,
        _ => panic!("expected theorem"),
    }
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
    axiom_report_cert.axiom_report.module_axioms.clear();
    axiom_report_cert.hashes.axiom_report_hash = hash_with_domain(
        b"NPA-AXIOM-REPORT-0.1",
        &encode_axiom_report(&axiom_report_cert.axiom_report),
    );
    axiom_report_cert.hashes.certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&axiom_report_cert),
    );
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
    import_hash_cert.imports[0].export_hash[0] ^= 0x01;
    import_hash_cert.hashes.certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&import_hash_cert),
    );
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
    noncanonical_table_cert
        .term_table
        .push(noncanonical_table_cert.term_table[0].clone());
    noncanonical_table_cert.hashes.certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&noncanonical_table_cert),
    );
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
    assert!(matches!(err, CertError::DecodeError));
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
fn rejects_unknown_term_tag_as_unsupported_encoding() {
    let cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    let mut bytes = encode_module_cert(&cert).unwrap();
    let offset = first_term_tag_offset(&bytes);
    bytes[offset] = 0x7f;

    let err = decode_module_cert(&bytes).unwrap_err();
    assert!(matches!(err, CertError::UnsupportedEncoding { tag: 0x7f }));
}

#[test]
fn rejects_export_block_that_was_rehashed_but_not_derived_from_declarations() {
    let mut cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    cert.export_block.clear();
    cert.hashes.export_hash = hash_with_domain(
        MODULE_EXPORT_DOMAIN,
        &encode_export_block(&cert.export_block),
    );
    cert.hashes.certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&cert),
    );

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
    cert.axiom_report.module_axioms.clear();
    cert.hashes.axiom_report_hash = hash_with_domain(
        b"NPA-AXIOM-REPORT-0.1",
        &encode_axiom_report(&cert.axiom_report),
    );
    cert.hashes.certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&cert),
    );

    let bytes = encode_module_cert(&cert).unwrap();
    let mut session = VerifierSession::new();
    let err = verify_module_cert(&bytes, &mut session, &AxiomPolicy::normal()).unwrap_err();
    assert!(matches!(err, CertError::AxiomReportMismatch { .. }));
}

#[test]
fn rejects_noncanonical_term_table_even_if_bytes_round_trip() {
    let mut cert = build_module_cert(id_module("A", "x"), &[]).unwrap();
    cert.term_table.push(cert.term_table[0].clone());
    cert.hashes.certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&cert),
    );

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
        .term_table
        .iter()
        .position(|term| matches!(term, TermNode::Sort(_)))
        .unwrap();
    let bvar = cert
        .term_table
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
        .name_table
        .iter()
        .position(|name| *name == Name::from_dotted("u"))
        .unwrap();
    let zero = cert
        .level_table
        .iter()
        .position(|level| matches!(level, LevelNode::Zero))
        .unwrap();
    let param = cert
        .level_table
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
    let last = cert.term_table.len() - 1;
    cert.term_table.push(TermNode::App(last, last));
    cert.hashes.certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&cert),
    );

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
        .name_table
        .iter()
        .position(|name| *name == Name::from_dotted("u"))
        .unwrap();
    assert_eq!(cert.level_table, vec![LevelNode::Param(u)]);

    cert.level_table = vec![LevelNode::Zero, LevelNode::Param(u), LevelNode::Max(0, 1)];
    for term in &mut cert.term_table {
        replace_level_refs(term, 0, 2);
    }
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
    let last = cert.level_table.len() - 1;
    cert.level_table.push(LevelNode::Succ(last));
    cert.hashes.certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&cert),
    );

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
        .term_table
        .iter()
        .position(|term| matches!(term, TermNode::BVar(0)))
        .unwrap();
    match &mut cert.declarations[0].decl {
        DeclPayload::Def { value, .. } => *value = bvar_zero,
        _ => panic!("expected def"),
    }
    cert.hashes.certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&cert),
    );

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
    use_id_cert.imports[0].certificate_hash = None;
    use_id_cert.hashes.certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&use_id_cert),
    );
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
    use_id_cert.imports[0].certificate_hash = None;
    use_id_cert.hashes.certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&use_id_cert),
    );
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
    use_id_cert.imports[0].certificate_hash.as_mut().unwrap()[0] ^= 0x01;
    use_id_cert.hashes.certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&use_id_cert),
    );

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
    use_id_cert.imports[0].certificate_hash.as_mut().unwrap()[0] ^= 0x01;
    use_id_cert.hashes.certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&use_id_cert),
    );

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
    use_id_cert.imports[0].export_hash[0] ^= 0x01;
    use_id_cert.hashes.certificate_hash = hash_with_domain(
        MODULE_CERT_DOMAIN,
        &encode_module_cert_without_certificate_hash(&use_id_cert),
    );

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
    assert!(id_cert.axiom_report.module_axioms.is_empty());

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

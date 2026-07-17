use std::env;
use std::fs;
use std::path::{Path, PathBuf};

use npa_cert::{
    build_module_cert, encode_module_cert, generate_inductive_artifacts_v1,
    generate_mutual_inductive_artifacts_v1, term_hash, verify_module_cert, AxiomPolicy, CoreModule,
    DeclPayload, ModuleCert, Name, TermNode, VerifierSession,
};
use npa_kernel::{
    eq, eq_refl, nat, nat_succ, nat_zero, prop, type0, Binder, ConstructorDecl, Decl, Expr,
    InductiveDecl, Level, MutualInductiveBlock, UniverseConstraint,
};
use sha2::{Digest, Sha256};

fn list_type(level: Level, elem: Expr) -> Expr {
    Expr::app(Expr::konst("List", vec![level]), elem)
}

fn list_base() -> InductiveDecl {
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

fn option_type(level: Level, elem: Expr) -> Expr {
    Expr::app(Expr::konst("Option", vec![level]), elem)
}

fn option_base() -> InductiveDecl {
    let u = Level::param("u");
    InductiveDecl::new(
        "Option",
        vec!["u".to_owned()],
        vec![Binder::new("A", Expr::sort(u.clone()))],
        vec![],
        u.clone(),
        vec![
            ConstructorDecl::new(
                "Option.none",
                Expr::pi(
                    "A",
                    Expr::sort(u.clone()),
                    option_type(u.clone(), Expr::bvar(0)),
                ),
            ),
            ConstructorDecl::new(
                "Option.some",
                Expr::pi(
                    "A",
                    Expr::sort(u.clone()),
                    Expr::pi(
                        "value",
                        Expr::bvar(0),
                        option_type(u.clone(), Expr::bvar(1)),
                    ),
                ),
            ),
        ],
        None,
    )
}

fn prod_type(level: Level, first: Expr, second: Expr) -> Expr {
    Expr::apps(Expr::konst("Prod", vec![level]), vec![first, second])
}

fn prod_base() -> InductiveDecl {
    let u = Level::param("u");
    InductiveDecl::new(
        "Prod",
        vec!["u".to_owned()],
        vec![
            Binder::new("A", Expr::sort(u.clone())),
            Binder::new("B", Expr::sort(u.clone())),
        ],
        vec![],
        u.clone(),
        vec![ConstructorDecl::new(
            "Prod.mk",
            Expr::pi(
                "A",
                Expr::sort(u.clone()),
                Expr::pi(
                    "B",
                    Expr::sort(u.clone()),
                    Expr::pi(
                        "fst",
                        Expr::bvar(1),
                        Expr::pi(
                            "snd",
                            Expr::bvar(1),
                            prod_type(u.clone(), Expr::bvar(3), Expr::bvar(2)),
                        ),
                    ),
                ),
            ),
        )],
        None,
    )
}

fn rose_type(level: Level, elem: Expr) -> Expr {
    Expr::app(Expr::konst("Rose", vec![level]), elem)
}

fn rose_base() -> InductiveDecl {
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
                    Expr::pi(
                        "children",
                        list_type(u.clone(), rose_type(u.clone(), Expr::bvar(1))),
                        rose_type(u, Expr::bvar(2)),
                    ),
                ),
            ),
        )],
        None,
    )
}

fn nested_module() -> CoreModule {
    let list = generate_inductive_artifacts_v1(&list_base()).unwrap();
    let rose = generate_inductive_artifacts_v1(&rose_base()).unwrap();
    CoreModule {
        name: Name::from_dotted("Conformance.NestedRose"),
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

fn nested_all_type(level: Level, elem: Expr) -> Expr {
    Expr::app(Expr::konst("NestedAll", vec![level]), elem)
}

fn nested_all_base() -> InductiveDecl {
    let u = Level::param("u");
    let recursive = nested_all_type(u.clone(), Expr::bvar(1));
    InductiveDecl::new(
        "NestedAll",
        vec!["u".to_owned()],
        vec![Binder::new("A", Expr::sort(u.clone()))],
        vec![],
        u.clone(),
        vec![ConstructorDecl::new(
            "NestedAll.mk",
            Expr::pi(
                "A",
                Expr::sort(u.clone()),
                Expr::pi(
                    "value",
                    Expr::bvar(0),
                    Expr::pi(
                        "children",
                        prod_type(
                            u.clone(),
                            option_type(u.clone(), recursive.clone()),
                            list_type(u.clone(), recursive),
                        ),
                        nested_all_type(u, Expr::bvar(2)),
                    ),
                ),
            ),
        )],
        None,
    )
}

fn nested_all_module() -> CoreModule {
    let list = generate_inductive_artifacts_v1(&list_base()).unwrap();
    let option = generate_inductive_artifacts_v1(&option_base()).unwrap();
    let prod = generate_inductive_artifacts_v1(&prod_base()).unwrap();
    let nested = generate_inductive_artifacts_v1(&nested_all_base()).unwrap();
    let family_type = |name: &str| Decl::Inductive {
        name: name.to_owned(),
        universe_params: vec!["u".to_owned()],
        ty: Expr::pi(
            "A",
            Expr::sort(Level::param("u")),
            Expr::sort(Level::param("u")),
        ),
        data: Box::new(match name {
            "List" => list.clone(),
            "Option" => option.clone(),
            _ => unreachable!(),
        }),
    };
    CoreModule {
        name: Name::from_dotted("Conformance.NestedAll"),
        declarations: vec![
            family_type("List"),
            family_type("Option"),
            Decl::Inductive {
                name: "Prod".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: Expr::pi(
                    "A",
                    Expr::sort(Level::param("u")),
                    Expr::pi(
                        "B",
                        Expr::sort(Level::param("u")),
                        Expr::sort(Level::param("u")),
                    ),
                ),
                data: Box::new(prod),
            },
            Decl::Inductive {
                name: "NestedAll".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: Expr::pi(
                    "A",
                    Expr::sort(Level::param("u")),
                    Expr::sort(Level::param("u")),
                ),
                data: Box::new(nested),
            },
        ],
    }
}

fn vec_type(level: Level, element: Expr, length: Expr) -> Expr {
    Expr::apps(Expr::konst("Vec", vec![level]), vec![element, length])
}

fn vec_base() -> InductiveDecl {
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

fn fin_type(length: Expr) -> Expr {
    Expr::app(Expr::konst("Fin", vec![]), length)
}

fn fin_base() -> InductiveDecl {
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

fn indexed_module() -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Conformance.Indexed"),
        declarations: vec![
            Decl::Inductive {
                name: "Vec".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: Expr::pi(
                    "A",
                    Expr::sort(Level::param("u")),
                    Expr::pi("n", nat(), Expr::sort(Level::param("u"))),
                ),
                data: Box::new(generate_inductive_artifacts_v1(&vec_base()).unwrap()),
            },
            Decl::Inductive {
                name: "Fin".to_owned(),
                universe_params: vec![],
                ty: Expr::pi("n", nat(), Expr::sort(type0())),
                data: Box::new(generate_inductive_artifacts_v1(&fin_base()).unwrap()),
            },
        ],
    }
}

fn vec_nil(level: Level, element: Expr) -> Expr {
    Expr::app(Expr::konst("Vec.nil", vec![level]), element)
}

fn imported_vec_iota_term() -> Expr {
    let element_level = type0();
    let motive_level = Level::succ(element_level.clone());
    let motive = Expr::lam(
        "n",
        nat(),
        Expr::lam(
            "_",
            vec_type(element_level.clone(), nat(), Expr::bvar(0)),
            Expr::sort(element_level.clone()),
        ),
    );
    let nil_case = vec_type(element_level.clone(), nat(), nat_zero());
    let cons_case = Expr::lam(
        "n",
        nat(),
        Expr::lam(
            "x",
            nat(),
            Expr::lam(
                "xs",
                vec_type(element_level.clone(), nat(), Expr::bvar(1)),
                Expr::lam(
                    "_ih",
                    Expr::sort(element_level.clone()),
                    vec_type(element_level.clone(), nat(), nat_succ(Expr::bvar(3))),
                ),
            ),
        ),
    );
    Expr::apps(
        Expr::konst("Vec.rec", vec![element_level.clone(), motive_level]),
        vec![
            nat(),
            motive,
            nil_case,
            cons_case,
            nat_zero(),
            vec_nil(element_level, nat()),
        ],
    )
}

fn imported_vec_iota_module() -> CoreModule {
    let element_level = type0();
    CoreModule {
        name: Name::from_dotted("Conformance.ImportedVecIota"),
        declarations: vec![Decl::Theorem {
            name: "Conformance.ImportedVecIota.nil".to_owned(),
            universe_params: vec![],
            ty: imported_vec_iota_term(),
            proof: vec_nil(element_level, nat()),
        }],
    }
}

fn even_type(index: Expr) -> Expr {
    Expr::app(Expr::konst("Even", vec![]), index)
}

fn odd_type(index: Expr) -> Expr {
    Expr::app(Expr::konst("Odd", vec![]), index)
}

fn mutual_base() -> MutualInductiveBlock {
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

fn mutual_module() -> CoreModule {
    let block = generate_mutual_inductive_artifacts_v1(&mutual_base()).unwrap();
    CoreModule {
        name: Name::from_dotted("Conformance.EvenOdd"),
        declarations: vec![Decl::MutualInductiveBlock {
            name: block.name.clone(),
            universe_params: block.universe_params.clone(),
            data: Box::new(block),
        }],
    }
}

fn even_zero() -> Expr {
    Expr::konst("Even.zero", vec![])
}

fn odd_succ(index: Expr, proof: Expr) -> Expr {
    Expr::apps(Expr::konst("Odd.succ", vec![]), vec![index, proof])
}

fn imported_mutual_iota_recursor_term() -> Expr {
    let proposition = eq(type0(), nat(), nat_zero(), nat_zero());
    let even_motive = Expr::lam(
        "n",
        nat(),
        Expr::lam("_", even_type(Expr::bvar(0)), proposition.clone()),
    );
    let odd_motive = Expr::lam(
        "n",
        nat(),
        Expr::lam("_", odd_type(Expr::bvar(0)), proposition.clone()),
    );
    let even_step = Expr::lam(
        "n",
        nat(),
        Expr::lam(
            "h",
            odd_type(Expr::bvar(0)),
            Expr::lam("ih", proposition.clone(), Expr::bvar(0)),
        ),
    );
    let odd_step = Expr::lam(
        "n",
        nat(),
        Expr::lam(
            "h",
            even_type(Expr::bvar(0)),
            Expr::lam("ih", proposition.clone(), Expr::bvar(0)),
        ),
    );
    let odd_one = odd_succ(nat_zero(), even_zero());
    Expr::apps(
        Expr::konst("Odd.rec", vec![]),
        vec![
            even_motive,
            odd_motive,
            eq_refl(type0(), nat(), nat_zero()),
            even_step,
            odd_step,
            nat_succ(nat_zero()),
            odd_one,
        ],
    )
}

fn imported_mutual_iota_module() -> CoreModule {
    let proposition = eq(type0(), nat(), nat_zero(), nat_zero());
    let proof = eq_refl(type0(), nat(), nat_zero());
    CoreModule {
        name: Name::from_dotted("Conformance.ImportedMutualIota"),
        declarations: vec![Decl::Theorem {
            name: "Conformance.ImportedMutualIota.cross_family".to_owned(),
            universe_params: vec![],
            ty: eq(
                prop(),
                proposition.clone(),
                imported_mutual_iota_recursor_term(),
                proof.clone(),
            ),
            proof: eq_refl(prop(), proposition, proof),
        }],
    }
}

fn identity_type() -> Expr {
    Expr::pi(
        "A",
        Expr::sort(Level::param("u")),
        Expr::pi("x", Expr::bvar(0), Expr::bvar(1)),
    )
}

fn identity_proof() -> Expr {
    Expr::lam(
        "A",
        Expr::sort(Level::param("u")),
        Expr::lam("x", Expr::bvar(0), Expr::bvar(0)),
    )
}

fn unchecked_provider_module() -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Conformance.UncheckedProvider"),
        declarations: vec![Decl::Theorem {
            name: "Conformance.UncheckedProvider.id".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: identity_type(),
            proof: identity_proof(),
        }],
    }
}

fn unchecked_consumer_module() -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Conformance.UncheckedConsumer"),
        declarations: vec![Decl::Theorem {
            name: "Conformance.UncheckedConsumer.id".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: identity_type(),
            proof: Expr::konst("Conformance.UncheckedProvider.id", vec![Level::param("u")]),
        }],
    }
}

fn forbidden_axiom_module() -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Conformance.ForbiddenAxiom"),
        declarations: vec![Decl::Axiom {
            name: "Conformance.ForbiddenAxiom.P".to_owned(),
            universe_params: vec![],
            ty: Expr::sort(prop()),
        }],
    }
}

fn hash_with_domain(domain: &[u8], payload: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(domain);
    hasher.update(payload);
    hasher.finalize().into()
}

fn recompute_module_certificate_hash(certificate: &mut ModuleCert) {
    let encoded = encode_module_cert(certificate).unwrap();
    let payload = &encoded[..encoded.len() - 32];
    certificate.hashes.certificate_hash = hash_with_domain(b"NPA-MODULE-CERT-0.2.0", payload);
}

fn semantically_invalid_provider(mut certificate: ModuleCert) -> ModuleCert {
    let bvar_zero = certificate
        .term_table
        .iter()
        .position(|term| matches!(term, TermNode::BVar(0)))
        .unwrap();
    let bvar_one = certificate
        .term_table
        .iter()
        .position(|term| matches!(term, TermNode::BVar(1)))
        .unwrap();
    let inner_lambda = certificate
        .term_table
        .iter()
        .position(|term| {
            matches!(
                term,
                TermNode::Lam { ty, body } if *ty == bvar_zero && *body == bvar_zero
            )
        })
        .unwrap();
    match &mut certificate.term_table[inner_lambda] {
        TermNode::Lam { body, .. } => *body = bvar_one,
        _ => unreachable!(),
    }
    let proof = match certificate.declarations[0].decl {
        DeclPayload::Theorem { proof, .. } => proof,
        _ => unreachable!(),
    };
    let mut payload = Vec::new();
    payload.extend(certificate.declarations[0].hashes.decl_interface_hash);
    payload.extend(term_hash(&certificate, proof).unwrap());
    payload.push(0);
    certificate.declarations[0].hashes.decl_certificate_hash =
        hash_with_domain(b"NPA-DECL-CERT-0.1", &payload);
    recompute_module_certificate_hash(&mut certificate);
    certificate
}

fn write_unchecked_import_fixtures(output: &Path) {
    let good_certificate = build_module_cert(unchecked_provider_module(), &[]).unwrap();
    let good_bytes = encode_module_cert(&good_certificate).unwrap();
    let mut verifier = VerifierSession::new();
    let verified_provider =
        verify_module_cert(&good_bytes, &mut verifier, &AxiomPolicy::normal()).unwrap();
    let bad_certificate = semantically_invalid_provider(good_certificate);

    let mut dependency_hash_mismatch = build_module_cert(
        unchecked_consumer_module(),
        std::slice::from_ref(&verified_provider),
    )
    .unwrap();
    dependency_hash_mismatch.declarations[0].dependencies[0].decl_interface_hash[0] ^= 1;
    let mut unpinned_consumer =
        build_module_cert(unchecked_consumer_module(), &[verified_provider]).unwrap();
    unpinned_consumer.imports[0].certificate_hash = None;
    recompute_module_certificate_hash(&mut unpinned_consumer);
    let mut pinned_consumer = unpinned_consumer.clone();
    pinned_consumer.imports[0].certificate_hash = Some(bad_certificate.hashes.certificate_hash);
    recompute_module_certificate_hash(&mut pinned_consumer);

    fs::write(
        output.join("dependency-hash-mismatch-v0.2.npcert"),
        encode_module_cert(&dependency_hash_mismatch).unwrap(),
    )
    .unwrap();
    fs::write(
        output.join("unchecked-provider-bad-v0.2.npcert"),
        encode_module_cert(&bad_certificate).unwrap(),
    )
    .unwrap();
    fs::write(
        output.join("unchecked-consumer-unpinned-v0.2.npcert"),
        encode_module_cert(&unpinned_consumer).unwrap(),
    )
    .unwrap();
    fs::write(
        output.join("unchecked-consumer-pinned-v0.2.npcert"),
        encode_module_cert(&pinned_consumer).unwrap(),
    )
    .unwrap();
}

fn write_fixture(output: &Path, file_name: &str, module: CoreModule) {
    let certificate = build_module_cert(module, &[]).unwrap();
    let bytes = encode_module_cert(&certificate).unwrap();
    fs::write(output.join(file_name), bytes).unwrap();
}

fn write_noncanonical_identity_fixture(output: &Path) {
    let mut certificate = build_module_cert(
        CoreModule {
            name: Name::from_dotted("Conformance.PartialIdentity"),
            declarations: Vec::new(),
        },
        &[],
    )
    .unwrap();
    let unused_name = Name::from_dotted("zzzzUnusedDiagnosticName");
    assert!(certificate
        .name_table
        .last()
        .is_none_or(|last| last < &unused_name));
    certificate.name_table.push(unused_name);
    recompute_module_certificate_hash(&mut certificate);
    fs::write(
        output.join("noncanonical-unused-name-v0.2.npcert"),
        encode_module_cert(&certificate).unwrap(),
    )
    .unwrap();
}

fn write_indexed_imported_iota_fixtures(output: &Path) {
    let indexed_certificate = build_module_cert(indexed_module(), &[]).unwrap();
    let indexed_bytes = encode_module_cert(&indexed_certificate).unwrap();
    let mut verifier = VerifierSession::new();
    let indexed_verified =
        verify_module_cert(&indexed_bytes, &mut verifier, &AxiomPolicy::normal()).unwrap();
    let consumer = build_module_cert(imported_vec_iota_module(), &[indexed_verified]).unwrap();

    fs::write(output.join("indexed-v0.2.npcert"), indexed_bytes).unwrap();
    fs::write(
        output.join("imported-indexed-iota-v0.2.npcert"),
        encode_module_cert(&consumer).unwrap(),
    )
    .unwrap();
}

fn write_mutual_imported_iota_fixtures(output: &Path) {
    let mutual_certificate = build_module_cert(mutual_module(), &[]).unwrap();
    let mutual_bytes = encode_module_cert(&mutual_certificate).unwrap();
    let mut verifier = VerifierSession::new();
    let mutual_verified =
        verify_module_cert(&mutual_bytes, &mut verifier, &AxiomPolicy::normal()).unwrap();
    let consumer = build_module_cert(imported_mutual_iota_module(), &[mutual_verified]).unwrap();

    fs::write(output.join("mutual-v0.2.npcert"), mutual_bytes).unwrap();
    fs::write(
        output.join("imported-mutual-iota-v0.2.npcert"),
        encode_module_cert(&consumer).unwrap(),
    )
    .unwrap();
}

fn main() {
    let output = env::args_os()
        .nth(1)
        .map(PathBuf::from)
        .expect("usage: generate_ext_conformance OUTPUT_DIR");
    fs::create_dir_all(&output).unwrap();
    write_indexed_imported_iota_fixtures(&output);
    write_mutual_imported_iota_fixtures(&output);
    write_fixture(&output, "nested-v0.2.npcert", nested_module());
    write_fixture(&output, "nested-all-v0.2.npcert", nested_all_module());
    write_fixture(
        &output,
        "forbidden-axiom-v0.2.npcert",
        forbidden_axiom_module(),
    );
    write_noncanonical_identity_fixture(&output);
    write_unchecked_import_fixtures(&output);
}

use std::{
    env,
    path::{Path, PathBuf},
};

use npa_cert::{
    build_module_cert, encode_module_cert, generate_inductive_artifacts_v1,
    generate_mutual_inductive_artifacts_v1, term_hash, verify_module_cert, AxiomPolicy, CertError,
    CoreModule, DeclPayload, DependencyEntryKind, LocalImplementationDependencyErrorReason,
    ModuleCert, Name, TermNode, VerifierSession,
};
use npa_kernel::{
    eq, eq_refl, nat, nat_succ, nat_zero, prop, type0, Binder, ConstructorDecl, Decl, Expr,
    InductiveDecl, Level, MutualInductiveBlock, Reducibility, UniverseConstraint,
};
use sha2::{Digest, Sha256};

#[path = "../../npa-api/examples/support/closed_private_tree.rs"]
mod closed_private_tree;

use closed_private_tree::ClosedPrivateDirectory;

fn write_output(
    output: &ClosedPrivateDirectory,
    file_name: &str,
    bytes: &[u8],
) -> Result<(), String> {
    output
        .create_new_file(Path::new(file_name), bytes)
        .map_err(|error| format!("cannot write {file_name}: {error}"))
}

fn run() -> Result<(), String> {
    let mut arguments = env::args_os().skip(1);
    let output = arguments
        .next()
        .map(PathBuf::from)
        .ok_or_else(|| "usage: generate_ext_conformance OUTPUT_DIR".to_owned())?;
    if arguments.next().is_some() {
        return Err("usage: generate_ext_conformance OUTPUT_DIR".to_owned());
    }
    generate(&output)
}

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

fn opaque_direct_module() -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Conformance.OpaqueDirect"),
        declarations: vec![
            Decl::Def {
                name: "hidden_nat".to_owned(),
                universe_params: vec![],
                ty: nat(),
                value: nat_zero(),
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

fn opaque_alias_chain_module() -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Conformance.OpaqueAliasChain"),
        declarations: vec![
            Decl::Def {
                name: "hidden".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: identity_type(),
                value: identity_proof(),
                reducibility: Reducibility::Opaque,
            },
            Decl::Def {
                name: "alias".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: identity_type(),
                value: Expr::konst("hidden", vec![Level::param("u")]),
                reducibility: Reducibility::Reducible,
            },
            Decl::Theorem {
                name: "uses_alias".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: identity_type(),
                proof: Expr::konst("alias", vec![Level::param("u")]),
            },
        ],
    }
}

fn opaque_alias_module() -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Conformance.OpaqueAlias"),
        declarations: vec![
            Decl::Def {
                name: "hidden".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: identity_type(),
                value: identity_proof(),
                reducibility: Reducibility::Opaque,
            },
            Decl::Def {
                name: "alias".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: identity_type(),
                value: Expr::konst("hidden", vec![Level::param("u")]),
                reducibility: Reducibility::Reducible,
            },
        ],
    }
}

fn invalid_target_base_module() -> CoreModule {
    CoreModule {
        name: Name::from_dotted("Conformance.InvalidOpaqueTarget"),
        declarations: vec![
            Decl::Def {
                name: "a_reducible".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: identity_type(),
                value: identity_proof(),
                reducibility: Reducibility::Reducible,
            },
            Decl::Def {
                name: "hidden".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: identity_type(),
                value: identity_proof(),
                reducibility: Reducibility::Opaque,
            },
            Decl::Theorem {
                name: "z_uses_hidden".to_owned(),
                universe_params: vec!["u".to_owned()],
                ty: identity_type(),
                proof: Expr::konst("hidden", vec![Level::param("u")]),
            },
        ],
    }
}

fn hash_with_domain(domain: &[u8], payload: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(domain);
    hasher.update(payload);
    hasher.finalize().into()
}

fn recompute_module_certificate_hash(certificate: ModuleCert) -> ModuleCert {
    let encoded = encode_module_cert(&certificate).unwrap();
    let payload = &encoded[..encoded.len() - 32];
    let mut parts = certificate.into_parts();
    parts.hashes.certificate_hash = hash_with_domain(b"NPA-MODULE-CERT-0.4.0", payload);
    ModuleCert::from_parts(parts)
}

fn build_v0_4(module: CoreModule) -> ModuleCert {
    build_module_cert(module, &[]).unwrap()
}

fn encode_uvar(mut value: usize) -> Vec<u8> {
    let mut bytes = Vec::new();
    loop {
        let byte = (value & 0x7f) as u8;
        value >>= 7;
        if value == 0 {
            bytes.push(byte);
            return bytes;
        }
        bytes.push(byte | 0x80);
    }
}

fn local_implementation_bytes(certificate: &ModuleCert, declaration_index: usize) -> Vec<u8> {
    let dependency = certificate.declarations()[declaration_index]
        .dependencies
        .iter()
        .find(|dependency| dependency.kind() == DependencyEntryKind::LocalImplementation)
        .unwrap();
    let npa_cert::GlobalRef::Local { decl_index } = dependency.global_ref() else {
        unreachable!()
    };
    let mut bytes = vec![0x01, 0x01];
    bytes.extend(encode_uvar(*decl_index));
    bytes.extend(dependency.decl_interface_hash());
    bytes.extend(dependency.decl_certificate_hash().unwrap());
    bytes
}

fn unique_offset(haystack: &[u8], needle: &[u8]) -> usize {
    let offsets = haystack
        .windows(needle.len())
        .enumerate()
        .filter_map(|(offset, window)| (window == needle).then_some(offset))
        .collect::<Vec<_>>();
    assert_eq!(offsets.len(), 1, "fixture mutation material must be unique");
    offsets[0]
}

fn rehash_v0_4_alias_dependency(
    mut bytes: Vec<u8>,
    certificate: &ModuleCert,
    declaration_index: usize,
    old_dependency: &[u8],
    new_dependency: &[u8],
) -> Vec<u8> {
    assert_eq!(old_dependency.len(), new_dependency.len());
    let dependency_offset = unique_offset(&bytes, old_dependency);
    bytes[dependency_offset..dependency_offset + new_dependency.len()]
        .copy_from_slice(new_dependency);

    let declaration = &certificate.declarations()[declaration_index];
    let mut declaration_payload = Vec::new();
    declaration_payload.extend(declaration.hashes.decl_interface_hash);
    match declaration.decl {
        DeclPayload::Def { value, .. } | DeclPayload::DefConstrained { value, .. } => {
            declaration_payload.extend(term_hash(certificate, value).unwrap());
            declaration_payload.extend(encode_uvar(1));
            declaration_payload.extend(new_dependency);
            declaration_payload.push(0x00);
        }
        DeclPayload::Theorem { proof, .. } | DeclPayload::TheoremConstrained { proof, .. } => {
            declaration_payload.extend(term_hash(certificate, proof).unwrap());
            declaration_payload.extend(encode_uvar(1));
            declaration_payload.extend(new_dependency);
        }
        _ => unreachable!(),
    }
    let new_declaration_hash = hash_with_domain(b"NPA-DECL-CERT-0.4.0", &declaration_payload);
    let old_declaration_hash = declaration.hashes.decl_certificate_hash;
    let declaration_hash_offset = unique_offset(&bytes, &old_declaration_hash);
    bytes[declaration_hash_offset..declaration_hash_offset + 32]
        .copy_from_slice(&new_declaration_hash);

    let certificate_hash_offset = bytes.len() - 32;
    let new_certificate_hash =
        hash_with_domain(b"NPA-MODULE-CERT-0.4.0", &bytes[..certificate_hash_offset]);
    bytes[certificate_hash_offset..].copy_from_slice(&new_certificate_hash);
    bytes
}

fn write_v0_4_fixtures(output: &ClosedPrivateDirectory) -> Result<(), String> {
    let direct = build_v0_4(opaque_direct_module());
    let direct_bytes = encode_module_cert(&direct).unwrap();
    assert!(verify_module_cert(
        &direct_bytes,
        &mut VerifierSession::new(),
        &AxiomPolicy::normal()
    )
    .is_ok());
    write_output(output, "opaque-direct-v0.4.npcert", &direct_bytes)?;

    let alias_chain = build_v0_4(opaque_alias_chain_module());
    let alias_chain_bytes = encode_module_cert(&alias_chain).unwrap();
    assert!(verify_module_cert(
        &alias_chain_bytes,
        &mut VerifierSession::new(),
        &AxiomPolicy::normal()
    )
    .is_ok());
    write_output(output, "opaque-alias-chain-v0.4.npcert", &alias_chain_bytes)?;
    let alias = build_v0_4(opaque_alias_module());
    let alias_bytes = encode_module_cert(&alias).unwrap();
    let declaration_index = 1;
    let old_dependency = local_implementation_bytes(&alias, declaration_index);

    let invalid_base = build_v0_4(invalid_target_base_module());
    let invalid_bytes = encode_module_cert(&invalid_base).unwrap();
    let invalid_declaration_index = 2;
    let invalid_old_dependency =
        local_implementation_bytes(&invalid_base, invalid_declaration_index);
    let mut invalid_target = invalid_old_dependency.clone();
    invalid_target[2] = 0;
    let invalid_target_bytes = rehash_v0_4_alias_dependency(
        invalid_bytes,
        &invalid_base,
        invalid_declaration_index,
        &invalid_old_dependency,
        &invalid_target,
    );
    assert!(matches!(
        verify_module_cert(
            &invalid_target_bytes,
            &mut VerifierSession::new(),
            &AxiomPolicy::normal()
        ),
        Err(CertError::InvalidLocalImplementationDependency {
            reason: LocalImplementationDependencyErrorReason::TargetNotOpaque,
            ..
        })
    ));
    write_output(output, "invalid-target-v0.4.npcert", &invalid_target_bytes)?;

    let mut stale_hash = old_dependency.clone();
    let last = stale_hash.len() - 1;
    stale_hash[last] ^= 1;
    let stale_hash_bytes = rehash_v0_4_alias_dependency(
        alias_bytes,
        &alias,
        declaration_index,
        &old_dependency,
        &stale_hash,
    );
    assert!(matches!(
        verify_module_cert(
            &stale_hash_bytes,
            &mut VerifierSession::new(),
            &AxiomPolicy::normal()
        ),
        Err(CertError::InvalidLocalImplementationDependency {
            reason: LocalImplementationDependencyErrorReason::CertificateHashMismatch,
            ..
        })
    ));
    write_output(
        output,
        "stale-implementation-hash-v0.4.npcert",
        &stale_hash_bytes,
    )?;

    let forbidden = build_v0_4(forbidden_axiom_module());
    let forbidden_bytes = encode_module_cert(&forbidden).unwrap();
    assert!(matches!(
        verify_module_cert(
            &forbidden_bytes,
            &mut VerifierSession::new(),
            &AxiomPolicy::high_trust()
        ),
        Err(CertError::ForbiddenAxiom { .. })
    ));
    write_output(output, "forbidden-axiom-v0.4.npcert", &forbidden_bytes)?;
    Ok(())
}

fn semantically_invalid_provider(certificate: ModuleCert) -> ModuleCert {
    let bvar_zero = certificate
        .term_table()
        .iter()
        .position(|term| matches!(term, TermNode::BVar(0)))
        .unwrap();
    let bvar_one = certificate
        .term_table()
        .iter()
        .position(|term| matches!(term, TermNode::BVar(1)))
        .unwrap();
    let inner_lambda = certificate
        .term_table()
        .iter()
        .position(|term| {
            matches!(
                term,
                TermNode::Lam { ty, body } if *ty == bvar_zero && *body == bvar_zero
            )
        })
        .unwrap();
    let mut parts = certificate.into_parts();
    match &mut parts.term_table[inner_lambda] {
        TermNode::Lam { body, .. } => *body = bvar_one,
        _ => unreachable!(),
    }
    let certificate = ModuleCert::from_parts(parts);
    let proof = match certificate.declarations()[0].decl {
        DeclPayload::Theorem { proof, .. } => proof,
        _ => unreachable!(),
    };
    let mut payload = Vec::new();
    payload.extend(certificate.declarations()[0].hashes.decl_interface_hash);
    payload.extend(term_hash(&certificate, proof).unwrap());
    payload.push(0);
    let mut parts = certificate.into_parts();
    parts.declarations[0].hashes.decl_certificate_hash =
        hash_with_domain(b"NPA-DECL-CERT-0.4.0", &payload);
    recompute_module_certificate_hash(ModuleCert::from_parts(parts))
}

fn write_unchecked_import_fixtures(output: &ClosedPrivateDirectory) -> Result<(), String> {
    let good_certificate = build_module_cert(unchecked_provider_module(), &[]).unwrap();
    let good_bytes = encode_module_cert(&good_certificate).unwrap();
    let mut verifier = VerifierSession::new();
    let verified_provider =
        verify_module_cert(&good_bytes, &mut verifier, &AxiomPolicy::normal()).unwrap();
    let bad_certificate = semantically_invalid_provider(good_certificate);

    let dependency_hash_mismatch = build_module_cert(
        unchecked_consumer_module(),
        std::slice::from_ref(&verified_provider),
    )
    .unwrap();
    let dependency_hash =
        dependency_hash_mismatch.declarations()[0].dependencies[0].decl_interface_hash();
    let mut dependency_hash_mismatch_bytes = encode_module_cert(&dependency_hash_mismatch).unwrap();
    let mut duplicated_hashes = Vec::with_capacity(dependency_hash.len() * 2);
    duplicated_hashes.extend(dependency_hash);
    duplicated_hashes.extend(dependency_hash);
    let dependency_hash_offset = dependency_hash_mismatch_bytes
        .windows(duplicated_hashes.len())
        .position(|window| window == duplicated_hashes)
        .expect("imported dependency must encode its interface hash twice")
        + dependency_hash.len();
    dependency_hash_mismatch_bytes[dependency_hash_offset] ^= 1;
    let unpinned_consumer =
        build_module_cert(unchecked_consumer_module(), &[verified_provider]).unwrap();
    let mut parts = unpinned_consumer.into_parts();
    parts.imports[0].certificate_hash = None;
    let unpinned_consumer = recompute_module_certificate_hash(ModuleCert::from_parts(parts));
    let mut parts = unpinned_consumer.clone().into_parts();
    parts.imports[0].certificate_hash = Some(bad_certificate.hashes().certificate_hash);
    let pinned_consumer = recompute_module_certificate_hash(ModuleCert::from_parts(parts));

    write_output(
        output,
        "dependency-hash-mismatch-v0.4.npcert",
        &dependency_hash_mismatch_bytes,
    )?;
    write_output(
        output,
        "unchecked-provider-bad-v0.4.npcert",
        &encode_module_cert(&bad_certificate).unwrap(),
    )?;
    write_output(
        output,
        "unchecked-consumer-unpinned-v0.4.npcert",
        &encode_module_cert(&unpinned_consumer).unwrap(),
    )?;
    write_output(
        output,
        "unchecked-consumer-pinned-v0.4.npcert",
        &encode_module_cert(&pinned_consumer).unwrap(),
    )?;
    Ok(())
}

fn write_fixture(
    output: &ClosedPrivateDirectory,
    file_name: &str,
    module: CoreModule,
) -> Result<(), String> {
    let certificate = build_module_cert(module, &[]).unwrap();
    let bytes = encode_module_cert(&certificate).unwrap();
    write_output(output, file_name, &bytes)
}

fn write_noncanonical_identity_fixture(output: &ClosedPrivateDirectory) -> Result<(), String> {
    let certificate = build_module_cert(
        CoreModule {
            name: Name::from_dotted("Conformance.PartialIdentity"),
            declarations: Vec::new(),
        },
        &[],
    )
    .unwrap();
    let unused_name = Name::from_dotted("zzzzUnusedDiagnosticName");
    assert!(certificate
        .name_table()
        .last()
        .is_none_or(|last| last < &unused_name));
    let mut parts = certificate.into_parts();
    parts.name_table.push(unused_name);
    let certificate = recompute_module_certificate_hash(ModuleCert::from_parts(parts));
    write_output(
        output,
        "noncanonical-unused-name-v0.4.npcert",
        &encode_module_cert(&certificate).unwrap(),
    )
}

fn write_indexed_imported_iota_fixtures(output: &ClosedPrivateDirectory) -> Result<(), String> {
    let indexed_certificate = build_module_cert(indexed_module(), &[]).unwrap();
    let indexed_bytes = encode_module_cert(&indexed_certificate).unwrap();
    let mut verifier = VerifierSession::new();
    let indexed_verified =
        verify_module_cert(&indexed_bytes, &mut verifier, &AxiomPolicy::normal()).unwrap();
    let consumer = build_module_cert(imported_vec_iota_module(), &[indexed_verified]).unwrap();

    write_output(output, "indexed-v0.4.npcert", &indexed_bytes)?;
    write_output(
        output,
        "imported-indexed-iota-v0.4.npcert",
        &encode_module_cert(&consumer).unwrap(),
    )?;
    Ok(())
}

fn write_mutual_imported_iota_fixtures(output: &ClosedPrivateDirectory) -> Result<(), String> {
    let mutual_certificate = build_module_cert(mutual_module(), &[]).unwrap();
    let mutual_bytes = encode_module_cert(&mutual_certificate).unwrap();
    let mut verifier = VerifierSession::new();
    let mutual_verified =
        verify_module_cert(&mutual_bytes, &mut verifier, &AxiomPolicy::normal()).unwrap();
    let consumer = build_module_cert(imported_mutual_iota_module(), &[mutual_verified]).unwrap();

    write_output(output, "mutual-v0.4.npcert", &mutual_bytes)?;
    write_output(
        output,
        "imported-mutual-iota-v0.4.npcert",
        &encode_module_cert(&consumer).unwrap(),
    )?;
    Ok(())
}

fn generate(output: &Path) -> Result<(), String> {
    let output_parent = output
        .parent()
        .filter(|path| !path.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."))
        .canonicalize()
        .map_err(|error| format!("output parent must be an existing real directory: {error}"))?;
    let requested_name = output
        .file_name()
        .ok_or_else(|| "output directory must have a basename".to_owned())?;
    let canonical_output = output_parent.join(requested_name);
    if !output.components().all(|component| {
        matches!(
            component,
            std::path::Component::RootDir
                | std::path::Component::CurDir
                | std::path::Component::Normal(_)
        )
    }) {
        return Err("output directory path must be normalized".to_owned());
    }
    let staging = ClosedPrivateDirectory::new_in(&output_parent, "npa-ext-conformance")?;
    let populate = (|| {
        write_indexed_imported_iota_fixtures(&staging)?;
        write_mutual_imported_iota_fixtures(&staging)?;
        write_fixture(&staging, "nested-v0.4.npcert", nested_module())?;
        write_fixture(&staging, "nested-all-v0.4.npcert", nested_all_module())?;
        write_noncanonical_identity_fixture(&staging)?;
        write_unchecked_import_fixtures(&staging)?;
        write_v0_4_fixtures(&staging)
    })();
    if let Err(error) = populate {
        let cleanup = staging.capture_cleanup_catalog().map_err(|cleanup_error| {
            format!("{error}; cannot capture failed generation cleanup: {cleanup_error}")
        })?;
        staging
            .remove_captured_root(&cleanup)
            .map_err(|cleanup_error| {
                format!("{error}; cannot clean failed generation: {cleanup_error}")
            })?;
        return Err(error);
    }
    let cleanup = staging.capture_cleanup_catalog()?;
    match staging.publish_new_root(&canonical_output, "external conformance fixture directory") {
        Ok(()) => Ok(()),
        Err(error) => {
            staging
                .remove_captured_root(&cleanup)
                .map_err(|cleanup_error| {
                    format!("{error}; cannot clean unpublished fixtures: {cleanup_error}")
                })?;
            Err(error)
        }
    }
}

fn main() {
    if let Err(error) = run() {
        eprintln!("generate-ext-conformance: {error}");
        std::process::exit(2);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn publication_collision_preserves_output_and_cleans_private_staging() {
        let parent = ClosedPrivateDirectory::new("npa-ext-conformance-test").unwrap();
        let output = parent.path().join("fixtures");
        generate(&output).unwrap();
        let committed: [(&str, &[u8]); 16] = [
            (
                "dependency-hash-mismatch-v0.4.npcert",
                include_bytes!(
                    "../../../checkers/npa-checker-ext/test/fixtures/conformance/dependency-hash-mismatch-v0.4.npcert"
                ),
            ),
            (
                "forbidden-axiom-v0.4.npcert",
                include_bytes!(
                    "../../../checkers/npa-checker-ext/test/fixtures/conformance/forbidden-axiom-v0.4.npcert"
                ),
            ),
            (
                "imported-indexed-iota-v0.4.npcert",
                include_bytes!(
                    "../../../checkers/npa-checker-ext/test/fixtures/conformance/imported-indexed-iota-v0.4.npcert"
                ),
            ),
            (
                "imported-mutual-iota-v0.4.npcert",
                include_bytes!(
                    "../../../checkers/npa-checker-ext/test/fixtures/conformance/imported-mutual-iota-v0.4.npcert"
                ),
            ),
            (
                "indexed-v0.4.npcert",
                include_bytes!(
                    "../../../checkers/npa-checker-ext/test/fixtures/conformance/indexed-v0.4.npcert"
                ),
            ),
            (
                "invalid-target-v0.4.npcert",
                include_bytes!(
                    "../../../checkers/npa-checker-ext/test/fixtures/conformance/invalid-target-v0.4.npcert"
                ),
            ),
            (
                "mutual-v0.4.npcert",
                include_bytes!(
                    "../../../checkers/npa-checker-ext/test/fixtures/conformance/mutual-v0.4.npcert"
                ),
            ),
            (
                "nested-all-v0.4.npcert",
                include_bytes!(
                    "../../../checkers/npa-checker-ext/test/fixtures/conformance/nested-all-v0.4.npcert"
                ),
            ),
            (
                "nested-v0.4.npcert",
                include_bytes!(
                    "../../../checkers/npa-checker-ext/test/fixtures/conformance/nested-v0.4.npcert"
                ),
            ),
            (
                "noncanonical-unused-name-v0.4.npcert",
                include_bytes!(
                    "../../../checkers/npa-checker-ext/test/fixtures/conformance/noncanonical-unused-name-v0.4.npcert"
                ),
            ),
            (
                "opaque-alias-chain-v0.4.npcert",
                include_bytes!(
                    "../../../checkers/npa-checker-ext/test/fixtures/conformance/opaque-alias-chain-v0.4.npcert"
                ),
            ),
            (
                "opaque-direct-v0.4.npcert",
                include_bytes!(
                    "../../../checkers/npa-checker-ext/test/fixtures/conformance/opaque-direct-v0.4.npcert"
                ),
            ),
            (
                "stale-implementation-hash-v0.4.npcert",
                include_bytes!(
                    "../../../checkers/npa-checker-ext/test/fixtures/conformance/stale-implementation-hash-v0.4.npcert"
                ),
            ),
            (
                "unchecked-consumer-pinned-v0.4.npcert",
                include_bytes!(
                    "../../../checkers/npa-checker-ext/test/fixtures/conformance/unchecked-consumer-pinned-v0.4.npcert"
                ),
            ),
            (
                "unchecked-consumer-unpinned-v0.4.npcert",
                include_bytes!(
                    "../../../checkers/npa-checker-ext/test/fixtures/conformance/unchecked-consumer-unpinned-v0.4.npcert"
                ),
            ),
            (
                "unchecked-provider-bad-v0.4.npcert",
                include_bytes!(
                    "../../../checkers/npa-checker-ext/test/fixtures/conformance/unchecked-provider-bad-v0.4.npcert"
                ),
            ),
        ];
        for (file_name, expected) in committed {
            let generated = parent
                .read_regular_file(&Path::new("fixtures").join(file_name), 64 * 1024 * 1024)
                .unwrap();
            assert_eq!(generated, expected, "generated fixture drift: {file_name}");
        }
        let before_paths = parent.catalog_root_paths().unwrap();
        let before_bytes = parent
            .read_regular_file(Path::new("fixtures/opaque-direct-v0.4.npcert"), 1024 * 1024)
            .unwrap();
        let cleanup = parent.capture_cleanup_catalog().unwrap();

        assert!(generate(&output).is_err());
        assert_eq!(parent.catalog_root_paths().unwrap(), before_paths);
        assert_eq!(
            parent
                .read_regular_file(Path::new("fixtures/opaque-direct-v0.4.npcert"), 1024 * 1024,)
                .unwrap(),
            before_bytes
        );

        parent.remove_captured_root(&cleanup).unwrap();
    }
}

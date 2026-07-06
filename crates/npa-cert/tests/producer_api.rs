use npa_cert::{
    build_module_cert, build_module_cert_from_checked_candidates, canonical_import_env_keys,
    canonical_import_export_views, check_core_decl_candidates, encode_module_cert,
    initial_env_fingerprint, post_env_fingerprint, precheck_core_decl_candidate,
    prior_chain_fingerprint, prior_chain_fingerprint_canonical_bytes,
    producer_checked_decl_interface, producer_env_fingerprint,
    producer_env_fingerprint_canonical_bytes, producer_import_env_key,
    producer_limits_canonical_bytes, producer_limits_hash, producer_lookup_env, stricter_or_equal,
    validate_candidate_batch_imports, validate_prior_current_decls, verify_module_cert,
    AxiomPolicy, AxiomRef, CandidateBatch, CandidateBatchResult, CandidateHashPreview,
    CandidateStatus, CertError, CheckedDeclCandidate, CoreDeclCandidate, CoreModule, GlobalRef,
    ModuleCert, Name, ProducerCheckedDeclInterface, ProducerEnvFingerprintBytes,
    ProducerImportEnvKey, ProducerLimitKind, ProducerLimits, ProducerPriorChainBytes,
    ProducerPriorChainEntry, ProducerProfile, ProducerTokenHashField, VerifiedModule,
    VerifierSession,
};
use npa_kernel::{Decl, Env, Error as KernelError, Expr, Level, Reducibility, ResourceLimitKind};

fn trivial_axiom(name: &str) -> Decl {
    Decl::Axiom {
        name: name.to_owned(),
        universe_params: vec![],
        ty: Expr::sort(Level::zero()),
    }
}

fn generous_limits() -> ProducerLimits {
    ProducerLimits {
        max_declarations: 1,
        max_expr_nodes: 64,
        max_level_nodes: 64,
        max_name_components: 8,
        max_reduction_steps: 64,
        max_conversion_steps: 64,
    }
}

fn generous_limits_with_declarations(max_declarations: u32) -> ProducerLimits {
    ProducerLimits {
        max_declarations,
        ..generous_limits()
    }
}

fn hash(byte: u8) -> [u8; 32] {
    [byte; 32]
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct TestProducerSidecar {
    module: Name,
    producer_profile: ProducerProfile,
    producer_run_id: String,
    model_name: String,
    prompt: String,
    score: i32,
    diagnostics: Vec<String>,
    cache_hit: bool,
    input_artifact_hashes: Vec<[u8; 32]>,
}

impl TestProducerSidecar {
    fn human(module: &str) -> Self {
        Self {
            module: Name::from_dotted(module),
            producer_profile: ProducerProfile::HumanSurface,
            producer_run_id: "human-run-1".to_owned(),
            model_name: "surface-elaborator".to_owned(),
            prompt: "human surface source".to_owned(),
            score: 100,
            diagnostics: vec!["accepted by human producer".to_owned()],
            cache_hit: false,
            input_artifact_hashes: vec![hash(0x11)],
        }
    }

    fn ai(module: &str) -> Self {
        Self {
            module: Name::from_dotted(module),
            producer_profile: ProducerProfile::AiCoreMvp,
            producer_run_id: "ai-run-1".to_owned(),
            model_name: "proof-candidate-model".to_owned(),
            prompt: "generate checked core declarations".to_owned(),
            score: 80,
            diagnostics: vec!["accepted by AI producer".to_owned()],
            cache_hit: true,
            input_artifact_hashes: vec![hash(0x22)],
        }
    }

    fn marker(&self) -> String {
        let input_artifact_marker = self
            .input_artifact_hashes
            .iter()
            .flatten()
            .map(|byte| u32::from(*byte))
            .sum::<u32>();
        format!(
            "{}|{:?}|{}|{}|{}|{}|{}|{}|{}",
            self.module.as_dotted(),
            self.producer_profile,
            self.producer_run_id,
            self.model_name,
            self.prompt,
            self.score,
            self.diagnostics.join(";"),
            self.cache_hit,
            input_artifact_marker
        )
    }
}

fn verify_module(module: CoreModule) -> VerifiedModule {
    let cert = build_module_cert(module, &[]).unwrap();
    let bytes = encode_module_cert(&cert).unwrap();
    let mut session = VerifierSession::new();
    verify_module_cert(&bytes, &mut session, &AxiomPolicy::normal()).unwrap()
}

fn build_bytes_and_hashes_with_out_of_band_sidecar(
    module: CoreModule,
    sidecar: Option<&TestProducerSidecar>,
) -> (Vec<u8>, [u8; 32], [u8; 32], [u8; 32]) {
    if let Some(sidecar) = sidecar {
        assert_eq!(&sidecar.module, &module.name);
        assert!(!sidecar.marker().is_empty());
    }
    let cert = build_module_cert(module, &[]).unwrap();
    let bytes = encode_module_cert(&cert).unwrap();
    (
        bytes,
        cert.hashes.export_hash,
        cert.hashes.axiom_report_hash,
        cert.hashes.certificate_hash,
    )
}

fn verify_module_with_imports(module: CoreModule, imports: &[VerifiedModule]) -> VerifiedModule {
    let cert = build_module_cert(module, imports).unwrap();
    let bytes = encode_module_cert(&cert).unwrap();
    let mut session = VerifierSession::new();
    for import in imports {
        session.register_verified_module(import.clone());
    }
    verify_module_cert(&bytes, &mut session, &AxiomPolicy::normal()).unwrap()
}

fn producer_env(
    direct_imports: Vec<ProducerImportEnvKey>,
    checked_decls: Vec<ProducerCheckedDeclInterface>,
) -> ProducerEnvFingerprintBytes {
    ProducerEnvFingerprintBytes {
        direct_imports,
        checked_decls,
    }
}

fn checked_decl_interface(byte: u8) -> ProducerCheckedDeclInterface {
    ProducerCheckedDeclInterface {
        decl_interface_hash: hash(byte),
        axiom_dependencies: vec![],
    }
}

fn local_axiom_ref(decl_index: usize, name: usize, byte: u8) -> AxiomRef {
    AxiomRef {
        global_ref: GlobalRef::Local { decl_index },
        name,
        decl_interface_hash: hash(byte),
    }
}

fn empty_batch(imports: &[VerifiedModule]) -> CandidateBatch<'_> {
    CandidateBatch {
        imports,
        prior_current_decls: &[],
        candidates: vec![],
        limits: generous_limits(),
    }
}

fn axiom_module(module_name: &str, decl_name: &str) -> CoreModule {
    CoreModule {
        name: Name::from_dotted(module_name),
        declarations: vec![trivial_axiom(decl_name)],
    }
}

fn sort_axiom_module(module_name: &str, decl_name: &str, level: Level) -> CoreModule {
    CoreModule {
        name: Name::from_dotted(module_name),
        declarations: vec![Decl::Axiom {
            name: decl_name.to_owned(),
            universe_params: vec![],
            ty: Expr::sort(level),
        }],
    }
}

fn opaque_def_module(module_name: &str, value: Expr) -> CoreModule {
    CoreModule {
        name: Name::from_dotted(module_name),
        declarations: vec![Decl::Def {
            name: "carrier".to_owned(),
            universe_params: vec![],
            ty: Expr::sort(Level::succ(Level::zero())),
            value,
            reducibility: Reducibility::Opaque,
        }],
    }
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

fn id_theorem_module(module_name: &str, proof: Expr) -> CoreModule {
    CoreModule {
        name: Name::from_dotted(module_name),
        declarations: vec![Decl::Theorem {
            name: "id_thm".to_owned(),
            universe_params: vec!["u".to_owned()],
            ty: id_type("A", "x"),
            proof,
        }],
    }
}

fn imported_theorem(name: &str, imported_name: &str) -> Decl {
    Decl::Theorem {
        name: name.to_owned(),
        universe_params: vec![],
        ty: Expr::konst(imported_name, vec![]),
        proof: Expr::konst(imported_name, vec![]),
    }
}

fn axiom_over(name: &str, ty_name: &str) -> Decl {
    Decl::Axiom {
        name: name.to_owned(),
        universe_params: vec![],
        ty: Expr::konst(ty_name, vec![]),
    }
}

fn accepted_tokens(result: CandidateBatchResult) -> Vec<CheckedDeclCandidate> {
    result
        .statuses
        .into_iter()
        .map(|status| match status {
            CandidateStatus::Accepted(token) => token,
            CandidateStatus::Rejected(err) => panic!("unexpected rejection: {err:?}"),
        })
        .collect()
}

fn prior_entry(
    decl_interface_hash: [u8; 32],
    decl_certificate_hash: [u8; 32],
    pre_env_fingerprint: [u8; 32],
    post_env_fingerprint: [u8; 32],
) -> ProducerPriorChainEntry {
    ProducerPriorChainEntry {
        decl_interface_hash,
        decl_certificate_hash,
        pre_env_fingerprint,
        post_env_fingerprint,
    }
}

#[test]
fn producer_types_are_available_from_public_api() {
    let limits = ProducerLimits {
        max_declarations: 1,
        max_expr_nodes: 8,
        max_level_nodes: 2,
        max_name_components: 4,
        max_reduction_steps: 16,
        max_conversion_steps: 16,
    };
    let candidate = CoreDeclCandidate {
        declaration: trivial_axiom("P"),
    };
    let imports: &[VerifiedModule] = &[];
    let prior: &[CheckedDeclCandidate] = &[];

    let batch = CandidateBatch {
        imports,
        prior_current_decls: prior,
        candidates: vec![candidate],
        limits,
    };

    assert_eq!(batch.imports.len(), 0);
    assert_eq!(batch.prior_current_decls.len(), 0);
    assert_eq!(batch.candidates.len(), 1);
    assert_eq!(batch.limits, limits);

    let preview = CandidateHashPreview {
        type_hash: None,
        body_hash: None,
        decl_interface_hash: None,
        decl_certificate_hash: None,
    };
    assert_eq!(preview.type_hash, None);

    let result = CandidateBatchResult {
        statuses: vec![CandidateStatus::Rejected(CertError::DecodeError)],
    };
    assert!(matches!(
        result.statuses.as_slice(),
        [CandidateStatus::Rejected(CertError::DecodeError)]
    ));
}

#[test]
fn public_certificate_api_signatures_exclude_producer_profile() {
    let _: fn(CoreModule, &[VerifiedModule]) -> npa_cert::Result<ModuleCert> = build_module_cert;
    let _: fn(&[u8], &mut VerifierSession, &AxiomPolicy) -> npa_cert::Result<VerifiedModule> =
        verify_module_cert;
    let _: fn(CandidateBatch<'_>) -> npa_cert::Result<CandidateBatchResult> =
        check_core_decl_candidates;
    let sidecar_only = ProducerProfile::AiCoreMvp;

    assert_eq!(sidecar_only, ProducerProfile::AiCoreMvp);
}

#[test]
fn validate_prior_current_decls_public_api_accepts_empty_prior_chain() {
    let imports: &[VerifiedModule] = &[];
    let batch = empty_batch(imports);

    assert_eq!(
        validate_prior_current_decls(&batch).unwrap(),
        Vec::<ProducerCheckedDeclInterface>::new()
    );
}

#[test]
fn check_core_decl_candidates_accepts_in_input_order_and_extends_local_environment() {
    let type_decl = trivial_axiom("LocalA");
    let value_decl = axiom_over("local_a", "LocalA");
    let batch = CandidateBatch {
        imports: &[],
        prior_current_decls: &[],
        candidates: vec![
            CoreDeclCandidate {
                declaration: type_decl.clone(),
            },
            CoreDeclCandidate {
                declaration: value_decl.clone(),
            },
        ],
        limits: generous_limits_with_declarations(2),
    };

    let result = check_core_decl_candidates(batch).unwrap();
    assert_eq!(result.statuses.len(), 2);
    let [CandidateStatus::Accepted(type_token), CandidateStatus::Accepted(value_token)] =
        result.statuses.as_slice()
    else {
        panic!("expected both candidates to be accepted");
    };

    let cert = build_module_cert(
        CoreModule {
            name: Name::from_dotted("Producer.Local"),
            declarations: vec![type_decl, value_decl],
        },
        &[],
    )
    .unwrap();
    assert_eq!(
        type_token.decl_interface_hash(),
        cert.declarations[0].hashes.decl_interface_hash
    );
    assert_eq!(
        value_token.decl_interface_hash(),
        cert.declarations[1].hashes.decl_interface_hash
    );
    assert_eq!(
        type_token.pre_env_fingerprint(),
        initial_env_fingerprint(&[]).unwrap()
    );
    assert_eq!(
        value_token.pre_env_fingerprint(),
        type_token.post_env_fingerprint()
    );
    assert_eq!(
        type_token.prior_chain_fingerprint(),
        prior_chain_fingerprint(&ProducerPriorChainBytes {
            checked_decls: vec![]
        })
    );
    assert_eq!(
        value_token.prior_chain_fingerprint(),
        prior_chain_fingerprint(&ProducerPriorChainBytes {
            checked_decls: vec![prior_entry(
                type_token.decl_interface_hash(),
                type_token.decl_certificate_hash(),
                type_token.pre_env_fingerprint(),
                type_token.post_env_fingerprint(),
            )]
        })
    );
    assert!(type_token.limit_profile_hash_matches());
    assert_eq!(
        type_token.preview_hashes().decl_interface_hash,
        Some(type_token.decl_interface_hash())
    );
}

#[test]
fn check_core_decl_candidates_accepts_import_and_builtin_references() {
    let import = verify_module(axiom_module("Lib.FastPathImport", "FastPathImported"));
    let imports = [import.clone()];
    let imported_decl = axiom_over("UsesFastPathImport", "FastPathImported");
    let import_batch = CandidateBatch {
        imports: &imports,
        prior_current_decls: &[],
        candidates: vec![CoreDeclCandidate {
            declaration: imported_decl.clone(),
        }],
        limits: generous_limits(),
    };

    let imported_tokens = accepted_tokens(check_core_decl_candidates(import_batch).unwrap());
    let imported_cert = build_module_cert(
        CoreModule {
            name: Name::from_dotted("Producer.Imported"),
            declarations: vec![imported_decl],
        },
        &imports,
    )
    .unwrap();
    assert_eq!(
        imported_tokens[0].decl_interface_hash(),
        imported_cert.declarations[0].hashes.decl_interface_hash
    );

    let builtin_decl = Decl::Theorem {
        name: "zero_is_nat".to_owned(),
        universe_params: vec![],
        ty: Expr::konst("Nat", vec![]),
        proof: Expr::konst("Nat.zero", vec![]),
    };
    let builtin_batch = CandidateBatch {
        imports: &[],
        prior_current_decls: &[],
        candidates: vec![CoreDeclCandidate {
            declaration: builtin_decl,
        }],
        limits: generous_limits(),
    };
    let builtin_tokens = accepted_tokens(check_core_decl_candidates(builtin_batch).unwrap());
    assert!(builtin_tokens[0].limit_profile_hash_matches());
}

#[test]
fn check_core_decl_candidates_rejects_pretty_only_import_name() {
    let import = verify_module(axiom_module("Lib.PrettyOnly", "PrettyOnlyType"));
    let imports = [import];
    let batch = CandidateBatch {
        imports: &imports,
        prior_current_decls: &[],
        candidates: vec![CoreDeclCandidate {
            declaration: axiom_over("UsesPrettyOnly", "Lib.PrettyOnly.PrettyOnlyType"),
        }],
        limits: generous_limits(),
    };

    let result = check_core_decl_candidates(batch).unwrap();
    assert_eq!(result.statuses.len(), 1);
    assert!(matches!(
        &result.statuses[0],
        CandidateStatus::Rejected(CertError::UnknownDependency { name })
            if *name == Name::from_dotted("Lib.PrettyOnly.PrettyOnlyType")
    ));
}

#[test]
fn check_core_decl_candidates_rejects_placeholder_like_ai_candidates() {
    let batch = CandidateBatch {
        imports: &[],
        prior_current_decls: &[],
        candidates: vec![
            CoreDeclCandidate {
                declaration: axiom_over("UsesPlaceholderName", "_"),
            },
            CoreDeclCandidate {
                declaration: Decl::Axiom {
                    name: "FreeBVarPlaceholder".to_owned(),
                    universe_params: vec![],
                    ty: Expr::bvar(0),
                },
            },
            CoreDeclCandidate {
                declaration: Decl::Axiom {
                    name: "UnresolvedUniverseMetaLike".to_owned(),
                    universe_params: vec![],
                    ty: Expr::sort(Level::Param("?m".to_owned())),
                },
            },
        ],
        limits: generous_limits_with_declarations(3),
    };

    let result = check_core_decl_candidates(batch).unwrap();
    assert_eq!(result.statuses.len(), 3);
    assert!(matches!(
        &result.statuses[0],
        CandidateStatus::Rejected(CertError::UnknownDependency { name })
            if *name == Name::from_dotted("_")
    ));
    assert!(matches!(
        &result.statuses[1],
        CandidateStatus::Rejected(CertError::Kernel(KernelError::InvalidBVar(0)))
    ));
    assert!(matches!(
        &result.statuses[2],
        CandidateStatus::Rejected(CertError::NonCanonicalEncoding { object: "Name" })
    ));
}

#[test]
fn check_core_decl_candidates_hashes_depend_on_import_decl_interface_not_name_only() {
    let import_a = verify_module(sort_axiom_module("Lib.IfaceA", "IfaceT", Level::zero()));
    let import_b = verify_module(sort_axiom_module(
        "Lib.IfaceB",
        "IfaceT",
        Level::succ(Level::zero()),
    ));
    let decl = axiom_over("UsesIfaceT", "IfaceT");

    let tokens_a = accepted_tokens(
        check_core_decl_candidates(CandidateBatch {
            imports: std::slice::from_ref(&import_a),
            prior_current_decls: &[],
            candidates: vec![CoreDeclCandidate {
                declaration: decl.clone(),
            }],
            limits: generous_limits(),
        })
        .unwrap(),
    );
    let tokens_b = accepted_tokens(
        check_core_decl_candidates(CandidateBatch {
            imports: std::slice::from_ref(&import_b),
            prior_current_decls: &[],
            candidates: vec![CoreDeclCandidate {
                declaration: decl.clone(),
            }],
            limits: generous_limits(),
        })
        .unwrap(),
    );

    assert_ne!(
        tokens_a[0].decl_interface_hash(),
        tokens_b[0].decl_interface_hash()
    );
    assert_ne!(
        tokens_a[0].decl_certificate_hash(),
        tokens_b[0].decl_certificate_hash()
    );
    assert_eq!(
        tokens_a[0].preview_hashes().decl_interface_hash,
        Some(tokens_a[0].decl_interface_hash())
    );
    assert_eq!(
        tokens_a[0].preview_hashes().decl_certificate_hash,
        Some(tokens_a[0].decl_certificate_hash())
    );
    assert_eq!(
        tokens_b[0].preview_hashes().decl_interface_hash,
        Some(tokens_b[0].decl_interface_hash())
    );
    assert_eq!(
        tokens_b[0].preview_hashes().decl_certificate_hash,
        Some(tokens_b[0].decl_certificate_hash())
    );

    let lookup_a = producer_lookup_env(&[import_a], &[]).unwrap();
    let interface_a = producer_checked_decl_interface(&decl, &lookup_a).unwrap();
    let lookup_b = producer_lookup_env(&[import_b], &[]).unwrap();
    let interface_b = producer_checked_decl_interface(&decl, &lookup_b).unwrap();
    assert_eq!(
        tokens_a[0].decl_interface_hash(),
        interface_a.decl_interface_hash
    );
    assert_eq!(
        tokens_b[0].decl_interface_hash(),
        interface_b.decl_interface_hash
    );
}

#[test]
fn check_core_decl_candidates_rejects_import_decl_interface_hash_mismatch() {
    let original = verify_module(sort_axiom_module(
        "Lib.MismatchOriginal",
        "MismatchT",
        Level::zero(),
    ));
    let mismatched = verify_module(sort_axiom_module(
        "Lib.MismatchReplacement",
        "MismatchT",
        Level::succ(Level::zero()),
    ));
    let dependent = verify_module_with_imports(
        CoreModule {
            name: Name::from_dotted("Lib.MismatchUser"),
            declarations: vec![axiom_over("UsesOriginalMismatchT", "MismatchT")],
        },
        std::slice::from_ref(&original),
    );
    let imports = [mismatched, dependent];
    let batch = CandidateBatch {
        imports: &imports,
        prior_current_decls: &[],
        candidates: vec![CoreDeclCandidate {
            declaration: trivial_axiom("WillNotRun"),
        }],
        limits: generous_limits(),
    };

    assert!(matches!(
        check_core_decl_candidates(batch),
        Err(CertError::UnknownDependency { name })
            if name == Name::from_dotted("MismatchT")
    ));
}

#[test]
fn check_core_decl_candidates_rejects_ambiguous_import_name_instead_of_guessing() {
    let import_a = verify_module(sort_axiom_module(
        "Lib.AmbiguousA",
        "AmbiguousIfaceT",
        Level::zero(),
    ));
    let import_b = verify_module(sort_axiom_module(
        "Lib.AmbiguousB",
        "AmbiguousIfaceT",
        Level::succ(Level::zero()),
    ));
    let imports = [import_a, import_b];
    let batch = CandidateBatch {
        imports: &imports,
        prior_current_decls: &[],
        candidates: vec![CoreDeclCandidate {
            declaration: axiom_over("UsesAmbiguousIfaceT", "AmbiguousIfaceT"),
        }],
        limits: generous_limits(),
    };

    assert!(matches!(
        check_core_decl_candidates(batch),
        Err(CertError::Kernel(KernelError::DuplicateDecl(name)))
            if name == "AmbiguousIfaceT"
    ));
}

#[test]
fn check_core_decl_candidates_keeps_candidate_rejections_in_input_order() {
    let batch = CandidateBatch {
        imports: &[],
        prior_current_decls: &[],
        candidates: vec![
            CoreDeclCandidate {
                declaration: axiom_over("Bad", "MissingType"),
            },
            CoreDeclCandidate {
                declaration: trivial_axiom("Good"),
            },
        ],
        limits: generous_limits_with_declarations(2),
    };

    let result = check_core_decl_candidates(batch).unwrap();
    assert_eq!(result.statuses.len(), 2);
    assert!(matches!(
        &result.statuses[0],
        CandidateStatus::Rejected(CertError::UnknownDependency { name })
            if *name == Name::from_dotted("MissingType")
    ));
    assert!(matches!(&result.statuses[1], CandidateStatus::Accepted(_)));
}

#[test]
fn check_core_decl_candidates_rejections_do_not_perturb_later_accepted_tokens() {
    let bad = CoreDeclCandidate {
        declaration: axiom_over("BadMissing", "MissingType"),
    };
    let good = CoreDeclCandidate {
        declaration: trivial_axiom("StableAccepted"),
    };

    let bad_first = check_core_decl_candidates(CandidateBatch {
        imports: &[],
        prior_current_decls: &[],
        candidates: vec![bad.clone(), good.clone()],
        limits: generous_limits_with_declarations(2),
    })
    .unwrap();
    let good_first = check_core_decl_candidates(CandidateBatch {
        imports: &[],
        prior_current_decls: &[],
        candidates: vec![good, bad],
        limits: generous_limits_with_declarations(2),
    })
    .unwrap();

    assert!(matches!(
        &bad_first.statuses[0],
        CandidateStatus::Rejected(CertError::UnknownDependency { name })
            if *name == Name::from_dotted("MissingType")
    ));
    assert!(matches!(
        &good_first.statuses[1],
        CandidateStatus::Rejected(CertError::UnknownDependency { name })
            if *name == Name::from_dotted("MissingType")
    ));
    let CandidateStatus::Accepted(after_rejection) = &bad_first.statuses[1] else {
        panic!("expected accepted candidate after rejected candidate");
    };
    let CandidateStatus::Accepted(before_rejection) = &good_first.statuses[0] else {
        panic!("expected accepted candidate before rejected candidate");
    };
    assert_eq!(
        after_rejection.decl_interface_hash(),
        before_rejection.decl_interface_hash()
    );
    assert_eq!(
        after_rejection.decl_certificate_hash(),
        before_rejection.decl_certificate_hash()
    );
    assert_eq!(
        after_rejection.pre_env_fingerprint(),
        before_rejection.pre_env_fingerprint()
    );
    assert_eq!(
        after_rejection.post_env_fingerprint(),
        before_rejection.post_env_fingerprint()
    );
    assert_eq!(
        after_rejection.prior_chain_fingerprint(),
        before_rejection.prior_chain_fingerprint()
    );
}

#[test]
fn check_core_decl_candidates_reports_candidate_schema_limit_per_candidate() {
    let mut limits = generous_limits();
    limits.max_expr_nodes = 0;
    let batch = CandidateBatch {
        imports: &[],
        prior_current_decls: &[],
        candidates: vec![CoreDeclCandidate {
            declaration: trivial_axiom("TooLarge"),
        }],
        limits,
    };

    let result = check_core_decl_candidates(batch).unwrap();
    assert_eq!(result.statuses.len(), 1);
    assert_eq!(
        result.statuses[0],
        CandidateStatus::Rejected(CertError::ProducerLimitExceeded {
            limit: ProducerLimitKind::MaxExprNodes
        })
    );
}

#[test]
fn check_core_decl_candidates_reports_kernel_precheck_failure_per_candidate() {
    let batch = CandidateBatch {
        imports: &[],
        prior_current_decls: &[],
        candidates: vec![CoreDeclCandidate {
            declaration: Decl::Def {
                name: "bad_value".to_owned(),
                universe_params: vec![],
                ty: Expr::sort(Level::zero()),
                value: Expr::sort(Level::zero()),
                reducibility: Reducibility::Reducible,
            },
        }],
        limits: generous_limits(),
    };

    let result = check_core_decl_candidates(batch).unwrap();
    assert_eq!(result.statuses.len(), 1);
    assert!(matches!(
        &result.statuses[0],
        CandidateStatus::Rejected(CertError::Kernel(_))
    ));
}

#[test]
fn check_core_decl_candidates_rejects_batch_schema_before_statuses() {
    let batch = CandidateBatch {
        imports: &[],
        prior_current_decls: &[],
        candidates: vec![
            CoreDeclCandidate {
                declaration: trivial_axiom("First"),
            },
            CoreDeclCandidate {
                declaration: trivial_axiom("Second"),
            },
        ],
        limits: generous_limits(),
    };

    assert_eq!(
        check_core_decl_candidates(batch).unwrap_err(),
        CertError::ProducerLimitExceeded {
            limit: ProducerLimitKind::MaxDeclarations
        }
    );
}

#[test]
fn check_core_decl_candidates_rejects_noncanonical_imports_batch_level() {
    let import_a = verify_module(axiom_module("Lib.FastBatchA", "FastBatchA"));
    let import_b = verify_module(axiom_module("Lib.FastBatchB", "FastBatchB"));
    let reversed_imports = [import_b, import_a];
    let batch = CandidateBatch {
        imports: &reversed_imports,
        prior_current_decls: &[],
        candidates: vec![CoreDeclCandidate {
            declaration: trivial_axiom("WillNotRun"),
        }],
        limits: generous_limits(),
    };

    assert_eq!(
        check_core_decl_candidates(batch).unwrap_err(),
        CertError::NonCanonicalEncoding { object: "Imports" }
    );
}

#[test]
fn check_core_decl_candidates_reuses_prior_tokens_with_local_references() {
    let first_batch = CandidateBatch {
        imports: &[],
        prior_current_decls: &[],
        candidates: vec![
            CoreDeclCandidate {
                declaration: trivial_axiom("PriorA"),
            },
            CoreDeclCandidate {
                declaration: axiom_over("prior_a", "PriorA"),
            },
        ],
        limits: generous_limits_with_declarations(2),
    };
    let prior_tokens = accepted_tokens(check_core_decl_candidates(first_batch).unwrap());
    let prior = prior_tokens.clone();
    let second_batch = CandidateBatch {
        imports: &[],
        prior_current_decls: &prior,
        candidates: vec![CoreDeclCandidate {
            declaration: axiom_over("prior_b", "PriorA"),
        }],
        limits: generous_limits_with_declarations(3),
    };

    let result = check_core_decl_candidates(second_batch).unwrap();
    let [CandidateStatus::Accepted(token)] = result.statuses.as_slice() else {
        panic!("expected candidate after prior chain to be accepted");
    };
    assert_eq!(
        token.pre_env_fingerprint(),
        prior_tokens[1].post_env_fingerprint()
    );
    assert_eq!(
        token.prior_chain_fingerprint(),
        prior_chain_fingerprint(&ProducerPriorChainBytes {
            checked_decls: vec![
                prior_entry(
                    prior_tokens[0].decl_interface_hash(),
                    prior_tokens[0].decl_certificate_hash(),
                    prior_tokens[0].pre_env_fingerprint(),
                    prior_tokens[0].post_env_fingerprint(),
                ),
                prior_entry(
                    prior_tokens[1].decl_interface_hash(),
                    prior_tokens[1].decl_certificate_hash(),
                    prior_tokens[1].pre_env_fingerprint(),
                    prior_tokens[1].post_env_fingerprint(),
                ),
            ]
        })
    );
}

#[test]
fn build_module_cert_from_checked_candidates_builds_verifiable_certificate() {
    let import = verify_module(axiom_module("Lib.CheckedBuild", "CheckedBuildT"));
    let imports = [import.clone()];
    let declarations = [
        axiom_over("UsesCheckedBuildT", "CheckedBuildT"),
        trivial_axiom("LocalCheckedBuildT"),
    ];
    let tokens = accepted_tokens(
        check_core_decl_candidates(CandidateBatch {
            imports: &imports,
            prior_current_decls: &[],
            candidates: declarations
                .iter()
                .cloned()
                .map(|declaration| CoreDeclCandidate { declaration })
                .collect(),
            limits: generous_limits_with_declarations(2),
        })
        .unwrap(),
    );

    let cert = build_module_cert_from_checked_candidates(
        Name::from_dotted("Producer.CheckedBuild"),
        &imports,
        &tokens,
    )
    .unwrap();
    assert_eq!(cert.declarations.len(), 2);

    let bytes = encode_module_cert(&cert).unwrap();
    let mut session = VerifierSession::new();
    session.register_verified_module(import);
    let verified = verify_module_cert(&bytes, &mut session, &AxiomPolicy::normal()).unwrap();
    assert_eq!(
        verified.module(),
        &Name::from_dotted("Producer.CheckedBuild")
    );
}

#[test]
fn build_module_cert_from_checked_candidates_rejects_token_order_mismatch() {
    let declarations = [
        trivial_axiom("BuildOrderA"),
        axiom_over("BuildOrderB", "BuildOrderA"),
    ];
    let mut tokens = accepted_tokens(
        check_core_decl_candidates(CandidateBatch {
            imports: &[],
            prior_current_decls: &[],
            candidates: declarations
                .into_iter()
                .map(|declaration| CoreDeclCandidate { declaration })
                .collect(),
            limits: generous_limits_with_declarations(2),
        })
        .unwrap(),
    );
    tokens.reverse();

    assert!(matches!(
        build_module_cert_from_checked_candidates(
            Name::from_dotted("Producer.Order"),
            &[],
            &tokens
        ),
        Err(CertError::ProducerTokenHashMismatch {
            token_index: 0,
            field: ProducerTokenHashField::PreEnvFingerprint,
            ..
        })
    ));
}

#[test]
fn build_module_cert_from_checked_candidates_requires_explicit_verification_for_import_store() {
    let tokens = accepted_tokens(
        check_core_decl_candidates(CandidateBatch {
            imports: &[],
            prior_current_decls: &[],
            candidates: vec![CoreDeclCandidate {
                declaration: trivial_axiom("UncheckedBuildT"),
            }],
            limits: generous_limits(),
        })
        .unwrap(),
    );
    let cert = build_module_cert_from_checked_candidates(
        Name::from_dotted("Producer.UncheckedBuild"),
        &[],
        &tokens,
    )
    .unwrap();
    let bytes = encode_module_cert(&cert).unwrap();

    let mut producer_session = VerifierSession::new();
    let verified =
        verify_module_cert(&bytes, &mut producer_session, &AxiomPolicy::normal()).unwrap();
    let downstream = build_module_cert(
        CoreModule {
            name: Name::from_dotted("Producer.Downstream"),
            declarations: vec![axiom_over("UsesUncheckedBuildT", "UncheckedBuildT")],
        },
        std::slice::from_ref(&verified),
    )
    .unwrap();
    let downstream_bytes = encode_module_cert(&downstream).unwrap();

    let mut empty_session = VerifierSession::new();
    assert!(matches!(
        verify_module_cert(&downstream_bytes, &mut empty_session, &AxiomPolicy::normal()),
        Err(CertError::ImportHashMismatch { module })
            if module == Name::from_dotted("Producer.UncheckedBuild")
    ));
    verify_module_cert(
        &downstream_bytes,
        &mut producer_session,
        &AxiomPolicy::normal(),
    )
    .unwrap();
}

#[test]
fn accepted_candidate_token_type_is_distinct_from_verified_module() {
    let tokens = accepted_tokens(
        check_core_decl_candidates(CandidateBatch {
            imports: &[],
            prior_current_decls: &[],
            candidates: vec![CoreDeclCandidate {
                declaration: trivial_axiom("AcceptedTokenBoundary"),
            }],
            limits: generous_limits(),
        })
        .unwrap(),
    );

    assert_eq!(tokens.len(), 1);
    assert_ne!(
        std::any::TypeId::of::<CheckedDeclCandidate>(),
        std::any::TypeId::of::<VerifiedModule>()
    );
}

#[test]
fn validate_candidate_batch_imports_preserves_canonical_import_index_order() {
    let import_a = verify_module(axiom_module("Lib.A", "A"));
    let import_b = verify_module(axiom_module("Lib.B", "B"));

    let imports = [import_a.clone(), import_b.clone()];
    let keys = validate_candidate_batch_imports(&empty_batch(&imports)).unwrap();
    assert_eq!(
        keys,
        vec![
            ProducerImportEnvKey {
                module: import_a.module().clone(),
                export_hash: import_a.export_hash(),
            },
            ProducerImportEnvKey {
                module: import_b.module().clone(),
                export_hash: import_b.export_hash(),
            },
        ]
    );

    let reversed_imports = [import_b, import_a];
    assert_eq!(
        validate_candidate_batch_imports(&empty_batch(&reversed_imports)).unwrap_err(),
        CertError::NonCanonicalEncoding { object: "Imports" }
    );
}

#[test]
fn validate_candidate_batch_imports_rejects_duplicate_env_key_before_certificate_hash() {
    let import_a = verify_module(opaque_def_module(
        "Lib.SameExport",
        Expr::sort(Level::zero()),
    ));
    let import_b = verify_module(opaque_def_module(
        "Lib.SameExport",
        Expr::pi("x", Expr::sort(Level::zero()), Expr::sort(Level::zero())),
    ));

    assert_eq!(import_a.export_hash(), import_b.export_hash());
    assert_ne!(import_a.certificate_hash(), import_b.certificate_hash());

    let imports = [import_a.clone(), import_b];
    assert_eq!(
        validate_candidate_batch_imports(&empty_batch(&imports)).unwrap_err(),
        CertError::DuplicateImportEnvKey {
            module: import_a.module().clone(),
            export_hash: import_a.export_hash(),
        }
    );
}

#[test]
fn producer_env_fingerprint_canonical_bytes_fix_record_order() {
    let env = producer_env(
        vec![ProducerImportEnvKey {
            module: Name::from_dotted("Lib.A"),
            export_hash: hash(0x11),
        }],
        vec![ProducerCheckedDeclInterface {
            decl_interface_hash: hash(0x22),
            axiom_dependencies: vec![],
        }],
    );

    let mut expected = vec![0x01, 0x02, 0x03, b'L', b'i', b'b', 0x01, b'A'];
    expected.extend(hash(0x11));
    expected.push(0x01);
    expected.extend(hash(0x22));
    expected.push(0x00);

    assert_eq!(producer_env_fingerprint_canonical_bytes(&env), expected);
    assert_eq!(
        producer_env_fingerprint(&env),
        [
            0x1c, 0xa5, 0xe5, 0xaa, 0xa4, 0x39, 0xec, 0x3e, 0x99, 0xc2, 0xc5, 0xe9, 0xff, 0x9d,
            0xaa, 0xda, 0xfd, 0x73, 0xff, 0x9f, 0x43, 0x57, 0xf5, 0x4c, 0x83, 0xda, 0xf6, 0x74,
            0x9e, 0x4a, 0xc4, 0x15,
        ]
    );
}

#[test]
fn producer_env_fingerprint_ignores_import_certificate_hash() {
    let import_a = verify_module(opaque_def_module(
        "Lib.SameExportForEnv",
        Expr::sort(Level::zero()),
    ));
    let import_b = verify_module(opaque_def_module(
        "Lib.SameExportForEnv",
        Expr::pi("x", Expr::sort(Level::zero()), Expr::sort(Level::zero())),
    ));

    assert_eq!(import_a.export_hash(), import_b.export_hash());
    assert_ne!(import_a.certificate_hash(), import_b.certificate_hash());

    let env_a = producer_env(vec![producer_import_env_key(&import_a)], vec![]);
    let env_b = producer_env(vec![producer_import_env_key(&import_b)], vec![]);

    assert_eq!(
        producer_env_fingerprint(&env_a),
        producer_env_fingerprint(&env_b)
    );
}

#[test]
fn producer_env_fingerprint_preserves_checked_decl_order() {
    let first = checked_decl_interface(0x31);
    let second = checked_decl_interface(0x32);

    let env_ab = producer_env(vec![], vec![first.clone(), second.clone()]);
    let env_ba = producer_env(vec![], vec![second, first]);

    assert_ne!(
        producer_env_fingerprint(&env_ab),
        producer_env_fingerprint(&env_ba)
    );
}

#[test]
fn producer_env_fingerprint_sorts_axiom_dependencies_canonically() {
    let axiom_a = local_axiom_ref(0, 1, 0x41);
    let axiom_b = local_axiom_ref(1, 0, 0x42);

    let env_ab = producer_env(
        vec![],
        vec![ProducerCheckedDeclInterface {
            decl_interface_hash: hash(0x51),
            axiom_dependencies: vec![axiom_a.clone(), axiom_b.clone()],
        }],
    );
    let env_ba = producer_env(
        vec![],
        vec![ProducerCheckedDeclInterface {
            decl_interface_hash: hash(0x51),
            axiom_dependencies: vec![axiom_b, axiom_a],
        }],
    );

    assert_eq!(
        producer_env_fingerprint_canonical_bytes(&env_ab),
        producer_env_fingerprint_canonical_bytes(&env_ba)
    );
    assert_eq!(
        producer_env_fingerprint(&env_ab),
        producer_env_fingerprint(&env_ba)
    );
}

#[test]
fn canonical_import_keys_and_export_views_preserve_same_indices() {
    let import_a = verify_module(axiom_module("Lib.IndexA", "IndexA"));
    let import_b = verify_module(axiom_module("Lib.IndexB", "IndexB"));
    let imports = [import_a, import_b];

    let keys = canonical_import_env_keys(&imports).unwrap();
    let views = canonical_import_export_views(&imports).unwrap();

    assert_eq!(keys.len(), views.len());
    for (key, view) in keys.iter().zip(&views) {
        assert_eq!(key.module, view.module);
        assert_eq!(key.export_hash, view.export_hash);
    }
}

#[test]
fn producer_checked_decl_interface_uses_import_export_view_indices() {
    let import_a = verify_module(axiom_module("Lib.LookupA", "LookupA"));
    let import_b = verify_module(axiom_module("Lib.LookupB", "LookupB"));
    let imports = [import_a, import_b];
    let lookup = producer_lookup_env(&imports, &[]).unwrap();

    let interface =
        producer_checked_decl_interface(&imported_theorem("UsesLookupB", "LookupB"), &lookup)
            .unwrap();

    assert_eq!(interface.axiom_dependencies.len(), 1);
    assert!(matches!(
        interface.axiom_dependencies[0].global_ref,
        GlobalRef::Imported {
            import_index: 1,
            ..
        }
    ));
}

#[test]
fn producer_checked_decl_interface_recomputes_axioms_from_export_view_not_key() {
    let import = verify_module(axiom_module("Lib.LookupSource", "LookupSource"));
    let imports = [import];
    let lookup = producer_lookup_env(&imports, &[]).unwrap();
    let decl = imported_theorem("UsesLookupSource", "LookupSource");

    let from_verified_view = producer_checked_decl_interface(&decl, &lookup).unwrap();

    let mut tampered_lookup = lookup.clone();
    tampered_lookup.import_exports[0].exports[0]
        .axiom_dependencies
        .clear();
    let from_tampered_view = producer_checked_decl_interface(&decl, &tampered_lookup).unwrap();

    assert_eq!(from_verified_view.axiom_dependencies.len(), 1);
    assert!(from_tampered_view.axiom_dependencies.is_empty());
    assert_ne!(
        from_verified_view.decl_interface_hash,
        from_tampered_view.decl_interface_hash
    );
}

#[test]
fn producer_checked_decl_interface_matches_certificate_generation_for_imported_axiom() {
    let import = verify_module(axiom_module("Lib.MatchP", "MatchP"));
    let imports = [import.clone()];
    let decl = Decl::Axiom {
        name: "MatchQ".to_owned(),
        universe_params: vec![],
        ty: Expr::konst("MatchP", vec![]),
    };
    let cert = build_module_cert(
        CoreModule {
            name: Name::from_dotted("MatchQ"),
            declarations: vec![decl.clone()],
        },
        &imports,
    )
    .unwrap();
    let lookup = producer_lookup_env(&imports, &[]).unwrap();

    let interface = producer_checked_decl_interface(&decl, &lookup).unwrap();

    assert_eq!(
        interface.decl_interface_hash,
        cert.declarations[0].hashes.decl_interface_hash
    );
    assert_eq!(
        interface.axiom_dependencies,
        cert.declarations[0].axiom_dependencies
    );
}

#[test]
fn initial_env_fingerprint_matches_explicit_full_recompute() {
    let import_a = verify_module(axiom_module("Lib.InitialA", "InitialA"));
    let import_b = verify_module(axiom_module("Lib.InitialB", "InitialB"));
    let imports = [import_a, import_b];

    let expected = producer_env_fingerprint(&ProducerEnvFingerprintBytes {
        direct_imports: canonical_import_env_keys(&imports).unwrap(),
        checked_decls: vec![],
    });

    assert_eq!(initial_env_fingerprint(&imports).unwrap(), expected);
}

#[test]
fn post_env_fingerprint_matches_explicit_full_recompute() {
    let import = verify_module(axiom_module("Lib.PostSource", "PostSource"));
    let imports = [import];
    let prior = vec![checked_decl_interface(0x61)];
    let decl = imported_theorem("UsesPostSource", "PostSource");
    let lookup = producer_lookup_env(&imports, &prior).unwrap();
    let mut expected_checked = prior.clone();
    expected_checked.push(producer_checked_decl_interface(&decl, &lookup).unwrap());
    let expected = producer_env_fingerprint(&ProducerEnvFingerprintBytes {
        direct_imports: canonical_import_env_keys(&imports).unwrap(),
        checked_decls: expected_checked,
    });

    assert_eq!(
        post_env_fingerprint(&imports, &prior, &decl).unwrap(),
        expected
    );
}

#[test]
fn post_env_fingerprint_is_deterministic_for_same_inputs() {
    let import = verify_module(axiom_module("Lib.PostDeterministic", "PostDeterministic"));
    let imports = [import];
    let prior = vec![ProducerCheckedDeclInterface {
        decl_interface_hash: hash(0x62),
        axiom_dependencies: vec![local_axiom_ref(0, 0, 0x63)],
    }];
    let decl = imported_theorem("UsesPostDeterministic", "PostDeterministic");

    assert_eq!(
        post_env_fingerprint(&imports, &prior, &decl).unwrap(),
        post_env_fingerprint(&imports, &prior, &decl).unwrap()
    );
}

#[test]
fn post_env_fingerprint_changes_when_checked_decl_sequence_changes() {
    let import = verify_module(axiom_module("Lib.PostSequence", "PostSequence"));
    let imports = [import];
    let decl = imported_theorem("UsesPostSequence", "PostSequence");
    let prior_a = vec![checked_decl_interface(0x71)];
    let prior_b = vec![checked_decl_interface(0x72)];

    assert_ne!(
        post_env_fingerprint(&imports, &prior_a, &decl).unwrap(),
        post_env_fingerprint(&imports, &prior_b, &decl).unwrap()
    );
}

#[test]
fn post_env_fingerprint_uses_import_public_environment_not_certificate_identity() {
    let import_a = verify_module(opaque_def_module(
        "Lib.SamePostExport",
        Expr::sort(Level::zero()),
    ));
    let import_b = verify_module(opaque_def_module(
        "Lib.SamePostExport",
        Expr::pi("x", Expr::sort(Level::zero()), Expr::sort(Level::zero())),
    ));
    let decl = Decl::Axiom {
        name: "UsesSamePostExport".to_owned(),
        universe_params: vec![],
        ty: Expr::konst("carrier", vec![]),
    };

    assert_eq!(import_a.export_hash(), import_b.export_hash());
    assert_ne!(import_a.certificate_hash(), import_b.certificate_hash());
    assert_eq!(
        post_env_fingerprint(&[import_a], &[], &decl).unwrap(),
        post_env_fingerprint(&[import_b], &[], &decl).unwrap()
    );
}

#[test]
fn prior_chain_fingerprint_canonical_bytes_fix_record_order() {
    let chain = ProducerPriorChainBytes {
        checked_decls: vec![prior_entry(hash(0x11), hash(0x22), hash(0x33), hash(0x44))],
    };
    let mut expected = vec![0x01];
    expected.extend(hash(0x11));
    expected.extend(hash(0x22));
    expected.extend(hash(0x33));
    expected.extend(hash(0x44));

    assert_eq!(prior_chain_fingerprint_canonical_bytes(&chain), expected);
}

#[test]
fn prior_chain_fingerprint_empty_chain_is_deterministic() {
    let chain = ProducerPriorChainBytes {
        checked_decls: vec![],
    };

    assert_eq!(prior_chain_fingerprint_canonical_bytes(&chain), vec![0x00]);
    assert_eq!(
        prior_chain_fingerprint(&chain),
        [
            0x81, 0x78, 0xcf, 0xcd, 0xe5, 0xe9, 0x89, 0x13, 0x8f, 0x61, 0x8d, 0x11, 0x02, 0x0f,
            0xef, 0xd3, 0x68, 0xde, 0x61, 0x5a, 0x69, 0xb2, 0x3e, 0x45, 0x06, 0x0e, 0xac, 0xa9,
            0xb8, 0xeb, 0x8b, 0xa4,
        ]
    );
}

#[test]
fn prior_chain_fingerprint_preserves_declaration_order() {
    let first = prior_entry(hash(0x11), hash(0x12), hash(0x13), hash(0x14));
    let second = prior_entry(hash(0x21), hash(0x22), hash(0x23), hash(0x24));
    let chain_ab = ProducerPriorChainBytes {
        checked_decls: vec![first.clone(), second.clone()],
    };
    let chain_ba = ProducerPriorChainBytes {
        checked_decls: vec![second, first],
    };

    assert_ne!(
        prior_chain_fingerprint(&chain_ab),
        prior_chain_fingerprint(&chain_ba)
    );
}

#[test]
fn prior_chain_fingerprint_changes_for_body_only_certificate_hash_change() {
    let cert_a = build_module_cert(
        id_theorem_module("Test.PriorBodyOnly", id_value("A", "x")),
        &[],
    )
    .unwrap();
    let cert_b = build_module_cert(
        id_theorem_module("Test.PriorBodyOnly", id_value_with_beta_redex()),
        &[],
    )
    .unwrap();
    let decl_a = &cert_a.declarations[0];
    let decl_b = &cert_b.declarations[0];

    assert_eq!(
        decl_a.hashes.decl_interface_hash,
        decl_b.hashes.decl_interface_hash
    );
    assert_ne!(
        decl_a.hashes.decl_certificate_hash,
        decl_b.hashes.decl_certificate_hash
    );

    let pre_env = initial_env_fingerprint(&[]).unwrap();
    let post_env_a = producer_env_fingerprint(&ProducerEnvFingerprintBytes {
        direct_imports: vec![],
        checked_decls: vec![ProducerCheckedDeclInterface {
            decl_interface_hash: decl_a.hashes.decl_interface_hash,
            axiom_dependencies: decl_a.axiom_dependencies.clone(),
        }],
    });
    let post_env_b = producer_env_fingerprint(&ProducerEnvFingerprintBytes {
        direct_imports: vec![],
        checked_decls: vec![ProducerCheckedDeclInterface {
            decl_interface_hash: decl_b.hashes.decl_interface_hash,
            axiom_dependencies: decl_b.axiom_dependencies.clone(),
        }],
    });

    assert_eq!(post_env_a, post_env_b);
    assert_ne!(
        prior_chain_fingerprint(&ProducerPriorChainBytes {
            checked_decls: vec![prior_entry(
                decl_a.hashes.decl_interface_hash,
                decl_a.hashes.decl_certificate_hash,
                pre_env,
                post_env_a,
            )],
        }),
        prior_chain_fingerprint(&ProducerPriorChainBytes {
            checked_decls: vec![prior_entry(
                decl_b.hashes.decl_interface_hash,
                decl_b.hashes.decl_certificate_hash,
                pre_env,
                post_env_b,
            )],
        })
    );
}

#[test]
fn prior_chain_fingerprint_changes_for_opaque_def_body_only_certificate_hash_change() {
    let cert_a = build_module_cert(
        opaque_def_module("Test.PriorOpaqueDefBodyOnly", Expr::sort(Level::zero())),
        &[],
    )
    .unwrap();
    let cert_b = build_module_cert(
        opaque_def_module(
            "Test.PriorOpaqueDefBodyOnly",
            Expr::pi("x", Expr::sort(Level::zero()), Expr::sort(Level::zero())),
        ),
        &[],
    )
    .unwrap();
    let decl_a = &cert_a.declarations[0];
    let decl_b = &cert_b.declarations[0];

    assert_eq!(cert_a.hashes.export_hash, cert_b.hashes.export_hash);
    assert_eq!(
        decl_a.hashes.decl_interface_hash,
        decl_b.hashes.decl_interface_hash
    );
    assert_ne!(
        decl_a.hashes.decl_certificate_hash,
        decl_b.hashes.decl_certificate_hash
    );

    let pre_env = initial_env_fingerprint(&[]).unwrap();
    let post_env_a = producer_env_fingerprint(&ProducerEnvFingerprintBytes {
        direct_imports: vec![],
        checked_decls: vec![ProducerCheckedDeclInterface {
            decl_interface_hash: decl_a.hashes.decl_interface_hash,
            axiom_dependencies: decl_a.axiom_dependencies.clone(),
        }],
    });
    let post_env_b = producer_env_fingerprint(&ProducerEnvFingerprintBytes {
        direct_imports: vec![],
        checked_decls: vec![ProducerCheckedDeclInterface {
            decl_interface_hash: decl_b.hashes.decl_interface_hash,
            axiom_dependencies: decl_b.axiom_dependencies.clone(),
        }],
    });

    assert_eq!(post_env_a, post_env_b);
    assert_ne!(
        prior_chain_fingerprint(&ProducerPriorChainBytes {
            checked_decls: vec![prior_entry(
                decl_a.hashes.decl_interface_hash,
                decl_a.hashes.decl_certificate_hash,
                pre_env,
                post_env_a,
            )],
        }),
        prior_chain_fingerprint(&ProducerPriorChainBytes {
            checked_decls: vec![prior_entry(
                decl_b.hashes.decl_interface_hash,
                decl_b.hashes.decl_certificate_hash,
                pre_env,
                post_env_b,
            )],
        })
    );
}

#[test]
fn producer_sidecar_is_out_of_band_for_certificate_bytes_and_hashes() {
    let module_name = "Test.ProducerSidecarOutOfBand";
    let sidecar = TestProducerSidecar::ai(module_name);
    let mut changed_sidecar = sidecar.clone();
    changed_sidecar.producer_profile = ProducerProfile::HumanSurface;
    changed_sidecar.producer_run_id = "human-rerun-2".to_owned();
    changed_sidecar.model_name = "different-audit-only-model".to_owned();
    changed_sidecar.prompt = "different prompt kept outside certificate".to_owned();
    changed_sidecar.score = 7;
    changed_sidecar.diagnostics = vec![
        "cache miss".to_owned(),
        "diagnostic payload changed".to_owned(),
    ];
    changed_sidecar.cache_hit = false;
    changed_sidecar.input_artifact_hashes = vec![hash(0x33), hash(0x44)];
    assert_ne!(sidecar.marker(), changed_sidecar.marker());

    let module = CoreModule {
        name: Name::from_dotted(module_name),
        declarations: vec![trivial_axiom("P")],
    };

    let with_sidecar =
        build_bytes_and_hashes_with_out_of_band_sidecar(module.clone(), Some(&sidecar));
    let with_changed_sidecar =
        build_bytes_and_hashes_with_out_of_band_sidecar(module.clone(), Some(&changed_sidecar));
    let without_sidecar = build_bytes_and_hashes_with_out_of_band_sidecar(module, None);
    assert_eq!(with_sidecar, with_changed_sidecar);
    assert_eq!(with_sidecar, without_sidecar);

    let mut session = VerifierSession::new();
    verify_module_cert(&with_sidecar.0, &mut session, &AxiomPolicy::normal()).unwrap();
}

#[test]
fn producer_api_proof_acceptance_negative_score_prompt_and_sidecar_tampering_do_not_change_certificate_identity(
) {
    let module_name = "Test.ProducerAcceptanceNegativeSidecar";
    let sidecar = TestProducerSidecar::ai(module_name);
    let mut tampered = sidecar.clone();
    tampered.prompt = "prompt tampering tries to rewrite trust evidence".to_owned();
    tampered.score = 1_000_000;
    tampered.model_name = "score-tampering-model".to_owned();
    tampered.diagnostics = vec!["sidecar substitution attempted".to_owned()];
    tampered.input_artifact_hashes = vec![hash(0xaa), hash(0xbb)];
    assert_ne!(sidecar.marker(), tampered.marker());

    let module = CoreModule {
        name: Name::from_dotted(module_name),
        declarations: vec![trivial_axiom("P")],
    };

    let original = build_bytes_and_hashes_with_out_of_band_sidecar(module.clone(), Some(&sidecar));
    let tampered = build_bytes_and_hashes_with_out_of_band_sidecar(module, Some(&tampered));

    assert_eq!(original, tampered);

    let mut session = VerifierSession::new();
    verify_module_cert(&original.0, &mut session, &AxiomPolicy::normal()).unwrap();
}

#[test]
fn human_and_ai_producer_sidecars_emit_same_certificate_for_same_core_declarations() {
    let module_name = "Test.ProducerSidecarSameCore";
    let declarations = vec![
        trivial_axiom("SidecarT"),
        axiom_over("sidecar_value", "SidecarT"),
    ];
    let human_sidecar = TestProducerSidecar::human(module_name);
    let ai_sidecar = TestProducerSidecar::ai(module_name);
    assert_ne!(human_sidecar.marker(), ai_sidecar.marker());

    let human_cert = build_module_cert(
        CoreModule {
            name: Name::from_dotted(module_name),
            declarations: declarations.clone(),
        },
        &[],
    )
    .unwrap();
    let tokens = accepted_tokens(
        check_core_decl_candidates(CandidateBatch {
            imports: &[],
            prior_current_decls: &[],
            candidates: declarations
                .into_iter()
                .map(|declaration| CoreDeclCandidate { declaration })
                .collect(),
            limits: generous_limits_with_declarations(2),
        })
        .unwrap(),
    );
    let ai_cert =
        build_module_cert_from_checked_candidates(Name::from_dotted(module_name), &[], &tokens)
            .unwrap();
    let human_bytes = encode_module_cert(&human_cert).unwrap();
    let ai_bytes = encode_module_cert(&ai_cert).unwrap();

    assert_eq!(human_bytes, ai_bytes);
    assert_eq!(human_cert.hashes, ai_cert.hashes);
    assert_eq!(human_cert.hashes.export_hash, ai_cert.hashes.export_hash);
    assert_eq!(
        human_cert.hashes.axiom_report_hash,
        ai_cert.hashes.axiom_report_hash
    );
    assert_eq!(
        human_cert.hashes.certificate_hash,
        ai_cert.hashes.certificate_hash
    );

    let mut session = VerifierSession::new();
    verify_module_cert(&ai_bytes, &mut session, &AxiomPolicy::normal()).unwrap();
}

#[test]
fn checked_candidate_certificate_is_independent_of_cache_sidecar_state() {
    let module_name = "Test.ProducerCacheSidecar";
    let declarations = [trivial_axiom("CacheT"), axiom_over("cache_value", "CacheT")];
    let cache_hit_tokens = accepted_tokens(
        check_core_decl_candidates(CandidateBatch {
            imports: &[],
            prior_current_decls: &[],
            candidates: declarations
                .iter()
                .cloned()
                .map(|declaration| CoreDeclCandidate { declaration })
                .collect(),
            limits: generous_limits_with_declarations(2),
        })
        .unwrap(),
    );
    let cache_miss_tokens = accepted_tokens(
        check_core_decl_candidates(CandidateBatch {
            imports: &[],
            prior_current_decls: &[],
            candidates: declarations
                .iter()
                .cloned()
                .map(|declaration| CoreDeclCandidate { declaration })
                .collect(),
            limits: generous_limits_with_declarations(2),
        })
        .unwrap(),
    );
    let mut cache_hit_sidecar = TestProducerSidecar::ai(module_name);
    cache_hit_sidecar.cache_hit = true;
    let mut cache_miss_sidecar = cache_hit_sidecar.clone();
    cache_miss_sidecar.producer_run_id = "ai-cache-miss-run".to_owned();
    cache_miss_sidecar.cache_hit = false;
    cache_miss_sidecar.diagnostics = vec!["cache miss".to_owned()];
    assert_ne!(cache_hit_sidecar.marker(), cache_miss_sidecar.marker());

    assert_eq!(
        cache_hit_tokens
            .iter()
            .map(CheckedDeclCandidate::decl_interface_hash)
            .collect::<Vec<_>>(),
        cache_miss_tokens
            .iter()
            .map(CheckedDeclCandidate::decl_interface_hash)
            .collect::<Vec<_>>()
    );
    let cache_hit_cert = build_module_cert_from_checked_candidates(
        Name::from_dotted(module_name),
        &[],
        &cache_hit_tokens,
    )
    .unwrap();
    let cache_miss_cert = build_module_cert_from_checked_candidates(
        Name::from_dotted(module_name),
        &[],
        &cache_miss_tokens,
    )
    .unwrap();
    let cache_hit_bytes = encode_module_cert(&cache_hit_cert).unwrap();
    let cache_miss_bytes = encode_module_cert(&cache_miss_cert).unwrap();

    assert_eq!(cache_hit_bytes, cache_miss_bytes);
    assert_eq!(cache_hit_cert.hashes, cache_miss_cert.hashes);

    let mut session = VerifierSession::new();
    verify_module_cert(&cache_hit_bytes, &mut session, &AxiomPolicy::normal()).unwrap();
}

#[test]
fn producer_limits_canonical_bytes_fix_field_order_and_minimal_uleb128() {
    let limits = ProducerLimits {
        max_declarations: 1,
        max_expr_nodes: 128,
        max_level_nodes: 16_384,
        max_name_components: 4,
        max_reduction_steps: 16,
        max_conversion_steps: 65_536,
    };

    assert_eq!(
        producer_limits_canonical_bytes(&limits),
        vec![0x01, 0x80, 0x01, 0x80, 0x80, 0x01, 0x04, 0x10, 0x80, 0x80, 0x04]
    );
}

#[test]
fn producer_limits_hash_is_deterministic_and_field_order_sensitive() {
    let limits = ProducerLimits {
        max_declarations: 1,
        max_expr_nodes: 2,
        max_level_nodes: 3,
        max_name_components: 4,
        max_reduction_steps: 5,
        max_conversion_steps: 6,
    };
    let swapped_first_two_fields = ProducerLimits {
        max_declarations: 2,
        max_expr_nodes: 1,
        ..limits
    };

    assert_eq!(producer_limits_hash(&limits), producer_limits_hash(&limits));
    assert_eq!(
        producer_limits_hash(&limits),
        [
            0xc9, 0x89, 0x1e, 0x26, 0xbb, 0x98, 0x9d, 0x9d, 0x53, 0x3b, 0x83, 0x1c, 0x08, 0xbb,
            0x86, 0xf6, 0x3b, 0xcd, 0x28, 0x4f, 0x60, 0x7d, 0xb6, 0xe4, 0x1f, 0x27, 0x5d, 0x55,
            0xb8, 0x8e, 0x18, 0x4f,
        ]
    );
    assert_ne!(
        producer_limits_hash(&limits),
        producer_limits_hash(&swapped_first_two_fields)
    );
}

#[test]
fn stricter_or_equal_compares_every_limit_field() {
    let baseline = ProducerLimits {
        max_declarations: 10,
        max_expr_nodes: 20,
        max_level_nodes: 30,
        max_name_components: 40,
        max_reduction_steps: 50,
        max_conversion_steps: 60,
    };
    let stricter = ProducerLimits {
        max_declarations: 9,
        max_expr_nodes: 19,
        max_level_nodes: 29,
        max_name_components: 39,
        max_reduction_steps: 49,
        max_conversion_steps: 59,
    };

    assert!(stricter_or_equal(&baseline, &baseline));
    assert!(stricter_or_equal(&stricter, &baseline));

    let looser_profiles = [
        ProducerLimits {
            max_declarations: baseline.max_declarations + 1,
            ..baseline
        },
        ProducerLimits {
            max_expr_nodes: baseline.max_expr_nodes + 1,
            ..baseline
        },
        ProducerLimits {
            max_level_nodes: baseline.max_level_nodes + 1,
            ..baseline
        },
        ProducerLimits {
            max_name_components: baseline.max_name_components + 1,
            ..baseline
        },
        ProducerLimits {
            max_reduction_steps: baseline.max_reduction_steps + 1,
            ..baseline
        },
        ProducerLimits {
            max_conversion_steps: baseline.max_conversion_steps + 1,
            ..baseline
        },
    ];

    for looser in looser_profiles {
        assert!(!stricter_or_equal(&looser, &baseline));
    }
}

#[test]
fn precheck_core_decl_candidate_accepts_simple_axiom_under_limits() {
    let candidate = CoreDeclCandidate {
        declaration: trivial_axiom("P"),
    };

    precheck_core_decl_candidate(&Env::new(), &candidate, &generous_limits()).unwrap();
}

#[test]
fn precheck_core_decl_candidate_rejects_schema_limit_excess_deterministically() {
    let candidate = CoreDeclCandidate {
        declaration: trivial_axiom("A.B"),
    };

    let mut limits = generous_limits();
    limits.max_declarations = 0;
    assert_eq!(
        precheck_core_decl_candidate(&Env::new(), &candidate, &limits).unwrap_err(),
        CertError::ProducerLimitExceeded {
            limit: ProducerLimitKind::MaxDeclarations
        }
    );

    let mut limits = generous_limits();
    limits.max_expr_nodes = 0;
    assert_eq!(
        precheck_core_decl_candidate(&Env::new(), &candidate, &limits).unwrap_err(),
        CertError::ProducerLimitExceeded {
            limit: ProducerLimitKind::MaxExprNodes
        }
    );

    let mut limits = generous_limits();
    limits.max_level_nodes = 0;
    assert_eq!(
        precheck_core_decl_candidate(&Env::new(), &candidate, &limits).unwrap_err(),
        CertError::ProducerLimitExceeded {
            limit: ProducerLimitKind::MaxLevelNodes
        }
    );

    let mut limits = generous_limits();
    limits.max_name_components = 1;
    assert_eq!(
        precheck_core_decl_candidate(&Env::new(), &candidate, &limits).unwrap_err(),
        CertError::ProducerLimitExceeded {
            limit: ProducerLimitKind::MaxNameComponents
        }
    );
}

#[test]
fn precheck_core_decl_candidate_maps_reduction_and_conversion_limits_to_kernel_fuel() {
    let axiom = CoreDeclCandidate {
        declaration: trivial_axiom("P"),
    };
    let mut limits = generous_limits();
    limits.max_reduction_steps = 0;
    assert_eq!(
        precheck_core_decl_candidate(&Env::new(), &axiom, &limits).unwrap_err(),
        CertError::Kernel(KernelError::ResourceLimit {
            kind: ResourceLimitKind::Whnf
        })
    );

    let definition = CoreDeclCandidate {
        declaration: Decl::Def {
            name: "P".to_owned(),
            universe_params: vec![],
            ty: Expr::sort(Level::succ(Level::zero())),
            value: Expr::sort(Level::zero()),
            reducibility: Reducibility::Reducible,
        },
    };
    let mut limits = generous_limits();
    limits.max_conversion_steps = 0;
    assert_eq!(
        precheck_core_decl_candidate(&Env::new(), &definition, &limits).unwrap_err(),
        CertError::Kernel(KernelError::ResourceLimit {
            kind: ResourceLimitKind::Conversion
        })
    );
}

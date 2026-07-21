pub mod builtins;
pub mod context;
pub mod decl;
pub mod diagnostic;
pub mod env;
pub mod error;
pub mod expr;
pub mod level;
mod memo;
pub mod name;
pub mod positivity;
pub mod subst;
pub mod work;

pub use builtins::{
    eq, eq_inductive, eq_rec_type, eq_refl, eq_refl_type, eq_type, nat, nat_inductive,
    nat_rec_type, nat_succ, nat_zero, prop, type0,
};
pub use context::Ctx;
pub use decl::{
    Binder, ConstructorDecl, Decl, InductiveDecl, MutualInductiveBlock, RecursorDecl,
    RecursorRules, Reducibility,
};
pub use diagnostic::{
    DiagnosedKernelError, KernelComparisonOutcome, KernelConversionContext,
    KernelDiagnosticContext, KernelDiagnosticPhase, KernelExprHead,
};
pub use env::Env;
pub use error::{Error, ResourceLimitKind, Result};
pub use expr::Expr;
pub use level::{
    Level, UniverseConstraint, UniverseConstraintRelation, UniverseContext,
    MAX_UNIVERSE_ATOM_INEQUALITIES, MAX_UNIVERSE_CONTEXT_NODES,
};
pub use memo::{KernelExecutionOptions, KernelMemoMode, KERNEL_MEMO_LIMITS_V1};
pub use name::{is_canonical_dotted_name, is_canonical_name_component};
pub use positivity::{approved_nested_functor, ApprovedNestedFunctor, APPROVED_NESTED_FUNCTORS};
pub use work::{KernelWorkCounterSink, KernelWorkCounters};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn diagnosed_kernel_declaration_preserves_error_and_bounds_conversion_context() {
        let mut ordinary = Env::with_builtins().unwrap();
        let mut diagnosed = ordinary.clone();
        let declaration = Decl::Def {
            name: "Bad".to_owned(),
            universe_params: vec![],
            ty: nat(),
            value: Expr::sort(Level::zero()),
            reducibility: Reducibility::Reducible,
        };
        let ordinary_error = ordinary
            .add_def(
                "Bad",
                vec![],
                nat(),
                Expr::sort(Level::zero()),
                Reducibility::Reducible,
            )
            .unwrap_err();
        let diagnosed_error = diagnosed.add_decl_diagnosed(declaration).unwrap_err();
        assert!(matches!(ordinary_error, Error::TypeMismatch { .. }));
        assert!(matches!(
            diagnosed_error.error(),
            Error::TypeMismatch { .. }
        ));
        let context = diagnosed_error.context().unwrap();
        assert_eq!(context.phase().as_str(), "declaration_value");
        let conversion = context.conversion().unwrap();
        assert_eq!(conversion.outcome().as_str(), "not_defeq");
        assert!(conversion.lhs_head().as_str().len() <= 265);
        assert!(conversion.rhs_head().as_str().len() <= 265);
    }

    #[test]
    fn diagnosed_kernel_conversion_fuel_exhaustion_records_active_heads() {
        let env = Env::new();
        let error = env
            .is_defeq_diagnosed_with_fuel(
                &Ctx::new(),
                &[],
                &Expr::app(Expr::konst("f", vec![]), Expr::bvar(0)),
                &Expr::app(Expr::konst("g", vec![]), Expr::bvar(0)),
                0,
            )
            .unwrap_err();
        assert!(matches!(
            error.error(),
            Error::ResourceLimit {
                kind: ResourceLimitKind::Conversion
            }
        ));
        let conversion = error.context().unwrap().conversion().unwrap();
        assert_eq!(conversion.outcome().as_str(), "fuel_exhausted");
        assert_eq!(conversion.lhs_head().as_str(), "application");
        assert_eq!(conversion.rhs_head().as_str(), "application");
        assert_eq!(conversion.depth(), 0);
    }

    #[test]
    fn optional_work_meter_preserves_kernel_result() {
        let mut env = Env::with_builtins().unwrap();
        let term = nat_zero();
        let ordinary = env.infer(&Ctx::new(), &[], &term).unwrap();
        let mut counters = KernelWorkCounters::default();
        let measured = env
            .infer_with_work_counters(&Ctx::new(), &[], &term, Some(&mut counters))
            .unwrap();
        assert_eq!(measured, ordinary);
        assert_eq!(counters.infer_calls, 1);
        assert!(env
            .is_defeq_with_work_counters(&Ctx::new(), &[], &term, &term, Some(&mut counters),)
            .is_ok());
        assert_eq!(counters.defeq_calls, 1);
        assert!(counters.logical_fuel > 0);
        assert_eq!(counters.successful_fuel, counters.logical_fuel);
        assert_eq!(counters.exhausted_fuel, 0);

        let beta = Expr::app(Expr::lam("x", nat(), Expr::bvar(0)), nat_zero());
        env.whnf_with_work_counters(&Ctx::new(), &[], &beta, Some(&mut counters))
            .unwrap();
        let zeta = Expr::let_in("x", nat(), nat_zero(), Expr::bvar(0));
        env.whnf_with_work_counters(&Ctx::new(), &[], &zeta, Some(&mut counters))
            .unwrap();
        env.add_def(
            "Measured.zero",
            vec![],
            nat(),
            nat_zero(),
            Reducibility::Reducible,
        )
        .unwrap();
        env.whnf_with_work_counters(
            &Ctx::new(),
            &[],
            &Expr::konst("Measured.zero", vec![]),
            Some(&mut counters),
        )
        .unwrap();
        let motive = Expr::lam("_", nat(), nat());
        let step = Expr::lam("_", nat(), Expr::lam("ih", nat(), nat_succ(Expr::bvar(0))));
        let recursor = Expr::apps(
            Expr::konst("Nat.rec", vec![type0()]),
            vec![motive, nat_zero(), step, nat_zero()],
        );
        env.whnf_with_work_counters(&Ctx::new(), &[], &recursor, Some(&mut counters))
            .unwrap();
        let mut context = Ctx::new();
        context.push_definition("x", nat(), nat_zero());
        env.whnf_with_work_counters(&context, &[], &Expr::bvar(0), Some(&mut counters))
            .unwrap();

        assert_eq!(counters.beta_steps, 1);
        assert_eq!(counters.delta_steps, 1);
        assert_eq!(counters.iota_steps, 1);
        assert_eq!(counters.zeta_steps, 2);
        assert_eq!(counters.physical_reductions, 5);
        assert_eq!(counters.context_lookups, 1);
        assert_eq!(counters.context_shifts, 1);
    }

    #[test]
    fn diagnosed_kernel_declaration_records_nested_application_mismatch() {
        let mut ordinary = Env::with_builtins().unwrap();
        let mut diagnosed = ordinary.clone();
        let value = Expr::app(Expr::konst("Nat.succ", vec![]), Expr::sort(Level::zero()));
        let ordinary_error = ordinary
            .add_def(
                "BadNested",
                vec![],
                nat(),
                value.clone(),
                Reducibility::Reducible,
            )
            .unwrap_err();
        let diagnosed_error = diagnosed
            .add_decl_diagnosed(Decl::Def {
                name: "BadNested".to_owned(),
                universe_params: vec![],
                ty: nat(),
                value,
                reducibility: Reducibility::Reducible,
            })
            .unwrap_err();

        assert!(matches!(ordinary_error, Error::TypeMismatch { .. }));
        assert!(matches!(
            diagnosed_error.error(),
            Error::TypeMismatch { .. }
        ));
        let context = diagnosed_error.context().unwrap();
        assert_eq!(context.phase(), KernelDiagnosticPhase::DeclarationValue);
        assert_eq!(
            context.conversion().unwrap().outcome(),
            KernelComparisonOutcome::NotDefEq
        );
    }

    fn id_type() -> Expr {
        let u = Level::param("u");
        Expr::pi(
            "A",
            Expr::sort(u),
            Expr::pi("x", Expr::bvar(0), Expr::bvar(1)),
        )
    }

    fn id_value() -> Expr {
        let u = Level::param("u");
        Expr::lam(
            "A",
            Expr::sort(u),
            Expr::lam("x", Expr::bvar(0), Expr::bvar(0)),
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

    fn list_inductive() -> InductiveDecl {
        let u = Level::param("u");
        let list_a = |level: Level, a: Expr| Expr::app(Expr::konst("List", vec![level]), a);

        InductiveDecl::new(
            "List",
            vec!["u".to_owned()],
            vec![Binder::new("A", Expr::sort(u.clone()))],
            vec![],
            u.clone(),
            vec![
                ConstructorDecl::new(
                    "List.nil",
                    Expr::pi("A", Expr::sort(u.clone()), list_a(u.clone(), Expr::bvar(0))),
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
                                list_a(u.clone(), Expr::bvar(1)),
                                list_a(u.clone(), Expr::bvar(2)),
                            ),
                        ),
                    ),
                ),
            ],
            None,
        )
    }

    fn constrained_box_inductive() -> InductiveDecl {
        let u = Level::param("u");
        let v = Level::param("v");
        let box_a = |u: Level, v: Level, a: Expr| Expr::app(Expr::konst("Box", vec![u, v]), a);

        InductiveDecl::new(
            "Box",
            vec!["u".to_owned(), "v".to_owned()],
            vec![Binder::new("A", Expr::sort(u.clone()))],
            vec![],
            u.clone(),
            vec![ConstructorDecl::new(
                "Box.mk",
                Expr::pi(
                    "A",
                    Expr::sort(u.clone()),
                    box_a(u.clone(), v.clone(), Expr::bvar(0)),
                ),
            )],
            None,
        )
        .with_universe_constraints(vec![UniverseConstraint::le(u, v)])
    }

    fn negative_param_list_inductive() -> InductiveDecl {
        let u = Level::param("u");
        let list_a = |a| Expr::app(Expr::konst("List", vec![u.clone()]), a);
        InductiveDecl::new(
            "List",
            vec!["u".to_owned()],
            vec![Binder::new("A", Expr::sort(u.clone()))],
            vec![],
            u.clone(),
            vec![ConstructorDecl::new(
                "List.mk",
                Expr::pi(
                    "A",
                    Expr::sort(u.clone()),
                    Expr::pi(
                        "f",
                        Expr::pi("_", Expr::bvar(0), nat()),
                        list_a(Expr::bvar(1)),
                    ),
                ),
            )],
            None,
        )
        .with_universe_constraints(vec![UniverseConstraint::le(type0(), u)])
    }

    fn vec_type(level: Level, a: Expr, n: Expr) -> Expr {
        Expr::apps(Expr::konst("Vec", vec![level]), vec![a, n])
    }

    fn vec_inductive() -> InductiveDecl {
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

    fn fin_inductive() -> InductiveDecl {
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

    fn even_zero() -> Expr {
        Expr::konst("Even.zero", vec![])
    }

    fn even_succ(n: Expr, h: Expr) -> Expr {
        Expr::apps(Expr::konst("Even.succ", vec![]), vec![n, h])
    }

    fn odd_succ(n: Expr, h: Expr) -> Expr {
        Expr::apps(Expr::konst("Odd.succ", vec![]), vec![n, h])
    }

    fn even_motive_type() -> Expr {
        Expr::pi(
            "n",
            nat(),
            Expr::pi("_", even_type(Expr::bvar(0)), Expr::sort(prop())),
        )
    }

    fn odd_motive_type() -> Expr {
        Expr::pi(
            "n",
            nat(),
            Expr::pi("_", odd_type(Expr::bvar(0)), Expr::sort(prop())),
        )
    }

    fn even_succ_minor_type() -> Expr {
        Expr::pi(
            "n",
            nat(),
            Expr::pi(
                "h",
                odd_type(Expr::bvar(0)),
                Expr::pi(
                    "ih",
                    Expr::apps(Expr::bvar(3), vec![Expr::bvar(1), Expr::bvar(0)]),
                    Expr::apps(
                        Expr::bvar(5),
                        vec![
                            nat_succ(Expr::bvar(2)),
                            even_succ(Expr::bvar(2), Expr::bvar(1)),
                        ],
                    ),
                ),
            ),
        )
    }

    fn odd_succ_minor_type() -> Expr {
        Expr::pi(
            "n",
            nat(),
            Expr::pi(
                "h",
                even_type(Expr::bvar(0)),
                Expr::pi(
                    "ih",
                    Expr::apps(Expr::bvar(5), vec![Expr::bvar(1), Expr::bvar(0)]),
                    Expr::apps(
                        Expr::bvar(5),
                        vec![
                            nat_succ(Expr::bvar(2)),
                            odd_succ(Expr::bvar(2), Expr::bvar(1)),
                        ],
                    ),
                ),
            ),
        )
    }

    fn even_recursor_type() -> Expr {
        let z_ty = Expr::apps(Expr::bvar(1), vec![nat_zero(), even_zero()]);
        Expr::pi(
            "m_even",
            even_motive_type(),
            Expr::pi(
                "m_odd",
                odd_motive_type(),
                Expr::pi(
                    "zero",
                    z_ty,
                    Expr::pi(
                        "even_succ",
                        even_succ_minor_type(),
                        Expr::pi(
                            "odd_succ",
                            odd_succ_minor_type(),
                            Expr::pi(
                                "n",
                                nat(),
                                Expr::pi(
                                    "major",
                                    even_type(Expr::bvar(0)),
                                    Expr::apps(Expr::bvar(6), vec![Expr::bvar(1), Expr::bvar(0)]),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        )
    }

    fn odd_recursor_type() -> Expr {
        let z_ty = Expr::apps(Expr::bvar(1), vec![nat_zero(), even_zero()]);
        Expr::pi(
            "m_even",
            even_motive_type(),
            Expr::pi(
                "m_odd",
                odd_motive_type(),
                Expr::pi(
                    "zero",
                    z_ty,
                    Expr::pi(
                        "even_succ",
                        even_succ_minor_type(),
                        Expr::pi(
                            "odd_succ",
                            odd_succ_minor_type(),
                            Expr::pi(
                                "n",
                                nat(),
                                Expr::pi(
                                    "major",
                                    odd_type(Expr::bvar(0)),
                                    Expr::apps(Expr::bvar(5), vec![Expr::bvar(1), Expr::bvar(0)]),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        )
    }

    fn even_odd_mutual_block() -> MutualInductiveBlock {
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
                    Some(RecursorDecl::with_rules(
                        "Even.rec",
                        vec![],
                        even_recursor_type(),
                        RecursorRules::new(2, 6),
                    )),
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
                    Some(RecursorDecl::with_rules(
                        "Odd.rec",
                        vec![],
                        odd_recursor_type(),
                        RecursorRules::new(2, 6),
                    )),
                ),
            ],
        )
    }

    fn non_positive_even_odd_mutual_block() -> MutualInductiveBlock {
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

    fn negative_bad_inductive() -> InductiveDecl {
        InductiveDecl::new(
            "Bad",
            vec![],
            vec![],
            vec![],
            type0(),
            vec![ConstructorDecl::new(
                "Bad.mk",
                Expr::pi(
                    "f",
                    Expr::pi("_", Expr::konst("Bad", vec![]), nat()),
                    Expr::konst("Bad", vec![]),
                ),
            )],
            None,
        )
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
        let motive_ty = Expr::pi("_", unary(), Expr::sort(level.clone()));
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

    fn unary_inductive() -> InductiveDecl {
        InductiveDecl::new(
            "Unary",
            vec![],
            vec![],
            vec![],
            type0(),
            vec![
                ConstructorDecl::new("Unary.zero", unary()),
                ConstructorDecl::new("Unary.succ", Expr::pi("_", unary(), unary())),
            ],
            Some(RecursorDecl::new(
                "Unary.rec",
                vec!["u".to_owned()],
                unary_rec_type(Level::param("u")),
            )),
        )
    }

    fn bad_unary() -> Expr {
        Expr::konst("BadUnary", vec![])
    }

    fn bad_unary_zero() -> Expr {
        Expr::konst("BadUnary.zero", vec![])
    }

    fn bad_unary_succ(arg: Expr) -> Expr {
        Expr::app(Expr::konst("BadUnary.succ", vec![]), arg)
    }

    fn bad_unary_rec_type_missing_ih(level: Level) -> Expr {
        let motive_ty = Expr::pi("_", bad_unary(), Expr::sort(level));
        let z_ty = Expr::app(Expr::bvar(0), bad_unary_zero());
        let s_ty = Expr::pi(
            "n",
            bad_unary(),
            Expr::app(Expr::bvar(2), bad_unary_succ(Expr::bvar(0))),
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
                    Expr::pi("n", bad_unary(), Expr::app(Expr::bvar(3), Expr::bvar(0))),
                ),
            ),
        )
    }

    fn bad_unary_missing_ih_inductive() -> InductiveDecl {
        InductiveDecl::new(
            "BadUnary",
            vec![],
            vec![],
            vec![],
            type0(),
            vec![
                ConstructorDecl::new("BadUnary.zero", bad_unary()),
                ConstructorDecl::new("BadUnary.succ", Expr::pi("_", bad_unary(), bad_unary())),
            ],
            Some(RecursorDecl::new(
                "BadUnary.rec",
                vec!["u".to_owned()],
                bad_unary_rec_type_missing_ih(Level::param("u")),
            )),
        )
    }

    fn bad_minor() -> Expr {
        Expr::konst("BadMinor", vec![])
    }

    fn bad_minor_zero() -> Expr {
        Expr::konst("BadMinor.zero", vec![])
    }

    fn bad_minor_succ(arg: Expr) -> Expr {
        Expr::app(Expr::konst("BadMinor.succ", vec![]), arg)
    }

    fn bad_minor_rec_type_wrong_zero(level: Level) -> Expr {
        let motive_ty = Expr::pi("_", bad_minor(), Expr::sort(level));
        let z_ty = Expr::app(Expr::bvar(0), bad_minor_succ(bad_minor_zero()));
        let s_ty = Expr::pi(
            "n",
            bad_minor(),
            Expr::pi(
                "ih",
                Expr::app(Expr::bvar(2), Expr::bvar(0)),
                Expr::app(Expr::bvar(3), bad_minor_succ(Expr::bvar(1))),
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
                    Expr::pi("n", bad_minor(), Expr::app(Expr::bvar(3), Expr::bvar(0))),
                ),
            ),
        )
    }

    fn bad_minor_wrong_zero_inductive() -> InductiveDecl {
        InductiveDecl::new(
            "BadMinor",
            vec![],
            vec![],
            vec![],
            type0(),
            vec![
                ConstructorDecl::new("BadMinor.zero", bad_minor()),
                ConstructorDecl::new("BadMinor.succ", Expr::pi("_", bad_minor(), bad_minor())),
            ],
            Some(RecursorDecl::new(
                "BadMinor.rec",
                vec!["u".to_owned()],
                bad_minor_rec_type_wrong_zero(Level::param("u")),
            )),
        )
    }

    fn bad_list_constructor_param_inductive() -> InductiveDecl {
        let u = Level::param("u");
        InductiveDecl::new(
            "BadList",
            vec!["u".to_owned()],
            vec![Binder::new("A", Expr::sort(u.clone()))],
            vec![],
            u,
            vec![ConstructorDecl::new(
                "BadList.bad",
                Expr::app(Expr::konst("BadList", vec![type0()]), nat()),
            )],
            None,
        )
    }

    fn nested_bad(level: Level, arg: Expr) -> Expr {
        Expr::app(Expr::konst("NestedBad", vec![level]), arg)
    }

    fn nested_bad_inductive() -> InductiveDecl {
        let u = Level::param("u");
        InductiveDecl::new(
            "NestedBad",
            vec!["u".to_owned()],
            vec![Binder::new("A", Expr::sort(u.clone()))],
            vec![],
            u.clone(),
            vec![ConstructorDecl::new(
                "NestedBad.mk",
                Expr::pi(
                    "A",
                    Expr::sort(u.clone()),
                    Expr::pi(
                        "bad",
                        nested_bad(u.clone(), nested_bad(u.clone(), Expr::bvar(0))),
                        nested_bad(u, Expr::bvar(1)),
                    ),
                ),
            )],
            None,
        )
    }

    fn list_type(level: Level, elem: Expr) -> Expr {
        Expr::app(Expr::konst("List", vec![level]), elem)
    }

    fn option_type(level: Level, elem: Expr) -> Expr {
        Expr::app(Expr::konst("Option", vec![level]), elem)
    }

    fn option_inductive() -> InductiveDecl {
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

    fn prod_type(level: Level, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(Expr::konst("Prod", vec![level]), vec![lhs, rhs])
    }

    fn prod_inductive() -> InductiveDecl {
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

    fn rose_nested_list_inductive() -> InductiveDecl {
        let u = Level::param("u");
        rose_inductive_with_child(list_type(u.clone(), rose_type(u, Expr::bvar(1))))
    }

    fn rose_nested_option_prod_inductive() -> InductiveDecl {
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
                            "maybe",
                            option_type(u.clone(), rose_type(u.clone(), Expr::bvar(1))),
                            Expr::pi(
                                "pair",
                                prod_type(
                                    u.clone(),
                                    Expr::bvar(2),
                                    rose_type(u.clone(), Expr::bvar(2)),
                                ),
                                rose_type(u, Expr::bvar(3)),
                            ),
                        ),
                    ),
                ),
            )],
            None,
        )
    }

    fn rose_unknown_functor_inductive() -> InductiveDecl {
        let u = Level::param("u");
        rose_inductive_with_child(Expr::app(
            Expr::konst("Box", vec![u.clone()]),
            rose_type(u, Expr::bvar(1)),
        ))
    }

    fn rose_negative_arrow_inductive(result_ty: Expr) -> InductiveDecl {
        let u = Level::param("u");
        rose_inductive_with_child(Expr::pi(
            "_",
            rose_type(u.clone(), Expr::bvar(1)),
            result_ty,
        ))
    }

    fn rose_higher_order_negative_inductive() -> InductiveDecl {
        let u = Level::param("u");
        let inner = Expr::pi("_", rose_type(u.clone(), Expr::bvar(1)), Expr::bvar(2));
        rose_inductive_with_child(Expr::pi("_", inner, rose_type(u, Expr::bvar(2))))
    }

    fn vec_result_family_mismatch_inductive() -> InductiveDecl {
        let u = Level::param("u");
        InductiveDecl::new(
            "BadVecFamily",
            vec!["u".to_owned()],
            vec![Binder::new("A", Expr::sort(u))],
            vec![Binder::new("n", nat())],
            type0(),
            vec![ConstructorDecl::new(
                "BadVecFamily.mk",
                Expr::pi("A", Expr::sort(type0()), nat()),
            )],
            None,
        )
    }

    fn vec_result_param_mismatch_inductive() -> InductiveDecl {
        let u = Level::param("u");
        InductiveDecl::new(
            "BadVecParam",
            vec!["u".to_owned()],
            vec![Binder::new("A", Expr::sort(u.clone()))],
            vec![Binder::new("n", nat())],
            u.clone(),
            vec![ConstructorDecl::new(
                "BadVecParam.mk",
                Expr::pi(
                    "A",
                    Expr::sort(u.clone()),
                    Expr::pi(
                        "B",
                        Expr::sort(u.clone()),
                        Expr::apps(
                            Expr::konst("BadVecParam", vec![u]),
                            vec![Expr::bvar(0), nat_zero()],
                        ),
                    ),
                ),
            )],
            None,
        )
    }

    fn vec_result_bad_index_type_inductive() -> InductiveDecl {
        let u = Level::param("u");
        InductiveDecl::new(
            "BadVecIndex",
            vec!["u".to_owned()],
            vec![Binder::new("A", Expr::sort(u.clone()))],
            vec![Binder::new("n", nat())],
            u.clone(),
            vec![ConstructorDecl::new(
                "BadVecIndex.mk",
                Expr::pi(
                    "A",
                    Expr::sort(u.clone()),
                    Expr::apps(
                        Expr::konst("BadVecIndex", vec![u]),
                        vec![Expr::bvar(0), Expr::bvar(0)],
                    ),
                ),
            )],
            None,
        )
    }

    fn vec_negative_inductive() -> InductiveDecl {
        let u = Level::param("u");
        InductiveDecl::new(
            "BadVecNegative",
            vec!["u".to_owned()],
            vec![Binder::new("A", Expr::sort(u.clone()))],
            vec![Binder::new("n", nat())],
            u.clone(),
            vec![ConstructorDecl::new(
                "BadVecNegative.mk",
                Expr::pi(
                    "A",
                    Expr::sort(u.clone()),
                    Expr::pi(
                        "f",
                        Expr::pi(
                            "_",
                            Expr::apps(
                                Expr::konst("BadVecNegative", vec![u.clone()]),
                                vec![Expr::bvar(0), nat_zero()],
                            ),
                            nat(),
                        ),
                        Expr::apps(
                            Expr::konst("BadVecNegative", vec![u]),
                            vec![Expr::bvar(1), nat_zero()],
                        ),
                    ),
                ),
            )],
            None,
        )
    }

    fn extra_binder() -> Expr {
        Expr::konst("ExtraBinder", vec![])
    }

    fn extra_binder_zero() -> Expr {
        Expr::konst("ExtraBinder.zero", vec![])
    }

    fn extra_binder_succ(arg: Expr) -> Expr {
        Expr::app(Expr::konst("ExtraBinder.succ", vec![]), arg)
    }

    fn extra_binder_rec_type(level: Level) -> Expr {
        let motive_ty = Expr::pi("_", extra_binder(), Expr::sort(level.clone()));
        let z_ty = Expr::app(Expr::bvar(0), extra_binder_zero());
        let s_ty = Expr::pi(
            "n",
            extra_binder(),
            Expr::pi(
                "ih",
                Expr::app(Expr::bvar(2), Expr::bvar(0)),
                Expr::app(Expr::bvar(3), extra_binder_succ(Expr::bvar(1))),
            ),
        );
        let extra_motive_ty = Expr::pi("_", extra_binder(), Expr::sort(level));

        Expr::pi(
            "motive",
            motive_ty,
            Expr::pi(
                "z",
                z_ty,
                Expr::pi(
                    "s",
                    s_ty,
                    Expr::pi(
                        "n",
                        extra_binder(),
                        Expr::pi(
                            "extra",
                            extra_motive_ty,
                            Expr::app(Expr::bvar(0), Expr::bvar(1)),
                        ),
                    ),
                ),
            ),
        )
    }

    fn extra_binder_inductive() -> InductiveDecl {
        InductiveDecl::new(
            "ExtraBinder",
            vec![],
            vec![],
            vec![],
            type0(),
            vec![
                ConstructorDecl::new("ExtraBinder.zero", extra_binder()),
                ConstructorDecl::new(
                    "ExtraBinder.succ",
                    Expr::pi("_", extra_binder(), extra_binder()),
                ),
            ],
            Some(RecursorDecl::new(
                "ExtraBinder.rec",
                vec!["u".to_owned()],
                extra_binder_rec_type(Level::param("u")),
            )),
        )
    }

    fn bad_result() -> Expr {
        Expr::konst("BadResult", vec![])
    }

    fn bad_result_zero() -> Expr {
        Expr::konst("BadResult.zero", vec![])
    }

    fn bad_result_succ(arg: Expr) -> Expr {
        Expr::app(Expr::konst("BadResult.succ", vec![]), arg)
    }

    fn bad_result_rec_type(level: Level) -> Expr {
        let motive_ty = Expr::pi("_", bad_result(), Expr::sort(level));
        let z_ty = Expr::app(Expr::bvar(0), bad_result_zero());
        let s_ty = Expr::pi(
            "n",
            bad_result(),
            Expr::pi(
                "ih",
                Expr::app(Expr::bvar(2), Expr::bvar(0)),
                Expr::app(Expr::bvar(3), bad_result_succ(Expr::bvar(1))),
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
                    Expr::pi(
                        "n",
                        bad_result(),
                        Expr::app(Expr::bvar(3), bad_result_zero()),
                    ),
                ),
            ),
        )
    }

    fn bad_result_inductive() -> InductiveDecl {
        InductiveDecl::new(
            "BadResult",
            vec![],
            vec![],
            vec![],
            type0(),
            vec![
                ConstructorDecl::new("BadResult.zero", bad_result()),
                ConstructorDecl::new("BadResult.succ", Expr::pi("_", bad_result(), bad_result())),
            ],
            Some(RecursorDecl::new(
                "BadResult.rec",
                vec!["u".to_owned()],
                bad_result_rec_type(Level::param("u")),
            )),
        )
    }

    fn bad_prop() -> Expr {
        Expr::konst("BadProp", vec![])
    }

    fn bad_prop_intro() -> Expr {
        Expr::konst("BadProp.intro", vec![])
    }

    fn bad_prop_rec_type(level: Level) -> Expr {
        let motive_ty = Expr::pi("_", bad_prop(), Expr::sort(level));
        let intro_ty = Expr::app(Expr::bvar(0), bad_prop_intro());

        Expr::pi(
            "motive",
            motive_ty,
            Expr::pi(
                "intro",
                intro_ty,
                Expr::pi("p", bad_prop(), Expr::app(Expr::bvar(2), Expr::bvar(0))),
            ),
        )
    }

    fn bad_prop_large_elim_inductive() -> InductiveDecl {
        InductiveDecl::new(
            "BadProp",
            vec![],
            vec![],
            vec![],
            prop(),
            vec![ConstructorDecl::new("BadProp.intro", bad_prop())],
            Some(RecursorDecl::new(
                "BadProp.rec",
                vec!["u".to_owned()],
                bad_prop_rec_type(Level::param("u")),
            )),
        )
    }

    #[test]
    fn checks_polymorphic_id() {
        let mut env = Env::new();
        env.add_def(
            "id",
            vec!["u".to_owned()],
            id_type(),
            id_value(),
            Reducibility::Reducible,
        )
        .unwrap();
    }

    #[test]
    fn checks_polymorphic_const() {
        let mut env = Env::new();
        env.add_def(
            "const",
            vec!["u".to_owned(), "v".to_owned()],
            const_type(),
            const_value(),
            Reducibility::Reducible,
        )
        .unwrap();
    }

    #[test]
    fn rejects_unsatisfiable_declaration_universe_context() {
        let mut env = Env::new();
        let err = env
            .add_axiom_with_universe_constraints(
                "Bad",
                vec!["u".to_owned()],
                vec![UniverseConstraint::le(
                    Level::succ(Level::param("u")),
                    Level::param("u"),
                )],
                Expr::sort(Level::param("u")),
            )
            .unwrap_err();

        assert_eq!(err, Error::UnsatisfiableUniverseConstraints);
        assert!(env.decl("Bad").is_none());
    }

    #[test]
    fn const_inference_rejects_violating_universe_constraints() {
        let mut env = Env::new();
        env.add_axiom_with_universe_constraints(
            "Constrained",
            vec!["u".to_owned(), "v".to_owned()],
            vec![UniverseConstraint::le(Level::param("u"), Level::param("v"))],
            Expr::sort(Level::param("u")),
        )
        .unwrap();

        let err = env
            .infer(
                &Ctx::new(),
                &[],
                &Expr::konst(
                    "Constrained",
                    vec![Level::succ(Level::zero()), Level::zero()],
                ),
            )
            .unwrap_err();

        assert_eq!(
            err,
            Error::UniverseConstraintViolation {
                declaration: "Constrained".to_owned(),
                constraint: UniverseConstraint::le(Level::succ(Level::zero()), Level::zero()),
            }
        );
        assert_eq!(
            env.infer(
                &Ctx::new(),
                &[],
                &Expr::konst("Constrained", vec![Level::zero(), Level::zero()])
            )
            .unwrap(),
            Expr::sort(Level::zero())
        );
    }

    #[test]
    fn ambient_context_entails_constrained_const_instantiation() {
        let mut env = Env::new();
        env.add_axiom_with_universe_constraints(
            "Constrained",
            vec!["u".to_owned(), "v".to_owned()],
            vec![UniverseConstraint::le(Level::param("u"), Level::param("v"))],
            Expr::sort(Level::param("u")),
        )
        .unwrap();
        let ambient = UniverseContext::new(
            vec!["a".to_owned(), "b".to_owned()],
            vec![UniverseConstraint::le(Level::param("a"), Level::param("b"))],
        )
        .unwrap();

        let ty = env
            .infer_in_universe_context(
                &Ctx::new(),
                &ambient,
                &Expr::konst("Constrained", vec![Level::param("a"), Level::param("b")]),
            )
            .unwrap();

        assert_eq!(ty, Expr::sort(Level::param("a")));
    }

    #[test]
    fn inductive_constructors_inherit_parent_universe_constraints() {
        let mut env = Env::new();
        env.add_inductive(constrained_box_inductive()).unwrap();

        let err = env
            .infer(
                &Ctx::new(),
                &[],
                &Expr::konst("Box.mk", vec![Level::succ(Level::zero()), Level::zero()]),
            )
            .unwrap_err();

        assert_eq!(
            err,
            Error::UniverseConstraintViolation {
                declaration: "Box.mk".to_owned(),
                constraint: UniverseConstraint::le(Level::succ(Level::zero()), Level::zero()),
            }
        );
        assert!(env
            .infer(
                &Ctx::new(),
                &[],
                &Expr::konst("Box.mk", vec![Level::zero(), Level::zero()])
            )
            .is_ok());
    }

    #[test]
    fn inductive_rejects_constructor_field_above_declared_sort() {
        let family_sort = type0();
        let mut env = Env::new();
        let err = env
            .add_inductive(InductiveDecl::new(
                "Audit.Code",
                vec![],
                vec![],
                vec![],
                family_sort.clone(),
                vec![ConstructorDecl::new(
                    "Audit.Code.mk",
                    Expr::pi(
                        "A",
                        Expr::sort(family_sort.clone()),
                        Expr::konst("Audit.Code", vec![]),
                    ),
                )],
                None,
            ))
            .unwrap_err();

        assert_eq!(
            err,
            Error::ConstructorUniverseBoundViolation {
                inductive: "Audit.Code".to_owned(),
                constructor: "Audit.Code.mk".to_owned(),
                field_index: 0,
                field_level: Level::succ(family_sort.clone()),
                inductive_sort: family_sort,
            }
        );
        assert!(env.decl("Audit.Code").is_none());
        assert!(env.decl("Audit.Code.mk").is_none());
    }

    #[test]
    fn inductive_rejects_polymorphic_successor_field_bound() {
        let u = Level::param("u");
        let mut env = Env::new();
        let err = env
            .add_inductive(InductiveDecl::new(
                "Audit.PolyCode",
                vec!["u".to_owned()],
                vec![],
                vec![],
                u.clone(),
                vec![ConstructorDecl::new(
                    "Audit.PolyCode.mk",
                    Expr::pi(
                        "A",
                        Expr::sort(u.clone()),
                        Expr::konst("Audit.PolyCode", vec![u.clone()]),
                    ),
                )],
                None,
            ))
            .unwrap_err();

        assert_eq!(
            err,
            Error::ConstructorUniverseBoundViolation {
                inductive: "Audit.PolyCode".to_owned(),
                constructor: "Audit.PolyCode.mk".to_owned(),
                field_index: 0,
                field_level: Level::succ(u.clone()),
                inductive_sort: u,
            }
        );
    }

    #[test]
    fn inductive_excludes_uniform_parameters_but_bounds_stored_values() {
        let u = Level::param("u");
        let v = Level::param("v");
        let family_target = |name: &str, argument: Expr| {
            Expr::app(Expr::konst(name, vec![u.clone(), v.clone()]), argument)
        };
        let phantom = InductiveDecl::new(
            "Phantom",
            vec!["u".to_owned(), "v".to_owned()],
            vec![Binder::new("A", Expr::sort(u.clone()))],
            vec![],
            v.clone(),
            vec![ConstructorDecl::new(
                "Phantom.mk",
                Expr::pi(
                    "A",
                    Expr::sort(u.clone()),
                    family_target("Phantom", Expr::bvar(0)),
                ),
            )],
            None,
        );
        let make_store = |constraints: Vec<UniverseConstraint>| {
            InductiveDecl::new(
                "Store",
                vec!["u".to_owned(), "v".to_owned()],
                vec![Binder::new("A", Expr::sort(u.clone()))],
                vec![],
                v.clone(),
                vec![ConstructorDecl::new(
                    "Store.mk",
                    Expr::pi(
                        "A",
                        Expr::sort(u.clone()),
                        Expr::pi(
                            "value",
                            Expr::bvar(0),
                            family_target("Store", Expr::bvar(1)),
                        ),
                    ),
                )],
                None,
            )
            .with_universe_constraints(constraints)
        };

        let mut env = Env::new();
        env.add_inductive(phantom).unwrap();
        let err = env.add_inductive(make_store(vec![])).unwrap_err();
        assert!(matches!(
            err,
            Error::ConstructorUniverseBoundViolation {
                field_index: 0,
                field_level,
                inductive_sort,
                ..
            } if field_level == u && inductive_sort == v
        ));
        assert!(env.decl("Store").is_none());

        env.add_inductive(make_store(vec![UniverseConstraint::le(
            u.clone(),
            v.clone(),
        )]))
        .unwrap();
        assert!(env.decl("Store.mk").is_some());
    }

    #[test]
    fn inductive_accepts_constructor_field_bounded_by_max_sort() {
        let u = Level::param("u");
        let v = Level::param("v");
        let sort = Level::max(u.clone(), v.clone());
        let target = Expr::app(
            Expr::konst("MaxStore", vec![u.clone(), v.clone()]),
            Expr::bvar(1),
        );
        let data = InductiveDecl::new(
            "MaxStore",
            vec!["u".to_owned(), "v".to_owned()],
            vec![Binder::new("A", Expr::sort(u.clone()))],
            vec![],
            sort,
            vec![ConstructorDecl::new(
                "MaxStore.mk",
                Expr::pi("A", Expr::sort(u), Expr::pi("value", Expr::bvar(0), target)),
            )],
            None,
        );

        let mut env = Env::new();
        env.add_inductive(data).unwrap();
        assert!(env.decl("MaxStore.mk").is_some());
    }

    #[test]
    fn inductive_checks_dependent_fields_under_preceding_constructor_domains() {
        let type0 = type0();
        let type1 = Level::succ(type0.clone());
        let data = InductiveDecl::new(
            "DependentStore",
            vec![],
            vec![],
            vec![],
            type1,
            vec![ConstructorDecl::new(
                "DependentStore.mk",
                Expr::pi(
                    "A",
                    Expr::sort(type0),
                    Expr::pi(
                        "value",
                        Expr::bvar(0),
                        Expr::konst("DependentStore", vec![]),
                    ),
                ),
            )],
            None,
        );

        let mut env = Env::new();
        env.add_inductive(data).unwrap();
        assert!(env.decl("DependentStore.mk").is_some());
    }

    #[test]
    fn mutual_inductive_constructor_bounds_use_each_family_sort_atomically() {
        let type0 = type0();
        let type1 = Level::succ(type0.clone());
        let mut env = Env::new();
        env.add_mutual_inductive(MutualInductiveBlock::new(
            "AllowedMixedSorts",
            vec![],
            vec![
                InductiveDecl::new(
                    "High",
                    vec![],
                    vec![],
                    vec![],
                    type1,
                    vec![ConstructorDecl::new(
                        "High.mk",
                        Expr::pi("A", Expr::sort(type0.clone()), Expr::konst("High", vec![])),
                    )],
                    None,
                ),
                InductiveDecl::new(
                    "Proof",
                    vec![],
                    vec![],
                    vec![],
                    Level::zero(),
                    vec![ConstructorDecl::new(
                        "Proof.mk",
                        Expr::pi("A", Expr::sort(type0.clone()), Expr::konst("Proof", vec![])),
                    )],
                    None,
                ),
            ],
        ))
        .unwrap();
        assert!(env.decl("High.mk").is_some());
        assert!(env.decl("Proof.mk").is_some());

        let err = env
            .add_mutual_inductive(MutualInductiveBlock::new(
                "RejectedBlock",
                vec![],
                vec![
                    InductiveDecl::new(
                        "Low",
                        vec![],
                        vec![],
                        vec![],
                        type0.clone(),
                        vec![ConstructorDecl::new(
                            "Low.mk",
                            Expr::pi("A", Expr::sort(type0.clone()), Expr::konst("Low", vec![])),
                        )],
                        None,
                    ),
                    InductiveDecl::new(
                        "Other",
                        vec![],
                        vec![],
                        vec![],
                        type0.clone(),
                        vec![ConstructorDecl::new(
                            "Other.mk",
                            Expr::konst("Other", vec![]),
                        )],
                        None,
                    ),
                ],
            ))
            .unwrap_err();
        assert!(matches!(
            err,
            Error::ConstructorUniverseBoundViolation {
                inductive,
                constructor,
                field_index: 0,
                ..
            } if inductive == "Low" && constructor == "Low.mk"
        ));
        assert!(env.decl("Low").is_none());
        assert!(env.decl("Low.mk").is_none());
        assert!(env.decl("Other").is_none());
        assert!(env.decl("Other.mk").is_none());
    }

    #[test]
    fn mutual_inductive_rejects_unsatisfiable_universe_context() {
        let mut env = Env::new();
        let mut block = even_odd_mutual_block();
        block.universe_params = vec!["u".to_owned()];
        block.universe_constraints = vec![UniverseConstraint::le(
            Level::succ(Level::param("u")),
            Level::param("u"),
        )];

        let err = env.add_mutual_inductive(block).unwrap_err();

        assert_eq!(err, Error::UnsatisfiableUniverseConstraints);
        assert!(env.decl("Even").is_none());
        assert!(env.decl("Odd").is_none());
    }

    #[test]
    fn has_initial_nat_and_eq() {
        let env = Env::with_builtins().unwrap();
        assert!(matches!(env.decl("Nat"), Some(Decl::Inductive { .. })));
        assert!(matches!(
            env.decl("Nat.zero"),
            Some(Decl::Constructor { .. })
        ));
        assert!(matches!(env.decl("Nat.rec"), Some(Decl::Recursor { .. })));
        assert!(matches!(env.decl("Eq"), Some(Decl::Inductive { .. })));
        assert!(matches!(
            env.decl("Eq.refl"),
            Some(Decl::Constructor { .. })
        ));
        assert!(matches!(env.decl("Eq.rec"), Some(Decl::Axiom { .. })));

        let zero_eq_zero = eq(type0(), nat(), nat_zero(), nat_zero());
        let proof = eq_refl(type0(), nat(), nat_zero());
        env.check(&Ctx::new(), &[], &proof, &zero_eq_zero).unwrap();
    }

    #[test]
    fn checks_parameterized_list_inductive() {
        let mut env = Env::new();
        env.add_inductive(list_inductive()).unwrap();

        assert!(matches!(env.decl("List"), Some(Decl::Inductive { .. })));
        assert!(matches!(
            env.decl("List.cons"),
            Some(Decl::Constructor { .. })
        ));
    }

    #[test]
    fn checks_indexed_vec_and_fin_inductives() {
        let mut env = Env::with_builtins().unwrap();
        env.add_inductive(vec_inductive()).unwrap();
        env.add_inductive(fin_inductive()).unwrap();

        assert!(matches!(env.decl("Vec"), Some(Decl::Inductive { .. })));
        assert!(matches!(
            env.decl("Vec.cons"),
            Some(Decl::Constructor { .. })
        ));
        assert!(matches!(env.decl("Fin"), Some(Decl::Inductive { .. })));
        assert!(matches!(
            env.decl("Fin.succ"),
            Some(Decl::Constructor { .. })
        ));
    }

    #[test]
    fn mutual_inductive_even_odd_registers_generated_decls() {
        let mut env = Env::with_builtins().unwrap();
        env.add_mutual_inductive(even_odd_mutual_block()).unwrap();

        assert!(matches!(env.decl("Even"), Some(Decl::Inductive { .. })));
        assert!(matches!(
            env.decl("Even.zero"),
            Some(Decl::Constructor { .. })
        ));
        assert!(matches!(env.decl("Even.rec"), Some(Decl::Recursor { .. })));
        assert!(matches!(env.decl("Odd"), Some(Decl::Inductive { .. })));
        assert!(matches!(
            env.decl("Odd.succ"),
            Some(Decl::Constructor { .. })
        ));
        assert!(matches!(env.decl("Odd.rec"), Some(Decl::Recursor { .. })));
    }

    #[test]
    fn mutual_inductive_rejects_duplicate_generated_name() {
        let mut env = Env::with_builtins().unwrap();
        let mut block = even_odd_mutual_block();
        block.inductives[1].recursor.as_mut().unwrap().name = "Even.rec".to_owned();

        let err = env.add_mutual_inductive(block).unwrap_err();

        assert!(matches!(err, Error::DuplicateDecl(ref name) if name == "Even.rec"));
        assert!(env.decl("Even").is_none());
    }

    #[test]
    fn mutual_inductive_rejects_non_positive_occurrence() {
        let mut env = Env::with_builtins().unwrap();

        let err = env
            .add_mutual_inductive(non_positive_even_odd_mutual_block())
            .unwrap_err();

        assert!(matches!(err, Error::NonPositiveOccurrence { .. }));
        assert!(env.decl("Even").is_none());
    }

    #[test]
    fn mutual_iota_reduces_even_odd_like_reference_checker() {
        let mut env = Env::with_builtins().unwrap();
        env.add_mutual_inductive(even_odd_mutual_block()).unwrap();

        let m_even = Expr::lam(
            "n",
            nat(),
            Expr::lam("_", even_type(Expr::bvar(0)), even_type(Expr::bvar(1))),
        );
        let m_odd = Expr::lam(
            "n",
            nat(),
            Expr::lam("_", odd_type(Expr::bvar(0)), odd_type(Expr::bvar(1))),
        );
        let z = even_zero();
        let even_step = Expr::lam(
            "n",
            nat(),
            Expr::lam(
                "h",
                odd_type(Expr::bvar(0)),
                Expr::lam(
                    "_ih",
                    odd_type(Expr::bvar(1)),
                    even_succ(Expr::bvar(2), Expr::bvar(1)),
                ),
            ),
        );
        let odd_step = Expr::lam(
            "n",
            nat(),
            Expr::lam(
                "h",
                even_type(Expr::bvar(0)),
                Expr::lam(
                    "_ih",
                    even_type(Expr::bvar(1)),
                    odd_succ(Expr::bvar(2), Expr::bvar(1)),
                ),
            ),
        );
        let odd_one = odd_succ(nat_zero(), even_zero());
        let term = Expr::apps(
            Expr::konst("Odd.rec", vec![]),
            vec![
                m_even.clone(),
                m_odd.clone(),
                z.clone(),
                even_step,
                odd_step,
                nat_succ(nat_zero()),
                odd_one.clone(),
            ],
        );

        env.check(&Ctx::new(), &[], &term, &odd_type(nat_succ(nat_zero())))
            .unwrap();
        assert!(env.is_defeq(&Ctx::new(), &[], &term, &odd_one).unwrap());
    }

    #[test]
    fn rejects_indexed_inductive_constructor_result_failures_deterministically() {
        let mut env = Env::with_builtins().unwrap();
        let family = env
            .add_inductive(vec_result_family_mismatch_inductive())
            .unwrap_err();
        assert!(matches!(family, Error::BadConstructorResult { .. }));

        let param = env
            .add_inductive(vec_result_param_mismatch_inductive())
            .unwrap_err();
        assert!(matches!(param, Error::BadConstructorResult { .. }));

        let index = env
            .add_inductive(vec_result_bad_index_type_inductive())
            .unwrap_err();
        assert!(matches!(index, Error::TypeMismatch { .. }));

        let negative = env.add_inductive(vec_negative_inductive()).unwrap_err();
        assert!(matches!(negative, Error::NonPositiveOccurrence { .. }));
    }

    #[test]
    fn rejects_negative_inductive_occurrence() {
        let mut env = Env::with_builtins().unwrap();
        let err = env.add_inductive(negative_bad_inductive()).unwrap_err();

        assert!(matches!(err, Error::NonPositiveOccurrence { .. }));
        assert!(env.decl("Bad").is_none());
    }

    #[test]
    fn rejects_recursor_minor_missing_recursive_ih() {
        let mut env = Env::new();
        let err = env
            .add_inductive(bad_unary_missing_ih_inductive())
            .unwrap_err();

        assert!(matches!(err, Error::InvalidInductive(_)));
        assert!(env.decl("BadUnary").is_none());
    }

    #[test]
    fn rejects_recursor_minor_with_wrong_constructor_target() {
        let mut env = Env::new();
        let err = env
            .add_inductive(bad_minor_wrong_zero_inductive())
            .unwrap_err();

        assert!(matches!(err, Error::InvalidInductive(_)));
        assert!(env.decl("BadMinor").is_none());
    }

    #[test]
    fn rejects_constructor_result_with_wrong_params() {
        let mut env = Env::with_builtins().unwrap();
        let err = env
            .add_inductive(bad_list_constructor_param_inductive())
            .unwrap_err();

        assert!(matches!(err, Error::BadConstructorResult { .. }));
        assert!(env.decl("BadList").is_none());
    }

    #[test]
    fn rejects_nested_recursive_occurrence_in_direct_field() {
        let mut env = Env::new();
        let err = env.add_inductive(nested_bad_inductive()).unwrap_err();

        assert!(matches!(err, Error::NonPositiveOccurrence { .. }));
        assert!(env.decl("NestedBad").is_none());
    }

    #[test]
    fn positivity_accepts_approved_nested_list_rose_occurrence() {
        let mut env = Env::new();
        env.add_inductive(list_inductive()).unwrap();
        env.add_inductive(rose_nested_list_inductive()).unwrap();

        assert!(matches!(env.decl("Rose"), Some(Decl::Inductive { .. })));
    }

    #[test]
    fn positivity_accepts_approved_nested_option_and_prod_occurrences() {
        let mut env = Env::new();
        env.add_inductive(option_inductive()).unwrap();
        env.add_inductive(prod_inductive()).unwrap();
        env.add_inductive(rose_nested_option_prod_inductive())
            .unwrap();

        assert!(matches!(env.decl("Rose"), Some(Decl::Inductive { .. })));
    }

    #[test]
    fn positivity_rejects_unknown_nested_functor_rose_occurrence() {
        let u = Level::param("u");
        let mut env = Env::new();
        env.add_axiom(
            "Box",
            vec!["u".to_owned()],
            Expr::pi("A", Expr::sort(u.clone()), Expr::sort(u)),
        )
        .unwrap();
        let err = env
            .add_inductive(rose_unknown_functor_inductive())
            .unwrap_err();

        assert!(matches!(err, Error::NonPositiveOccurrence { .. }));
        assert!(env.decl("Rose").is_none());
    }

    #[test]
    fn positivity_rejects_name_only_fake_approved_functor() {
        let mut env = Env::with_builtins().unwrap();
        env.add_inductive(negative_param_list_inductive()).unwrap();
        let err = env
            .add_inductive(rose_nested_list_inductive().with_universe_constraints(vec![
                UniverseConstraint::le(type0(), Level::param("u")),
            ]))
            .unwrap_err();

        assert!(matches!(err, Error::NonPositiveOccurrence { .. }));
    }

    #[test]
    fn positivity_rejects_negative_arrow_recursive_occurrences() {
        let u = Level::param("u");
        let mut env = Env::new();
        let err = env
            .add_inductive(rose_negative_arrow_inductive(Expr::bvar(2)))
            .unwrap_err();
        assert!(matches!(err, Error::NonPositiveOccurrence { .. }));

        let mut env = Env::new();
        let err = env
            .add_inductive(rose_negative_arrow_inductive(rose_type(u, Expr::bvar(2))))
            .unwrap_err();
        assert!(matches!(err, Error::NonPositiveOccurrence { .. }));
    }

    #[test]
    fn positivity_rejects_higher_order_negative_occurrence() {
        let mut env = Env::new();
        let err = env
            .add_inductive(rose_higher_order_negative_inductive())
            .unwrap_err();

        assert!(matches!(err, Error::NonPositiveOccurrence { .. }));
    }

    #[test]
    fn positivity_policy_rejects_prop_large_elimination() {
        let mut env = Env::new();
        let err = env
            .add_inductive(bad_prop_large_elim_inductive())
            .unwrap_err();

        assert!(matches!(err, Error::InvalidInductive(_)));
        assert!(env.decl("BadProp").is_none());
    }

    #[test]
    fn rejects_recursor_with_binder_after_major_premise() {
        let mut env = Env::new();
        let err = env.add_inductive(extra_binder_inductive()).unwrap_err();

        assert!(matches!(err, Error::InvalidInductive(_)));
        assert!(env.decl("ExtraBinder").is_none());
    }

    #[test]
    fn rejects_recursor_result_not_targeting_major_premise() {
        let mut env = Env::new();
        let err = env.add_inductive(bad_result_inductive()).unwrap_err();

        assert!(matches!(err, Error::InvalidInductive(_)));
        assert!(env.decl("BadResult").is_none());
    }

    #[test]
    fn rejects_prop_recursor_large_elimination() {
        let mut env = Env::new();
        let err = env
            .add_inductive(bad_prop_large_elim_inductive())
            .unwrap_err();

        assert!(matches!(err, Error::InvalidInductive(_)));
        assert!(env.decl("BadProp").is_none());
    }

    #[test]
    fn reduces_nat_rec_zero() {
        let env = Env::with_builtins().unwrap();
        let motive = Expr::lam("_", nat(), nat());
        let step = Expr::lam("_", nat(), Expr::lam("ih", nat(), nat_succ(Expr::bvar(0))));
        let term = Expr::apps(
            Expr::konst("Nat.rec", vec![type0()]),
            vec![motive, nat_zero(), step, nat_zero()],
        );
        let reduced = env.whnf(&Ctx::new(), &[], &term).unwrap();
        assert!(env
            .is_defeq(&Ctx::new(), &[], &reduced, &nat_zero())
            .unwrap());
    }

    #[test]
    fn reduces_nat_rec_succ() {
        let env = Env::with_builtins().unwrap();
        let motive = Expr::lam("_", nat(), nat());
        let step = Expr::lam("_", nat(), Expr::lam("ih", nat(), nat_succ(Expr::bvar(0))));
        let term = Expr::apps(
            Expr::konst("Nat.rec", vec![type0()]),
            vec![motive, nat_zero(), step, nat_succ(nat_zero())],
        );
        let expected = nat_succ(nat_zero());

        assert!(env.is_defeq(&Ctx::new(), &[], &term, &expected).unwrap());
    }

    #[test]
    fn generic_iota_reduces_non_nat_recursor() {
        let mut env = Env::new();
        env.add_inductive(unary_inductive()).unwrap();
        let motive = Expr::lam("_", unary(), unary());
        let step = Expr::lam(
            "_",
            unary(),
            Expr::lam("ih", unary(), unary_succ(Expr::bvar(0))),
        );
        let term = Expr::apps(
            Expr::konst("Unary.rec", vec![type0()]),
            vec![motive, unary_zero(), step, unary_succ(unary_zero())],
        );
        let expected = unary_succ(unary_zero());

        assert!(env.is_defeq(&Ctx::new(), &[], &term, &expected).unwrap());
    }

    #[test]
    fn checks_let_and_zeta_reduction() {
        let env = Env::with_builtins().unwrap();
        let term = Expr::let_in("x", nat(), nat_zero(), Expr::bvar(0));

        env.check(&Ctx::new(), &[], &term, &nat()).unwrap();
        let reduced = env.whnf(&Ctx::new(), &[], &term).unwrap();
        assert!(env
            .is_defeq(&Ctx::new(), &[], &reduced, &nat_zero())
            .unwrap());
    }

    #[test]
    fn rejects_ill_typed_application() {
        let env = Env::with_builtins().unwrap();
        let bad = Expr::app(nat_zero(), nat_zero());

        assert!(matches!(
            env.infer(&Ctx::new(), &[], &bad),
            Err(Error::ExpectedPi { .. })
        ));
    }

    #[test]
    fn checks_nat_add_and_add_zero() {
        let mut env = Env::with_builtins().unwrap();
        env.add_def(
            "Nat.add",
            vec![],
            nat_add_type(),
            nat_add_value(),
            Reducibility::Reducible,
        )
        .unwrap();
        env.add_theorem("Nat.add_zero", vec![], add_zero_type(), add_zero_value())
            .unwrap();
    }
}

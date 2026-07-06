use crate::{
    decl::{Binder, ConstructorDecl, InductiveDecl, RecursorDecl},
    expr::Expr,
    level::Level,
};

pub fn prop() -> Level {
    Level::zero()
}

pub fn type0() -> Level {
    Level::succ(prop())
}

pub fn nat() -> Expr {
    Expr::konst("Nat", vec![])
}

pub fn nat_zero() -> Expr {
    Expr::konst("Nat.zero", vec![])
}

pub fn nat_succ(arg: Expr) -> Expr {
    Expr::app(Expr::konst("Nat.succ", vec![]), arg)
}

pub fn eq(level: Level, ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(Expr::konst("Eq", vec![level]), vec![ty, lhs, rhs])
}

pub fn eq_refl(level: Level, ty: Expr, value: Expr) -> Expr {
    Expr::apps(Expr::konst("Eq.refl", vec![level]), vec![ty, value])
}

pub fn eq_type(level: Level) -> Expr {
    Expr::pi(
        "A",
        Expr::sort(level),
        Expr::pi(
            "lhs",
            Expr::bvar(0),
            Expr::pi("rhs", Expr::bvar(1), Expr::sort(prop())),
        ),
    )
}

pub fn eq_refl_type(level: Level) -> Expr {
    Expr::pi(
        "A",
        Expr::sort(level.clone()),
        Expr::pi(
            "x",
            Expr::bvar(0),
            eq(level, Expr::bvar(1), Expr::bvar(0), Expr::bvar(0)),
        ),
    )
}

pub fn eq_rec_type(value_level: Level, motive_level: Level) -> Expr {
    let a_sort_level = value_level.clone();
    let motive_ty = Expr::pi(
        "b",
        Expr::bvar(1),
        Expr::pi(
            "h",
            eq(
                value_level.clone(),
                Expr::bvar(2),
                Expr::bvar(1),
                Expr::bvar(0),
            ),
            Expr::sort(motive_level),
        ),
    );
    let refl_proof = eq_refl(value_level.clone(), Expr::bvar(2), Expr::bvar(1));
    let minor_ty = Expr::apps(Expr::bvar(0), vec![Expr::bvar(1), refl_proof]);
    let major_ty = eq(value_level, Expr::bvar(4), Expr::bvar(3), Expr::bvar(0));
    let result_ty = Expr::apps(Expr::bvar(3), vec![Expr::bvar(1), Expr::bvar(0)]);

    Expr::pi(
        "A",
        Expr::sort(a_sort_level),
        Expr::pi(
            "a",
            Expr::bvar(0),
            Expr::pi(
                "motive",
                motive_ty,
                Expr::pi(
                    "minor",
                    minor_ty,
                    Expr::pi("b", Expr::bvar(3), Expr::pi("h", major_ty, result_ty)),
                ),
            ),
        ),
    )
}

pub fn nat_rec_type(level: Level) -> Expr {
    let motive_ty = Expr::pi("_", nat(), Expr::sort(level.clone()));
    let z_ty = Expr::app(Expr::bvar(0), nat_zero());

    let s_ty = Expr::pi(
        "n",
        nat(),
        Expr::pi(
            "ih",
            Expr::app(Expr::bvar(2), Expr::bvar(0)),
            Expr::app(Expr::bvar(3), nat_succ(Expr::bvar(1))),
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
                Expr::pi("n", nat(), Expr::app(Expr::bvar(3), Expr::bvar(0))),
            ),
        ),
    )
}

pub fn nat_inductive() -> InductiveDecl {
    InductiveDecl::new(
        "Nat",
        vec![],
        vec![],
        vec![],
        type0(),
        vec![
            ConstructorDecl::new("Nat.zero", nat()),
            ConstructorDecl::new("Nat.succ", Expr::pi("_", nat(), nat())),
        ],
        Some(RecursorDecl::new(
            "Nat.rec",
            vec!["u".to_owned()],
            nat_rec_type(Level::param("u")),
        )),
    )
}

pub fn eq_inductive() -> InductiveDecl {
    InductiveDecl::new(
        "Eq",
        vec!["u".to_owned()],
        vec![
            Binder::new("A", Expr::sort(Level::param("u"))),
            Binder::new("lhs", Expr::bvar(0)),
        ],
        vec![Binder::new("rhs", Expr::bvar(1))],
        prop(),
        vec![ConstructorDecl::new(
            "Eq.refl",
            eq_refl_type(Level::param("u")),
        )],
        None,
    )
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ApprovedNestedFunctor {
    pub name: &'static str,
    pub arity: usize,
    pub positive_args: &'static [usize],
}

const UNARY_POSITIVE_ARGS: &[usize] = &[0];
const BINARY_POSITIVE_ARGS: &[usize] = &[0, 1];

pub const APPROVED_NESTED_FUNCTORS: &[ApprovedNestedFunctor] = &[
    ApprovedNestedFunctor {
        name: "List",
        arity: 1,
        positive_args: UNARY_POSITIVE_ARGS,
    },
    ApprovedNestedFunctor {
        name: "Option",
        arity: 1,
        positive_args: UNARY_POSITIVE_ARGS,
    },
    ApprovedNestedFunctor {
        name: "Prod",
        arity: 2,
        positive_args: BINARY_POSITIVE_ARGS,
    },
];

pub fn approved_nested_functor(name: &str, arity: usize) -> Option<&'static ApprovedNestedFunctor> {
    APPROVED_NESTED_FUNCTORS
        .iter()
        .find(|functor| functor.name == name && functor.arity == arity)
}

use std::sync::Arc;

use crate::{
    error::{Error, Result},
    expr::Expr,
    subst::shift,
};

#[derive(Clone, Debug, Default)]
pub struct Ctx {
    locals: Vec<Arc<LocalDecl>>,
}

#[derive(Debug)]
pub(crate) struct LocalDecl {
    ty: Expr,
}

impl LocalDecl {
    pub(crate) fn memo_expressions(&self) -> impl Iterator<Item = &Expr> {
        std::iter::once(&self.ty)
    }
}

impl Ctx {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn push_assumption(&mut self, _name: impl Into<String>, ty: Expr) {
        self.locals.push(Arc::new(LocalDecl { ty }));
    }

    fn lookup(&self, index: u32) -> Result<&LocalDecl> {
        let index = index as usize;
        if index >= self.locals.len() {
            return Err(Error::InvalidBVar(index as u32));
        }
        Ok(&self.locals[self.locals.len() - 1 - index])
    }

    pub(crate) fn lookup_type(&self, index: u32) -> Result<Expr> {
        shift(&self.lookup(index)?.ty, index as i32 + 1, 0)
    }

    pub(crate) fn ensure_bound(&self, index: u32) -> Result<()> {
        self.lookup(index).map(|_| ())
    }

    pub(crate) fn memo_locals(&self) -> &[Arc<LocalDecl>] {
        &self.locals
    }
}

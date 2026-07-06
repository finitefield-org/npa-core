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
struct LocalDecl {
    ty: Expr,
    value: Option<Expr>,
}

impl Ctx {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn push_assumption(&mut self, _name: impl Into<String>, ty: Expr) {
        self.locals.push(Arc::new(LocalDecl { ty, value: None }));
    }

    pub fn push_definition(&mut self, _name: impl Into<String>, ty: Expr, value: Expr) {
        self.locals.push(Arc::new(LocalDecl {
            ty,
            value: Some(value),
        }));
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

    pub(crate) fn lookup_value(&self, index: u32) -> Result<Option<Expr>> {
        self.lookup(index)?
            .value
            .as_ref()
            .map(|value| shift(value, index as i32 + 1, 0))
            .transpose()
    }
}

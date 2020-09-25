use cst_source::Span;
use num::{BigInt, BigRational};
use std::rc::Rc;

#[derive(Debug, Clone)]
pub enum Expr {
    IntLiteral(Rc<BigInt>),
    FloatLiteral(Rc<BigRational>),
    Ident(Span),
    Tuple(Vec<Expr>),
    Lambda(Vec<Span>, Box<Expr>),
    Apply(Box<Expr>, Box<Expr>),
    Hole,
}

#[derive(Debug, Clone)]
pub struct Binding {
    pub name: Span,
    pub value: Expr,
}

#[derive(Debug, Clone)]
pub struct Ast {
    pub bindings: Vec<Binding>,
}

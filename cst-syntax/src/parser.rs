use crate::{
    ast::{Ast, Binding, Expr},
    lexer::Lexer,
    token::{TokenData, TokenKind, TokenPattern},
};
use cst_error::Emitter;
use cst_source::Src;

#[derive(Debug)]
pub struct Parser<'emitter, 'diagnostics> {
    lexer: Lexer<'emitter, 'diagnostics>,
}

impl<'emitter, 'diagnostics> Parser<'emitter, 'diagnostics> {
    pub fn new(
        src: Src,
        err_emitter: &'emitter mut Emitter<'diagnostics>,
    ) -> Self {
        Self { lexer: Lexer::new(src, err_emitter) }
    }

    pub fn parse(mut self) -> Ast {
        let mut ast = Ast { bindings: Vec::new() };
        while !self.lexer.is_eof() {
            if let Some(binding) = self.parse_binding(&TokenKind::Eof) {
                ast.bindings.push(binding);
            }
        }
        ast
    }

    pub fn parse_binding<P>(&mut self, end_pattern: P) -> Option<Binding>
    where
        P: TokenPattern,
    {
        self.lexer.expect(TokenKind::Val)?;
        let ident = self.lexer.expect(TokenKind::Ident)?;
        self.lexer.expect(TokenKind::Equals);
        let expr_pat: &[&dyn TokenPattern] = &[&TokenKind::Val, &end_pattern];
        let expr = self.parse_expr(expr_pat);
        Some(Binding { name: ident.span, value: expr })
    }

    pub fn parse_expr<P>(&mut self, end_pattern: P) -> Expr
    where
        P: TokenPattern,
    {
        let mut stack = Vec::new();
        let expected_pat: &[_] =
            &[TokenKind::IntLiteral, TokenKind::FloatLiteral, TokenKind::Ident];
        while !self.lexer.check(&end_pattern) {
            if let Some(tok) = self.lexer.expect(expected_pat) {
                match &tok.data {
                    TokenData::Ident => stack.push(Expr::Ident(tok.span)),
                    TokenData::IntLiteral(lit) => {
                        stack.push(Expr::IntLiteral(lit.clone()))
                    },
                    TokenData::FloatLiteral(lit) => {
                        stack.push(Expr::FloatLiteral(lit.clone()))
                    },
                    _ => unreachable!(),
                }
            }
        }
        stack.pop().unwrap()
    }
}

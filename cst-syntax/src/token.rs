use cst_fmt::SeqFmt;
use cst_source::Span;
use num::{BigInt, BigRational};
use std::fmt::{self, Write};

/// A kind of token.
#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum TokenKind {
    /// Identifier.
    Ident,
    /// Operator.
    Operator,
    /// Comma ,
    Comma,
    /// Opening parenthesis (
    OpenParen,
    /// Closing parenthesis )
    CloseParen,
    /// =>
    ThinArrow,
    /// ->
    FatArrow,
    /// =
    Equals,
    /// if
    If,
    /// Integer literal.
    IntLiteral(BigInt),
    /// Float ltieral.
    FloatLiteral(BigRational),
    /// End of file.
    Eof,
}

impl fmt::Display for TokenKind {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.write_str(match self {
            TokenKind::Ident => "identifier",
            TokenKind::Operator => "oerator",
            TokenKind::Comma => "comma",
            TokenKind::OpenParen => "opening parenthesis",
            TokenKind::CloseParen => "closing parenthesis",
            TokenKind::ThinArrow => "thin arrow",
            TokenKind::FatArrow => "fat arrow",
            TokenKind::Equals => "equals",
            TokenKind::If => "if",
            TokenKind::IntLiteral(_) => "integer literal",
            TokenKind::FloatLiteral(_) => "float literal",
            TokenKind::Eof => "end of input",
        })
    }
}

/// A complete token.
#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    /// The kind of the token.
    pub kind: TokenKind,
    /// The span this token reaches.
    pub span: Span,
}

impl fmt::Display for Token {
    fn fmt(&self, fmtr: &mut fmt::Formatter) -> fmt::Result {
        write!(fmtr, "{} (`{}`) {}", self.kind, self.span.as_str(), self.span)
    }
}

/// A generic token pattern, used for parsing errors.
pub trait TokenPattern {
    /// Is this token valid for this pattern?
    fn test(&self, tok: &Token) -> bool;

    /// Renders this token pattern for errors.
    fn render<'buf, 'obj, 'sep, 'sep_lim>(
        &self,
        pieces: &mut SeqFmt<'buf, 'obj, 'sep, 'sep_lim>,
    ) -> fmt::Result;
}

impl TokenPattern for TokenKind {
    fn test(&self, tok: &Token) -> bool {
        tok.kind == *self
    }

    fn render(&self, pieces: &mut SeqFmt) -> fmt::Result {
        pieces.mark_elem_start()?;
        write!(pieces, "{}", self)
    }
}

impl<'content> TokenPattern for (TokenKind, &'content str) {
    fn test(&self, tok: &Token) -> bool {
        tok.kind == self.0 && tok.span.as_str() == self.1
    }

    fn render(&self, pieces: &mut SeqFmt) -> fmt::Result {
        pieces.mark_elem_start()?;
        write!(pieces, "{} (`{}`)", self.0, self.1)
    }
}

impl<P> TokenPattern for [P]
where
    P: TokenPattern,
{
    fn test(&self, tok: &Token) -> bool {
        for pat in self {
            if pat.test(tok) {
                return true;
            }
        }

        false
    }

    fn render(&self, pieces: &mut SeqFmt) -> fmt::Result {
        for pat in self {
            pat.render(pieces)?;
        }

        Ok(())
    }
}

impl<'pat, P> TokenPattern for &'pat P
where
    P: TokenPattern + ?Sized,
{
    fn test(&self, tok: &Token) -> bool {
        (**self).test(tok)
    }

    fn render(&self, pieces: &mut SeqFmt) -> fmt::Result {
        (**self).render(pieces)
    }
}

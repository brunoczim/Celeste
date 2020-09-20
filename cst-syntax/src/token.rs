use cst_fmt::SeqFmt;
use cst_source::Span;
use num::{BigInt, BigRational};
use std::fmt::{self, Write};

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum TokenKind {
    Ident,
    Operator,
    Comma,
    OpenParen,
    CloseParen,
    Eof,
    ThinArrow,
    FatArrow,
    Equals,
    If,
    IntLiteral(BigInt),
    FloatLiteral(BigRational),
}

impl fmt::Display for TokenKind {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.write_str(match self {
            TokenKind::Ident => "identifier",
            TokenKind::Operator => "oerator",
            TokenKind::Comma => "comma",
            TokenKind::OpenParen => "opening parenthesis",
            TokenKind::CloseParen => "closing parenthesis",
            TokenKind::Eof => "end of input",
            TokenKind::ThinArrow => "thin arrow",
            TokenKind::FatArrow => "fat arrow",
            TokenKind::Equals => "equals",
            TokenKind::If => "if",
            TokenKind::IntLiteral(_) => "integer literal",
            TokenKind::FloatLiteral(_) => "float literal",
        })
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

impl fmt::Display for Token {
    fn fmt(&self, fmtr: &mut fmt::Formatter) -> fmt::Result {
        write!(fmtr, "{} (`{}`) {}", self.kind, self.span.as_str(), self.span)
    }
}

pub trait TokenPattern {
    fn test(&self, tok: &Token) -> bool;

    fn render<'buf>(&self, pieces: &mut SeqFmt<'buf>) -> fmt::Result;
}

impl TokenPattern for TokenKind {
    fn test(&self, tok: &Token) -> bool {
        tok.kind == *self
    }

    fn render<'buf>(&self, pieces: &mut SeqFmt<'buf>) -> fmt::Result {
        pieces.mark_start()?;
        write!(pieces, "{}", self)
    }
}

impl<'content> TokenPattern for (TokenKind, &'content str) {
    fn test(&self, tok: &Token) -> bool {
        tok.kind == self.0 && tok.span.as_str() == self.1
    }

    fn render<'buf>(&self, pieces: &mut SeqFmt<'buf>) -> fmt::Result {
        pieces.mark_start()?;
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

    fn render<'buf>(&self, pieces: &mut SeqFmt<'buf>) -> fmt::Result {
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

    fn render<'buf>(&self, pieces: &mut SeqFmt<'buf>) -> fmt::Result {
        (**self).render(pieces)
    }
}

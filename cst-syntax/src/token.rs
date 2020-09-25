use cst_fmt::SeqFmt;
use cst_source::Span;
use num::{BigInt, BigRational};
use std::{
    fmt::{self, Write},
    rc::Rc,
};

/// A kind of token.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
    /// val
    Val,
    /// Integer literal.
    IntLiteral,
    /// Float ltieral.
    FloatLiteral,
    /// End of file.
    Eof,
}

impl fmt::Display for TokenKind {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.pad(match self {
            TokenKind::Ident => "identifier",
            TokenKind::Operator => "oerator",
            TokenKind::Comma => "comma",
            TokenKind::OpenParen => "opening parenthesis",
            TokenKind::CloseParen => "closing parenthesis",
            TokenKind::ThinArrow => "thin arrow",
            TokenKind::FatArrow => "fat arrow",
            TokenKind::Equals => "equals",
            TokenKind::If => "if",
            TokenKind::Val => "val",
            TokenKind::IntLiteral => "integer literal",
            TokenKind::FloatLiteral => "float literal",
            TokenKind::Eof => "end of input",
        })
    }
}

/// A kind of token.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TokenData {
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
    /// val
    Val,
    /// Integer literal.
    IntLiteral(Rc<BigInt>),
    /// Float ltieral.
    FloatLiteral(Rc<BigRational>),
    /// End of file.
    Eof,
}

impl TokenData {
    pub fn int(int: i128) -> Self {
        TokenData::IntLiteral(Rc::new(BigInt::from(int)))
    }

    pub fn float(numer: i128, denom: i128) -> Self {
        TokenData::FloatLiteral(Rc::new(BigRational::new(
            BigInt::from(numer),
            BigInt::from(denom),
        )))
    }

    pub fn kind(&self) -> TokenKind {
        match self {
            TokenData::Ident => TokenKind::Ident,
            TokenData::Operator => TokenKind::Operator,
            TokenData::Comma => TokenKind::Comma,
            TokenData::OpenParen => TokenKind::OpenParen,
            TokenData::CloseParen => TokenKind::CloseParen,
            TokenData::ThinArrow => TokenKind::ThinArrow,
            TokenData::FatArrow => TokenKind::FatArrow,
            TokenData::Equals => TokenKind::Equals,
            TokenData::If => TokenKind::If,
            TokenData::Val => TokenKind::Val,
            TokenData::IntLiteral(_) => TokenKind::IntLiteral,
            TokenData::FloatLiteral(_) => TokenKind::FloatLiteral,
            TokenData::Eof => TokenKind::Eof,
        }
    }
}

impl fmt::Display for TokenData {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.kind(), fmt)
    }
}

/// A complete token.
#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    /// The data of the token.
    pub data: TokenData,
    /// The span this token reaches.
    pub span: Span,
}

impl fmt::Display for Token {
    fn fmt(&self, fmtr: &mut fmt::Formatter) -> fmt::Result {
        write!(fmtr, "{} (`{}`) {}", self.data, self.span.as_str(), self.span)
    }
}

/// A generic token pattern, used for parsing errors.
pub trait TokenPattern {
    /// Is this token valid for this pattern?
    fn test(&self, tok: &Token) -> bool;

    /// Renders this token pattern for errors.
    fn render<'buf, 'obj, 'sep, 'sep_lim>(
        &self,
        seq_fmt: &mut SeqFmt<'buf, 'obj, 'sep, 'sep_lim>,
    ) -> fmt::Result;

    fn to_boxed_dyn(&self) -> Box<dyn TokenPattern>;
}

impl TokenPattern for TokenKind {
    fn test(&self, tok: &Token) -> bool {
        tok.data.kind() == *self
    }

    fn render(&self, seq_fmt: &mut SeqFmt) -> fmt::Result {
        seq_fmt.mark_elem_start()?;
        write!(seq_fmt, "{}", self)
    }

    fn to_boxed_dyn(&self) -> Box<dyn TokenPattern> {
        Box::new(self.clone())
    }
}

impl<'content> TokenPattern for (TokenKind, String) {
    fn test(&self, tok: &Token) -> bool {
        (self.0, self.1.as_str()).test(tok)
    }

    fn render(&self, seq_fmt: &mut SeqFmt) -> fmt::Result {
        (self.0, self.1.as_str()).render(seq_fmt)
    }

    fn to_boxed_dyn(&self) -> Box<dyn TokenPattern> {
        Box::new((self.0, self.1.clone()))
    }
}

impl<'content> TokenPattern for (TokenKind, &'content str) {
    fn test(&self, tok: &Token) -> bool {
        tok.data.kind() == self.0 && tok.span.as_str() == self.1
    }

    fn render(&self, seq_fmt: &mut SeqFmt) -> fmt::Result {
        seq_fmt.mark_elem_start()?;
        write!(seq_fmt, "{} (`{}`)", self.0, self.1)
    }

    fn to_boxed_dyn(&self) -> Box<dyn TokenPattern> {
        Box::new((self.0, self.1.to_owned()))
    }
}

impl<P> TokenPattern for Vec<P>
where
    P: TokenPattern,
{
    fn test(&self, tok: &Token) -> bool {
        self[..].test(tok)
    }

    fn render(&self, seq_fmt: &mut SeqFmt) -> fmt::Result {
        self[..].render(seq_fmt)
    }

    fn to_boxed_dyn(&self) -> Box<dyn TokenPattern> {
        Box::new(self.iter().map(P::to_boxed_dyn).collect::<Vec<_>>())
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

    fn render(&self, seq_fmt: &mut SeqFmt) -> fmt::Result {
        for pat in self {
            pat.render(seq_fmt)?;
        }

        Ok(())
    }

    fn to_boxed_dyn(&self) -> Box<dyn TokenPattern> {
        Box::new(self.iter().map(P::to_boxed_dyn).collect::<Vec<_>>())
    }
}

impl<'pat, P> TokenPattern for &'pat P
where
    P: TokenPattern + ?Sized,
{
    fn test(&self, tok: &Token) -> bool {
        (**self).test(tok)
    }

    fn render(&self, seq_fmt: &mut SeqFmt) -> fmt::Result {
        (**self).render(seq_fmt)
    }

    fn to_boxed_dyn(&self) -> Box<dyn TokenPattern> {
        (**self).to_boxed_dyn()
    }
}

impl<P> TokenPattern for Box<P>
where
    P: TokenPattern + ?Sized,
{
    fn test(&self, tok: &Token) -> bool {
        (**self).test(tok)
    }

    fn render(&self, seq_fmt: &mut SeqFmt) -> fmt::Result {
        (**self).render(seq_fmt)
    }

    fn to_boxed_dyn(&self) -> Box<dyn TokenPattern> {
        (**self).to_boxed_dyn()
    }
}

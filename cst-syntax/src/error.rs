//! This module provides syntax errors.

use crate::token::{Token, TokenPattern};
use cst_error::Diagnostic;
use cst_fmt::SeqFmt;
use cst_source::Span;
use std::{error::Error, fmt};

/// An error shown when a bad character was found.
#[derive(Debug, Clone)]
pub struct BadChar {
    /// The [`Span`](cst_source::Span) of the error.
    pub span: Span,
}

impl fmt::Display for BadChar {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "Invalid character")
    }
}

impl Error for BadChar {}

impl Diagnostic for BadChar {
    fn code(&self) -> &str {
        "BADCH"
    }

    fn span(&self) -> Span {
        self.span.clone()
    }
}

/// An error shown when a potential ambiguity in lexing occurs.
#[derive(Debug, Clone)]
pub struct AmbiguousToken {
    /// The [`Span`](cst_source::Span) of the error.
    pub span: Span,
}

impl fmt::Display for AmbiguousToken {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "Ambiguous token, try inserting some spaces")
    }
}

impl Error for AmbiguousToken {}

impl Diagnostic for AmbiguousToken {
    fn code(&self) -> &str {
        "AMBTOK"
    }

    fn span(&self) -> Span {
        self.span.clone()
    }
}

/// An error shown when a exponent that is too big is found.
#[derive(Debug, Clone)]
pub struct ExponentTooBig {
    pub span: Span,
}

impl fmt::Display for ExponentTooBig {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "Exponent too big for a float number")
    }
}

impl Error for ExponentTooBig {}

impl Diagnostic for ExponentTooBig {
    fn code(&self) -> &str {
        "EXPHGE"
    }

    fn span(&self) -> Span {
        self.span.clone()
    }
}

///
/// An error shown when a exponent that is too small is found.
#[derive(Debug, Clone)]
pub struct ExponentTooSmall {
    /// The [`Span`](cst_source::Span) of the error.
    pub span: Span,
}

impl fmt::Display for ExponentTooSmall {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "Exponent too small for a float number")
    }
}

impl Error for ExponentTooSmall {}

impl Diagnostic for ExponentTooSmall {
    fn code(&self) -> &str {
        "EXPTNY"
    }

    fn span(&self) -> Span {
        self.span.clone()
    }
}

#[derive(Debug, Clone)]
pub struct EmptyExponent {
    pub span: Span,
}

impl fmt::Display for EmptyExponent {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "Exponent cannot be empty")
    }
}

impl Error for EmptyExponent {}

impl Diagnostic for EmptyExponent {
    fn code(&self) -> &str {
        "NULEXP"
    }

    fn span(&self) -> Span {
        self.span.clone()
    }
}

/// An error shown when a floating point's fractional part is empty.
#[derive(Debug, Clone)]
pub struct EmptyFrac {
    /// The [`Span`](cst_source::Span) of the error.
    pub span: Span,
}

impl fmt::Display for EmptyFrac {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "Fractionary part cannot be empty")
    }
}

impl Error for EmptyFrac {}

impl Diagnostic for EmptyFrac {
    fn code(&self) -> &str {
        "NULFRA"
    }

    fn span(&self) -> Span {
        self.span.clone()
    }
}

/// An error shown when an unexpected token is found.
#[derive(Clone)]
pub struct UnexpectedToken<P>
where
    P: TokenPattern,
{
    /// The token that was found in the source code.
    pub found: Token,
    /// The expected token pattern.
    pub expected: P,
}

impl<P> fmt::Debug for UnexpectedToken<P>
where
    P: TokenPattern,
{
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        let mut expected = String::new();
        let mut seq_fmt = SeqFmt::with_disjunction(&mut expected);
        self.expected.render(&mut seq_fmt)?;

        fmt.debug_struct("UnexpectedToken")
            .field("found", &self.found)
            .field("expected", &expected)
            .finish()
    }
}

impl<P> fmt::Display for UnexpectedToken<P>
where
    P: TokenPattern,
{
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "Unexpected token {}, expected ", &self.found)?;
        let mut seq_fmt = SeqFmt::with_disjunction(fmt);
        self.expected.render(&mut seq_fmt)?;
        Ok(())
    }
}

impl<P> Error for UnexpectedToken<P> where P: TokenPattern {}

impl<P> Diagnostic for UnexpectedToken<P>
where
    P: TokenPattern,
{
    fn code(&self) -> &str {
        "BADTOK"
    }

    fn span(&self) -> Span {
        self.found.span.clone()
    }
}

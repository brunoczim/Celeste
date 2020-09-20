use cst_error::Diagnostic;
use cst_source::Span;
use std::{error::Error, fmt};

#[derive(Debug, Clone)]
pub struct BadChar {
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

#[derive(Debug, Clone)]
pub struct AmbiguousToken {
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
        "AMTOK"
    }

    fn span(&self) -> Span {
        self.span.clone()
    }
}

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

#[derive(Debug, Clone)]
pub struct ExponentTooSmall {
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

#[derive(Debug, Clone)]
pub struct EmptyFrac {
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

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

use cst_error::{Diagnostic, Level};
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

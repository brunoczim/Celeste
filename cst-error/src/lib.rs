//! This crate provides error handling for the compiler.

use crossterm::{
    style::{Color, SetForegroundColor},
    tty::IsTty,
};
use cst_source::Span;
use std::{error::Error, fmt, io, rc::Rc, slice};

/// A possible error or a warning.
pub trait Diagnostic: Error {
    /// The span of the whole diagnostic.
    fn span(&self) -> Span;

    /// Short code which will be shown.
    fn code(&self) -> &str;

    /// Level of this diagnostic (warning or error).
    fn level(&self) -> Level {
        Level::Error
    }
}

/// Level of a diagnostic.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Level {
    /// Hard error.
    Error,
    /// Just a warning.
    Warning,
}

/// Error emitter.
#[derive(Debug, Clone)]
pub struct Emitter<'diagnostics> {
    /// Whether this emitter has emitted a hard error.
    has_error: bool,
    /// The diagnostics emitted by this emitter.
    diagnostics: Vec<Rc<dyn Diagnostic + 'diagnostics>>,
}

impl<'diagnostics> Default for Emitter<'diagnostics> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'diagnostics> Emitter<'diagnostics> {
    /// Creates a new emitter with no diagnostics.
    pub fn new() -> Self {
        Self { has_error: false, diagnostics: Vec::new() }
    }

    /// Emits a new diagnostic.
    pub fn emit<D>(&mut self, diagnostic: D)
    where
        D: Diagnostic + 'diagnostics,
    {
        self.has_error |= diagnostic.level() == Level::Error;
        self.diagnostics.push(Rc::new(diagnostic));
    }

    /// Whether a hard error was emitted.
    pub fn has_error(&self) -> bool {
        self.has_error
    }

    /// Iterates over the emitted diagnostics.
    pub fn iter<'emitter>(
        &'emitter self,
    ) -> EmitterIter<'emitter, 'diagnostics> {
        EmitterIter { inner: self.diagnostics.iter() }
    }
}

impl<'emitter, 'diagnostics> IntoIterator for &'emitter Emitter<'diagnostics> {
    type Item = &'emitter (dyn Diagnostic + 'diagnostics);
    type IntoIter = EmitterIter<'emitter, 'diagnostics>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl fmt::Display for Emitter<'_> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        let is_tty = io::stdout().is_tty();
        let mut first = true;

        for diagnostic in self {
            if first {
                first = false;
            } else {
                write!(fmt, "\n\n")?;
            }

            if is_tty {
                match diagnostic.level() {
                    Level::Error => {
                        write!(fmt, "{}", SetForegroundColor(Color::Red))?
                    },
                    Level::Warning => {
                        write!(fmt, "{}", SetForegroundColor(Color::Yellow))?
                    },
                }
            }
            fmt.write_str(match diagnostic.level() {
                Level::Error => "Error",
                Level::Warning => "Warning",
            })?;
            if is_tty {
                write!(fmt, "{}", SetForegroundColor(Color::Reset))?;
            }

            write!(fmt, " ({}) {}:\n", diagnostic.code(), diagnostic.span())?;
            let mut first = true;
            for elem in diagnostic.to_string().split('\n') {
                if first {
                    first = false;
                } else {
                    write!(fmt, "\n")?;
                }

                if elem.trim().len() > 0 {
                    write!(fmt, "    ")?;
                }
                write!(fmt, "{}", elem)?;
            }
        }

        Ok(())
    }
}

/// Iterator over the diagnostics of an emitter.
#[derive(Debug, Clone)]
pub struct EmitterIter<'emitter, 'diagnostics> {
    /// Iterator over the vector of an emitter.
    inner: slice::Iter<'emitter, Rc<dyn Diagnostic + 'diagnostics>>,
}

impl<'emitter, 'diagnostics> Iterator for EmitterIter<'emitter, 'diagnostics> {
    type Item = &'emitter (dyn Diagnostic + 'diagnostics);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(AsRef::as_ref)
    }
}

impl<'emitter, 'diagnostics> DoubleEndedIterator
    for EmitterIter<'emitter, 'diagnostics>
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back().map(AsRef::as_ref)
    }
}

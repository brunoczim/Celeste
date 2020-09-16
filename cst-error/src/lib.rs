use crossterm::{
    style::{Color, SetForegroundColor},
    tty::IsTty,
};
use cst_source::Span;
use std::{error::Error, fmt, io, rc::Rc, slice};

pub trait Diagnostic: Error {
    fn span(&self) -> Span;

    fn code(&self) -> &str;

    fn level(&self) -> Level {
        Level::Error
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Level {
    Error,
    Warning,
}

#[derive(Debug, Clone)]
pub struct Emitter<'diagnostics> {
    has_error: bool,
    diagnostics: Vec<Rc<dyn Diagnostic + 'diagnostics>>,
}

impl<'diagnostics> Default for Emitter<'diagnostics> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'diagnostics> Emitter<'diagnostics> {
    pub fn new() -> Self {
        Self { has_error: false, diagnostics: Vec::new() }
    }

    pub fn emit<D>(&mut self, diagnostic: D)
    where
        D: Diagnostic + 'diagnostics,
    {
        self.has_error = diagnostic.level() == Level::Error;
        self.diagnostics.push(Rc::new(diagnostic));
    }

    pub fn has_error(&self) -> bool {
        self.has_error
    }

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

            write!(
                fmt,
                " ({}) {}:\n{}",
                diagnostic.code(),
                diagnostic.span(),
                diagnostic
            )?;
        }

        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct EmitterIter<'emitter, 'diagnostics> {
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

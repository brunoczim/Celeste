//! This crate provides error handling for the compiler.

use crossterm::{
    style::{Color, SetForegroundColor},
    tty::IsTty,
};
use cst_fmt::{Ruler, SeqFmt};
use cst_source::Span;
use std::{error::Error, fmt, fmt::Write, io, rc::Rc, slice};

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

impl Level {
    /// Terminal color associated with this diagnostic level.
    pub fn color(&self) -> Color {
        match self {
            Level::Error => Color::Red,
            Level::Warning => Color::Yellow,
        }
    }
}

impl fmt::Display for Level {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.write_str(match self {
            Level::Error => "Error",
            Level::Warning => "Warning",
        })
    }
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
        let mut seq = SeqFmt::new(fmt, "\n\n", "\n\n");
        let is_tty = io::stdout().is_tty();

        for diagnostic in self {
            let span = diagnostic.span();

            seq.mark_elem_start()?;
            write_with_color(
                diagnostic.level().color(),
                &mut seq,
                is_tty,
                |writer| write!(writer, "{}", diagnostic.level()),
            )?;
            write!(seq, " ({}) ", diagnostic.code(),)?;
            write_with_color(Color::Blue, &mut seq, is_tty, |writer| {
                write!(writer, "{}", diagnostic.span())
            })?;
            write!(seq, ":\n")?;
            let mut ruler = Ruler::new(&mut seq, "  ");

            write!(ruler, "{}\nContext:\n", diagnostic)?;
            let lines = span.expand_lines();
            let mut code_ruler = Ruler::new(&mut ruler, "| ");

            write!(
                code_ruler,
                "{}",
                &span.src()[lines.start().pos() .. span.start().pos()]
            )?;
            write_with_color(
                diagnostic.level().color(),
                &mut code_ruler,
                is_tty,
                |writer| write!(writer, "{}", span.as_str()),
            )?;
            write!(
                code_ruler,
                "{}",
                &span.src()[span.end().pos() .. lines.end().pos()].trim_end()
            )?;
        }

        seq.finish()
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

/// Writes with a color only if stdout is a terminal, reseting color after it.
fn write_with_color<W, F>(
    color: Color,
    writer: &mut W,
    is_tty: bool,
    middle: F,
) -> fmt::Result
where
    W: Write,
    F: FnOnce(&mut W) -> fmt::Result,
{
    if is_tty {
        write!(writer, "{}", SetForegroundColor(color))?
    }
    middle(writer)?;
    if is_tty {
        write!(writer, "{}", SetForegroundColor(Color::Reset))?;
    }
    Ok(())
}

//! This module provides means of tracking location in a source code.

use crate::{Span, Src};
use std::fmt;

/// The location in a source code.
///
/// See [`Reader::mark`](crate::reader::Reader::mark) and
/// [`Reader::location`](crate::reader::Reader::location) to create a location.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Location {
    /// The source code object.
    src: Src,
    /// The string segment position.
    pos: usize,
}

impl Location {
    /// Creates a new location given a source code object and a string segment
    /// position in the object.
    pub(super) fn new(src: Src, pos: usize) -> Self {
        Self { src, pos }
    }

    /// The string segment position in the source code.
    pub fn pos(&self) -> usize {
        self.pos
    }

    /// The source code object this location refers to.
    pub fn src(&self) -> &Src {
        &self.src
    }

    /// Finds the line and column (respectively) of this location in the source
    /// code.
    pub fn line_column(&self) -> (usize, usize) {
        match self.src.inner.newlines.binary_search(self.pos) {
            Ok(0) | Err(0) => (0, self.pos),
            Ok(n) | Err(n) => {
                (n, self.pos - self.src.inner.newlines.index(n - 1))
            },
        }
    }

    /// Finds the line of this location in the source code.
    pub fn line(&self) -> usize {
        match self.src.inner.newlines.binary_search(self.pos) {
            Ok(n) | Err(n) => n,
        }
    }

    /// Finds the column of this location in the source code.
    pub fn column(&self) -> usize {
        let (_, column) = self.line_column();
        column
    }

    /// Creates a [`Span`](crate::span::Span) containing the whole line this
    /// location is in.
    pub fn line_span(&self) -> Span {
        let line = self.line();
        let init = line
            .checked_sub(1)
            .map_or(0, |prev| self.src.inner.newlines.index(prev) + 1);
        let end = self
            .src
            .inner
            .newlines
            .get(line + 1)
            .map_or(self.src.len(), |next| next + 1);
        Span::new(Self::new(self.src.clone(), init), end - init)
    }
}

impl fmt::Debug for Location {
    fn fmt(&self, fmtr: &mut fmt::Formatter) -> fmt::Result {
        let (line, column) = self.line_column();
        write!(
            fmtr,
            "Location {} src: {:?}, pos: {}, line: {}, column: {} {}",
            '{', self.src, self.pos, line, column, '}'
        )
    }
}

impl fmt::Display for Location {
    fn fmt(&self, fmtr: &mut fmt::Formatter) -> fmt::Result {
        let (line, column) = self.line_column();
        write!(fmtr, "in {} ({}, {})", self.src, line + 1, column + 1)
    }
}

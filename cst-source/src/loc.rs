//! This module provides means of tracking location in a source code.

use super::Src;
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
        match self.src.inner.newlines.binary_search(&self.pos) {
            Ok(0) | Err(0) => (1, self.pos + 1),
            Ok(n) | Err(n) => {
                (n + 1, self.pos - self.src.inner.newlines[n - 1] + 1)
            },
        }
    }

    /// Finds the line of this location in the source code.
    pub fn line(&self) -> usize {
        let (line, _) = self.line_column();
        line
    }

    /// Finds the column of this location in the source code.
    pub fn column(&self) -> usize {
        let (_, column) = self.line_column();
        column
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
        write!(fmtr, "in {} ({}, {})", self.src, line, column)
    }
}

use super::Src;
use std::fmt;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Location {
    src: Src,
    pos: usize,
}

impl Location {
    pub(crate) fn new(src: Src, pos: usize) -> Self {
        Self { src, pos }
    }

    pub fn pos(&self) -> usize {
        self.pos
    }

    pub fn src(&self) -> &Src {
        &self.src
    }

    pub fn line_column(&self) -> (usize, usize) {
        match self.src.inner.newlines.binary_search(&self.pos) {
            Ok(0) | Err(0) => (1, self.pos + 1),
            Ok(n) | Err(n) => {
                (n + 1, self.pos - self.src.inner.newlines[n - 1] + 1)
            },
        }
    }

    pub fn line(&self) -> usize {
        let (line, _) = self.line_column();
        line
    }

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

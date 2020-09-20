//! This module provides means of navigating on a source code, a stream.

use super::{Location, Span, Src};

/// A reader of a source code, a stream.
///
/// See [`Src::reader`](crate::Src::reader) to create a reader.
#[derive(Debug, Clone)]
pub struct Reader {
    /// The source code this reader is reading.
    src: Src,
    /// The position (in string segments) in the source this reader is.
    pos: usize,
    /// Last position (in string segments) marked by the reader.
    marked: usize,
}

impl Reader {
    /// Creates a new reader given the source code object it will read.
    pub(super) fn new(src: Src) -> Self {
        Self { src, pos: 0, marked: 0 }
    }

    /// Is the end of file reached?
    pub fn is_eof(&self) -> bool {
        self.curr().is_none()
    }

    /// Position in string segments that the reader is currently at.
    pub fn pos(&self) -> usize {
        self.pos
    }

    /// The current string segment rendered.
    pub fn curr(&self) -> Option<&str> {
        self.src.get(self.pos)
    }

    /// A string segment from current position until `current + additional`,
    /// rendered.
    pub fn curr_to(&self, additional: usize) -> Option<&str> {
        self.src.get(self.pos .. self.pos + additional)
    }

    /// The marked position (in string segments).
    pub fn marked(&self) -> usize {
        self.marked
    }

    /// The source code this reader is reading.
    pub fn src(&self) -> &Src {
        &self.src
    }

    /// Location at the given position.
    pub fn location(&self) -> Location {
        Location::new(self.src.clone(), self.pos)
    }

    /// [`Span`](crate::span::Span) from the marked position up to the current
    /// position.
    pub fn span(&self) -> Span {
        if self.marked < self.pos {
            let loc = Location::new(self.src.clone(), self.marked);
            Span::new(loc, self.pos - self.marked)
        } else {
            Span::new(self.location(), self.marked - self.pos)
        }
    }

    /// Marks the current position so it can be used to create a
    /// [`Span`](crate::span::Span) later.
    pub fn mark(&mut self) {
        self.marked = self.pos;
    }

    /// Advances the stream by 1 and returns whether it did move.
    pub fn next(&mut self) -> bool {
        self.advance(1) == 1
    }

    /// Goes back on the stream by 1 and returns whether it did move.
    pub fn prev(&mut self) -> bool {
        self.rollback(1) == 1
    }

    /// Advance the stream by the given `count` of string segments, and return
    /// how much it actually moved.
    pub fn advance(&mut self, count: usize) -> usize {
        let advanced = count.min(self.src.len() - self.pos);
        self.pos += advanced;
        advanced
    }

    /// Goes back on the stream by the given `count` of string segments, and
    /// return how much it actually moved.
    pub fn rollback(&mut self, count: usize) -> usize {
        let rolled = count.min(self.pos);
        self.pos -= rolled;
        rolled
    }

    #[deprecated]
    pub fn expect(&mut self, mut expected: &str) -> bool {
        let mut count = 0;

        while expected.len() > 0 {
            if let Some(found) =
                self.curr().filter(|found| expected.starts_with(found))
            {
                expected = &expected[found.len() ..];
                count += 1;
                self.next();
            } else {
                self.rollback(count);
                return false;
            }
        }

        true
    }
}

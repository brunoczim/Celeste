//! This module provides ways of tracking ranges (spans) in the source code.

use super::{Location, Src};
use std::{
    borrow::Borrow,
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
    ops::Deref,
};

/// A span (a range) in the source code.
///
/// See [`Reader::mark`](crate::reader::Reader::mark) and
/// [`Reader::span`](crate::reader::Reader::span) to create a span.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Span {
    /// Start of the span.
    loc: Location,
    /// Length of the span in string segments.
    len: usize,
}

impl Span {
    /// Creates a new span given the start location and length.
    pub(super) fn new(loc: Location, len: usize) -> Self {
        Self { loc, len }
    }

    /// The start location of this span.
    pub fn start(&self) -> Location {
        self.loc.clone()
    }

    /// The end location of this span.
    pub fn end(&self) -> Location {
        Location::new(self.src().clone(), self.loc.pos() + self.len)
    }

    /// The length of this span in string segments.
    pub fn len(&self) -> usize {
        self.len
    }

    /// The source code object this span refers to.
    pub fn src(&self) -> &Src {
        self.loc.src()
    }

    /// Gets the string this span includes as a whole.
    pub fn as_str(&self) -> &str {
        let start = self.loc.pos();
        self.src().get(start .. start + self.len()).unwrap()
    }

    /// Creates a type that, when displayed, shows the span contents, rather
    /// than location.
    pub fn content(&self) -> SpanContent {
        SpanContent { span: self.clone() }
    }
}

impl fmt::Debug for Span {
    fn fmt(&self, fmtr: &mut fmt::Formatter) -> fmt::Result {
        write!(
            fmtr,
            "Span {} src: {:?}, start: {}, end: {}, content: {:?} {}",
            '{',
            self.src(),
            self.start(),
            self.end(),
            self.as_str(),
            '}'
        )
    }
}

impl fmt::Display for Span {
    fn fmt(&self, fmtr: &mut fmt::Formatter) -> fmt::Result {
        let file = self.src().name();
        let (line_start, col_start) = self.start().line_column();
        let (line_end, col_end) = self.end().line_column();
        write!(
            fmtr,
            "in {} from ({}, {}) to ({}, {})",
            file, line_start, col_start, line_end, col_end
        )
    }
}

impl<T> AsRef<T> for Span
where
    T: ?Sized,
    str: AsRef<T>,
{
    fn as_ref(&self) -> &T {
        self.as_str().as_ref()
    }
}

/// A type that, when displayed, shows the span contents, rather than location.
#[derive(Clone, Debug)]
pub struct SpanContent {
    /// The inner span of a source code.
    span: Span,
}

impl SpanContent {
    /// Returns the inner span.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl Deref for SpanContent {
    type Target = str;

    fn deref(&self) -> &str {
        self.span.as_str()
    }
}

impl fmt::Display for SpanContent {
    fn fmt(&self, fmtr: &mut fmt::Formatter) -> fmt::Result {
        write!(fmtr, "{}", &**self)
    }
}

impl PartialEq for SpanContent {
    fn eq(&self, other: &Self) -> bool {
        **self == **other
    }
}

impl<T> PartialEq<T> for SpanContent
where
    T: ?Sized,
    str: PartialEq<T>,
{
    fn eq(&self, other: &T) -> bool {
        &**self == other
    }
}

impl Eq for SpanContent {}

impl PartialOrd for SpanContent {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> PartialOrd<T> for SpanContent
where
    T: ?Sized,
    str: PartialOrd<T>,
{
    fn partial_cmp(&self, other: &T) -> Option<Ordering> {
        (**self).partial_cmp(other)
    }
}

impl Ord for SpanContent {
    fn cmp(&self, other: &Self) -> Ordering {
        (**self).cmp(&**other)
    }
}

impl Hash for SpanContent {
    fn hash<H>(&self, hasher: &mut H)
    where
        H: Hasher,
    {
        (**self).hash(hasher)
    }
}

impl<T> AsRef<T> for SpanContent
where
    T: ?Sized,
    str: AsRef<T>,
{
    fn as_ref(&self) -> &T {
        (**self).as_ref()
    }
}

impl<T> Borrow<T> for SpanContent
where
    T: ?Sized,
    str: Borrow<T>,
{
    fn borrow(&self) -> &T {
        (**self).borrow()
    }
}

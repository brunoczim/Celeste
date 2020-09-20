//! This crate provides utilities to handle the source code.

mod loc;
mod reader;
mod span;

pub use self::{
    loc::Location,
    reader::Reader,
    span::{Span, SpanContent},
};
use std::{
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
    ops::{
        Index,
        Range,
        RangeFrom,
        RangeFull,
        RangeInclusive,
        RangeTo,
        RangeToInclusive,
    },
    rc::Rc,
};
use unicode_segmentation::UnicodeSegmentation;

/// Inner structure of a source.
#[derive(Debug)]
struct SrcInner {
    /// File name.
    name: Box<str>,
    /// Contents of the source.
    content: Box<str>,
    /// List of string segmentation in the source.
    segments: Box<[usize]>,
    /// List of newlines in the source.
    newlines: Box<[usize]>,
}

/// A source code object, such as read from a file.
#[derive(Debug, Clone)]
pub struct Src {
    /// The inner structure containing the actual data.
    inner: Rc<SrcInner>,
}

impl Src {
    /// Creates a new source code object given its name and its contents.
    pub fn new<S0, S1>(name: S0, content: S1) -> Self
    where
        S0: Into<Box<str>>,
        S1: Into<Box<str>>,
    {
        let name = name.into();
        let content = content.into();
        let mut segments = Vec::new();
        let mut newlines = Vec::new();

        for (idx, grapheme) in content.grapheme_indices(true) {
            if grapheme == "\n" {
                newlines.push(segments.len());
            }
            segments.push(idx);
        }
        segments.push(content.len());

        let segments = segments.into();
        let newlines = newlines.into();
        let inner = SrcInner { name, content, segments, newlines };
        Self { inner: Rc::new(inner) }
    }

    /// The (file) name of the source.
    pub fn name(&self) -> &str {
        &self.inner.name
    }

    /// The length the source.
    pub fn len(&self) -> usize {
        self.inner.segments.len() - 1
    }

    /// The contents of the source.
    pub fn content(&self) -> &str {
        &self.inner.content
    }

    /// The segments of the source.
    pub fn segments(&self) -> &[usize] {
        &self.inner.segments
    }

    /// Indexes this source. It can be a single `usize` or a range of `usize`.
    pub fn get<I>(&self, indexer: I) -> Option<&I::Output>
    where
        I: SrcIndex,
    {
        indexer.get(self)
    }

    /// Creates a source code reader (a stream) from this source code object.
    pub fn reader(&self) -> Reader {
        Reader::new(self.clone())
    }
}

impl<I> Index<I> for Src
where
    I: SrcIndex,
{
    type Output = I::Output;

    fn index(&self, indexer: I) -> &Self::Output {
        indexer.index(self)
    }
}

impl PartialEq for Src {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.inner, &other.inner)
    }
}

impl Eq for Src {}

impl PartialOrd for Src {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Src {
    fn cmp(&self, other: &Self) -> Ordering {
        (&*self.inner as *const SrcInner).cmp(&(&*other.inner as *const _))
    }
}

impl Hash for Src {
    fn hash<H>(&self, hasher: &mut H)
    where
        H: Hasher,
    {
        (&*self.inner as *const SrcInner).hash(hasher)
    }
}

impl fmt::Display for Src {
    fn fmt(&self, fmtr: &mut fmt::Formatter) -> fmt::Result {
        fmtr.write_str(self.name())
    }
}

/// An index on a source code.
pub trait SrcIndex: fmt::Debug {
    /// Output of the indexing operation.
    type Output: ?Sized;

    /// Indexes the source code and returns `None` if out of bounds.
    fn get<'src>(&self, src: &'src Src) -> Option<&'src Self::Output>;

    /// Indexes the source code and panics if out of bounds.
    fn index<'src>(&self, src: &'src Src) -> &'src Self::Output {
        match self.get(src) {
            Some(out) => out,
            None => panic!(
                "Index {:?} is not valid when accessing source {} of length {}",
                self,
                src.name(),
                src.len()
            ),
        }
    }
}

impl SrcIndex for usize {
    type Output = str;

    fn get<'src>(&self, src: &'src Src) -> Option<&'src Self::Output> {
        (*self .. self.checked_add(1)?).get(src)
    }
}

impl SrcIndex for Range<usize> {
    type Output = str;

    fn get<'src>(&self, src: &'src Src) -> Option<&'src Self::Output> {
        let start = *src.segments().get(self.start)?;
        let end = *src.segments().get(self.end)?;
        src.content().get(start .. end)
    }
}

impl SrcIndex for RangeTo<usize> {
    type Output = str;

    fn get<'src>(&self, src: &'src Src) -> Option<&'src Self::Output> {
        (0 .. self.end).get(src)
    }
}

impl SrcIndex for RangeFrom<usize> {
    type Output = str;

    fn get<'src>(&self, src: &'src Src) -> Option<&'src Self::Output> {
        (self.start .. src.len()).get(src)
    }
}

impl SrcIndex for RangeInclusive<usize> {
    type Output = str;

    fn get<'src>(&self, src: &'src Src) -> Option<&'src Self::Output> {
        (*self.start() .. self.end().checked_add(1)?).get(src)
    }
}

impl SrcIndex for RangeToInclusive<usize> {
    type Output = str;

    fn get<'src>(&self, src: &'src Src) -> Option<&'src Self::Output> {
        (0 .. self.end.checked_add(1)?).get(src)
    }
}

impl SrcIndex for RangeFull {
    type Output = str;

    fn get<'src>(&self, src: &'src Src) -> Option<&'src Self::Output> {
        Some(src.content())
    }
}

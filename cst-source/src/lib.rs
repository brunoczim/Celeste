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

#[derive(Debug)]
struct SrcInner {
    name: Box<str>,
    content: Box<str>,
    segments: Box<[usize]>,
    newlines: Box<[usize]>,
}

#[derive(Debug, Clone)]
pub struct Src {
    inner: Rc<SrcInner>,
}

impl Src {
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

    pub fn name(&self) -> &str {
        &self.inner.name
    }

    pub fn len(&self) -> usize {
        self.inner.segments.len() - 1
    }

    pub fn content(&self) -> &str {
        &self.inner.content
    }

    pub fn segments(&self) -> &[usize] {
        &self.inner.segments
    }

    pub fn get<I>(&self, indexer: I) -> Option<&I::Output>
    where
        I: SrcIndex,
    {
        indexer.get(self)
    }

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

pub trait SrcIndex: fmt::Debug {
    type Output: ?Sized;

    fn get<'src>(&self, src: &'src Src) -> Option<&'src Self::Output>;

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

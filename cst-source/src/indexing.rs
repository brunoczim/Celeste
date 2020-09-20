//! Utilities for indexing objects in memory, such as the source code object.

use super::Src;
use std::{
    cmp::Ordering,
    convert::TryFrom,
    fmt,
    ops::{
        Range,
        RangeFrom,
        RangeFull,
        RangeInclusive,
        RangeTo,
        RangeToInclusive,
    },
    slice,
};

/// Builder of an [`IndexArray`].
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct IndexArrayBuilder {
    /// 8 bit indices, which will be sorted by the end.
    as_u8: Vec<u8>,
    /// 16 bit indices, which will be sorted by the end.
    as_u16: Vec<u16>,
    /// 32 bit indices, which will be sorted by the end.
    as_u32: Vec<u32>,
    /// 64 bit indices, which will be sorted by the end.
    as_u64: Vec<u64>,
}

impl IndexArrayBuilder {
    /// Creates a new builder with no elements.
    pub fn new() -> Self {
        Self::default()
    }

    /// The length of this builder.
    pub fn len(&self) -> usize {
        self.as_u8.len()
            + self.as_u16.len()
            + self.as_u32.len()
            + self.as_u64.len()
    }

    /// Pushes a new index onto the builder.
    pub fn push(&mut self, index: usize) -> &mut Self {
        if let Ok(i) = u8::try_from(index) {
            self.as_u8.push(i);
        } else if let Ok(i) = u16::try_from(index) {
            self.as_u16.push(i);
        } else if let Ok(i) = u32::try_from(index) {
            self.as_u32.push(i);
        } else if let Ok(i) = u64::try_from(index) {
            self.as_u64.push(i);
        } else {
            panic!("Index {} is too big", index);
        }
        self
    }

    /// Finishes the builder and creates and [`IndexArray`].
    pub fn finish(mut self) -> IndexArray {
        self.as_u8.sort();
        self.as_u16.sort();
        self.as_u32.sort();
        self.as_u64.sort();

        IndexArray {
            as_u8: self.as_u8.into(),
            as_u16: self.as_u16.into(),
            as_u32: self.as_u32.into(),
            as_u64: self.as_u64.into(),
        }
    }
}

impl From<IndexArrayBuilder> for IndexArray {
    fn from(builder: IndexArrayBuilder) -> Self {
        builder.finish()
    }
}

/// A smart ordered array of indices, which tries to use space as little as
/// possible.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct IndexArray {
    /// Indices that fit 8 bits.
    as_u8: Box<[u8]>,
    /// Indices that fit 16 bits.
    as_u16: Box<[u16]>,
    /// Indices that fit 32 bits.
    as_u32: Box<[u32]>,
    /// Indices that fit 64 bits.
    as_u64: Box<[u64]>,
}

impl IndexArray {
    /// Length of this array.
    pub fn len(&self) -> usize {
        self.as_u8.len()
            + self.as_u16.len()
            + self.as_u32.len()
            + self.as_u64.len()
    }

    /// Gets an index stored in the array given this meta-index.
    ///
    /// # Panics
    /// Panics if out of bounds.
    pub fn index(&self, meta_index: usize) -> usize {
        match self.get(meta_index) {
            Some(index) => index,
            None => panic!(
                "Meta index was {}, but length is {}",
                meta_index,
                self.len()
            ),
        }
    }

    /// Gets an index stored in the array given this meta-index, returning
    /// `None` if out of bounds.
    pub fn get(&self, mut meta_index: usize) -> Option<usize> {
        if let Some(&i) = self.as_u8.get(meta_index) {
            return Some(i as usize);
        }
        meta_index -= self.as_u8.len();
        if let Some(&i) = self.as_u16.get(meta_index) {
            return Some(i as usize);
        }
        meta_index -= self.as_u16.len();
        if let Some(&i) = self.as_u32.get(meta_index) {
            return Some(i as usize);
        }
        meta_index -= self.as_u32.len();
        self.as_u64.get(meta_index).map(|&i| i as usize)
    }

    /// Performs a binary search on this index array. `Ok` means it was found,
    /// `Err` means it was not found, but we have the position where it would
    /// be.
    pub fn binary_search(&self, elem: usize) -> Result<usize, usize> {
        let mut low = 0;
        let mut high = self.len();
        let mut error = 0;
        while low < high {
            let mid = low + (high - low) / 2;
            match self.index(mid).cmp(&elem) {
                Ordering::Equal => return Ok(mid),
                Ordering::Greater => {
                    high = mid;
                    error = high
                },
                Ordering::Less => {
                    low = mid + 1;
                    error = low;
                },
            }
        }
        Err(error)
    }

    /// Iterates over the indices stored in this array.
    pub fn iter(&self) -> IndexArrayIter {
        IndexArrayIter {
            as_u8: self.as_u8.iter(),
            as_u16: self.as_u16.iter(),
            as_u32: self.as_u32.iter(),
            as_u64: self.as_u64.iter(),
        }
    }
}

impl<'array> IntoIterator for &'array IndexArray {
    type Item = usize;
    type IntoIter = IndexArrayIter<'array>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// Iterator over an array of indices. Double-ended and sized.
#[derive(Debug)]
pub struct IndexArrayIter<'array> {
    as_u8: slice::Iter<'array, u8>,
    as_u16: slice::Iter<'array, u16>,
    as_u32: slice::Iter<'array, u32>,
    as_u64: slice::Iter<'array, u64>,
}

impl<'array> Iterator for IndexArrayIter<'array> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(&i) = self.as_u8.next() {
            return Some(i as usize);
        }
        if let Some(&i) = self.as_u16.next() {
            return Some(i as usize);
        }
        if let Some(&i) = self.as_u32.next() {
            return Some(i as usize);
        }
        self.as_u64.next().map(|&i| i as usize)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.as_u8.len()
            + self.as_u16.len()
            + self.as_u32.len()
            + self.as_u64.len();
        (len, Some(len))
    }
}

impl<'array> DoubleEndedIterator for IndexArrayIter<'array> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some(&i) = self.as_u64.next() {
            return Some(i as usize);
        }
        if let Some(&i) = self.as_u32.next() {
            return Some(i as usize);
        }
        if let Some(&i) = self.as_u16.next() {
            return Some(i as usize);
        }
        self.as_u8.next().map(|&i| i as usize)
    }
}

impl<'array> ExactSizeIterator for IndexArrayIter<'array> {}

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
        let start = src.inner.segments.get(self.start)?;
        let end = src.inner.segments.get(self.end)?;
        src.contents().get(start .. end)
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
        Some(src.contents())
    }
}

#[cfg(test)]
mod test {
    use super::IndexArrayBuilder;

    #[test]
    fn binary_search() {
        let mut builder = IndexArrayBuilder::default();
        builder.push(1).push(2).push(4).push(7).push(8).push(9);
        let array = builder.finish();
        assert_eq!(array.binary_search(0), Err(0));
        assert_eq!(array.binary_search(1), Ok(0));
        assert_eq!(array.binary_search(2), Ok(1));
        assert_eq!(array.binary_search(3), Err(2));
        assert_eq!(array.binary_search(4), Ok(2));
        assert_eq!(array.binary_search(5), Err(3));
        assert_eq!(array.binary_search(6), Err(3));
        assert_eq!(array.binary_search(7), Ok(3));
        assert_eq!(array.binary_search(8), Ok(4));
        assert_eq!(array.binary_search(9), Ok(5));
        assert_eq!(array.binary_search(10), Err(6));
    }
}

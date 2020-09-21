//! This crate provides extensions to rust string formatting API.

use std::{
    fmt::{self, Write},
    str,
};

/// A formatter that inserts indentation at each line.
pub struct Ruler<'target, 'obj, 'indent> {
    /// The actual writer.
    target: &'target mut (dyn Write + 'obj),
    /// Indentation size.
    indent: &'indent str,
    /// Whether indentation is required in the next line.
    need_indent: bool,
}

impl<'target, 'obj, 'indent> Ruler<'target, 'obj, 'indent> {
    /// Creates a new ruler with given indentation size.
    pub fn new(
        target: &'target mut (dyn Write + 'obj),
        indent: &'indent str,
    ) -> Self {
        Self { target, indent, need_indent: true }
    }
}

impl<'target, 'obj, 'indent> fmt::Debug for Ruler<'target, 'obj, 'indent> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_struct("SeqFmt")
            .field("target", &(self.target as *const _))
            .field("indent", &self.indent)
            .finish()
    }
}

impl<'target, 'obj, 'indent> Write for Ruler<'target, 'obj, 'indent> {
    fn write_str(&mut self, str: &str) -> fmt::Result {
        let mut needs_newline = false;
        for piece in str.split('\n') {
            if self.need_indent {
                if needs_newline {
                    write!(self.target, "\n",)?;
                }
                write!(self.target, "{}", self.indent)?;
            }
            needs_newline = true;
            self.need_indent = true;
            write!(self.target, "{}", piece)?;
        }

        self.need_indent = false;
        Ok(())
    }
}

/// A formatter that produces sequences in the form "a, b, c or d".
pub struct SeqFmt<'target, 'obj, 'sep, 'last_sep> {
    /// The actual writer.
    target: &'target mut (dyn Write + 'obj),
    /// The cache of the two last elements of the sequence.
    cache: Vec<u8>,
    /// Cursor to separate previous element from the current one.
    curr: usize,
    /// Separator of all elements but the last.
    sep: &'sep str,
    /// Separator of the last two elements.
    last_sep: &'last_sep str,
}

impl<'target, 'obj, 'sep, 'last_sep> SeqFmt<'target, 'obj, 'sep, 'last_sep> {
    /// Creates a new sequence formatter given the target writer.
    pub fn new(
        target: &'target mut (dyn Write + 'obj),
        sep: &'sep str,
        last_sep: &'last_sep str,
    ) -> Self {
        Self { target, cache: Vec::new(), curr: 0, sep, last_sep }
    }

    /// Creates a sequence formatter that always separates with commas.
    pub fn with_only_commas(target: &'target mut (dyn Write + 'obj)) -> Self {
        Self::new(target, ", ", ", ")
    }

    /// Creates a sequence formatter that separates with commas and a final
    /// "or".
    pub fn with_disjunction(target: &'target mut (dyn Write + 'obj)) -> Self {
        Self::new(target, ", ", " or ")
    }

    /// Creates a sequence formatter that separates with commas and a final
    /// "and".
    pub fn with_conjunction(target: &'target mut (dyn Write + 'obj)) -> Self {
        Self::new(target, ", ", " and ")
    }

    /// Marks the start of a new element.
    pub fn mark_elem_start(&mut self) -> fmt::Result {
        let old_curr = self.curr;

        self.curr = self.cache.len() - old_curr;
        if old_curr != 0 {
            let str = str::from_utf8(&self.cache[.. old_curr]).unwrap();
            self.target.write_str(str)?;

            self.target.write_str(self.sep)?;

            for i in old_curr .. self.cache.len() {
                self.cache[i - old_curr] = self.cache[i];
            }
            self.cache.truncate(self.curr);
        }

        Ok(())
    }

    /// Finishes the sequence.
    pub fn finish(self) -> fmt::Result {
        let (first, second) = self.cache.split_at(self.curr);

        if first.len() > 0 {
            let str = str::from_utf8(first).unwrap();
            self.target.write_str(str)?;
            self.target.write_str(self.last_sep)?;
        }

        let str = str::from_utf8(second).unwrap();
        self.target.write_str(str)
    }
}

impl<'target, 'obj, 'sep, 'last_sep> Write
    for SeqFmt<'target, 'obj, 'sep, 'last_sep>
{
    fn write_str(&mut self, str: &str) -> fmt::Result {
        self.cache.extend_from_slice(str.as_bytes());
        Ok(())
    }
}

impl<'target, 'obj, 'sep, 'last_sep> fmt::Debug
    for SeqFmt<'target, 'obj, 'sep, 'last_sep>
{
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_struct("SeqFmt")
            .field("target", &(self.target as *const _))
            .field("cache", &self.cache)
            .field("curr", &self.curr)
            .field("sep", &self.sep)
            .field("last_sep", &self.last_sep)
            .finish()
    }
}

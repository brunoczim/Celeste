use std::{
    fmt::{self, Write},
    str,
};

pub struct SeqFmt<'buf> {
    buf: &'buf mut (dyn Write + 'buf),
    cache: Vec<u8>,
    curr: usize,
}

impl<'buf> SeqFmt<'buf> {
    pub fn new(buf: &'buf mut (dyn Write + 'buf)) -> Self {
        Self { buf, cache: Vec::new(), curr: 0 }
    }

    pub fn mark_start(&mut self) -> fmt::Result {
        let old_curr = self.curr;

        self.curr = self.cache.len() - old_curr;
        if old_curr != 0 {
            let str = str::from_utf8(&self.cache[.. old_curr]).unwrap();
            self.buf.write_str(str)?;

            self.buf.write_str(", ")?;

            for i in old_curr .. self.cache.len() {
                self.cache[i - old_curr] = self.cache[i];
            }
            self.cache.truncate(self.curr);
        }

        Ok(())
    }

    pub fn finish(self) -> fmt::Result {
        let (first, second) = self.cache.split_at(self.curr);

        if first.len() > 0 {
            let str = str::from_utf8(first).unwrap();
            self.buf.write_str(str)?;
            self.buf.write_str(" or ")?;
        }

        let str = str::from_utf8(second).unwrap();
        self.buf.write_str(str)
    }
}

impl<'buf> Write for SeqFmt<'buf> {
    fn write_str(&mut self, str: &str) -> fmt::Result {
        self.cache.extend_from_slice(str.as_bytes());
        Ok(())
    }
}

impl<'buf> fmt::Debug for SeqFmt<'buf> {
    fn fmt(&self, fmtr: &mut fmt::Formatter) -> fmt::Result {
        write!(
            fmtr,
            "SeqFmt {} buf: {:?}, cache: {:?}, curr: {} {}",
            '{', self.buf as *const _, self.cache, self.curr, '}'
        )
    }
}

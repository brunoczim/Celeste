use super::{Location, Span, Src};

#[derive(Debug, Clone)]
pub struct Reader {
    src: Src,
    pos: usize,
    marked: usize,
}

impl Reader {
    pub(super) fn new(src: Src) -> Self {
        Self { src, pos: 0, marked: 0 }
    }

    pub fn is_eof(&self) -> bool {
        self.curr().is_none()
    }

    pub fn pos(&self) -> usize {
        self.pos
    }

    pub fn curr(&self) -> Option<&str> {
        self.src.get(self.pos)
    }

    pub fn curr_to(&self, additional: usize) -> Option<&str> {
        self.src.get(self.pos .. self.pos + additional)
    }

    pub fn marked(&self) -> usize {
        self.marked
    }

    pub fn src(&self) -> &Src {
        &self.src
    }

    pub fn location(&self) -> Location {
        Location::new(self.src.clone(), self.pos)
    }

    pub fn span(&self) -> Span {
        if self.marked < self.pos {
            let loc = Location::new(self.src.clone(), self.marked);
            Span::new(loc, self.pos - self.marked)
        } else {
            Span::new(self.location(), self.marked - self.pos)
        }
    }

    pub fn mark(&mut self) {
        self.marked = self.pos;
    }

    pub fn next(&mut self) -> bool {
        self.advance(1) == 1
    }

    pub fn prev(&mut self) -> bool {
        self.rollback(1) == 1
    }

    pub fn advance(&mut self, count: usize) -> usize {
        let advanced = count.min(self.src.len() - self.pos);
        self.pos += advanced;
        advanced
    }

    pub fn rollback(&mut self, count: usize) -> usize {
        let rolled = count.min(self.pos);
        self.pos -= rolled;
        rolled
    }

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

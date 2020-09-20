use std::{cell::RefCell, collections::HashSet, rc::Rc};

#[derive(Debug, Default)]
struct Interner {
    table: HashSet<Rc<str>>,
}

impl Interner {
    fn intern(&mut self, string: &str) -> Rc<str> {
        self.table.get(string).map(Clone::clone).unwrap_or_else(|| {
            let rc = Rc::<str>::from(string);
            self.table.insert(rc.clone());
            rc
        })
    }

    fn clear(&mut self) {
        self.table = HashSet::new();
    }
}

thread_local! {
    static INTERNER: RefCell<Interner> = RefCell::new(Interner::default());
}

pub fn get(s: &str) -> Rc<str> {
    INTERNER.with(|inter| inter.borrow_mut().intern(s))
}

pub fn clear() {
    INTERNER.with(|inter| inter.borrow_mut().clear())
}

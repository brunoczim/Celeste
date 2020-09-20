//! This crate provides thread-local string internship.

use std::{cell::RefCell, collections::HashSet, rc::Rc};

/// The inner implementation of the interner.
#[derive(Debug, Default)]
struct Interner {
    /// Table of interned strings.
    table: HashSet<Rc<str>>,
}

impl Interner {
    /// Returns an interned version of the given string, interning if not
    /// already interned.
    fn intern(&mut self, string: &str) -> Rc<str> {
        self.table.get(string).map(Clone::clone).unwrap_or_else(|| {
            let rc = Rc::<str>::from(string);
            self.table.insert(rc.clone());
            rc
        })
    }

    /// Clears all interned strings, freeing memory of the table.
    fn clear(&mut self) {
        self.table = HashSet::new();
    }
}

thread_local! {
    /// The thread interner.
    static INTERNER: RefCell<Interner> = RefCell::new(Interner::default());
}

/// Returns an interned version of the given string, interning if not already
/// interned.
pub fn get(s: &str) -> Rc<str> {
    INTERNER.with(|inter| inter.borrow_mut().intern(s))
}

/// Clears all interned strings, freeing memory of the table.
pub fn clear() {
    INTERNER.with(|inter| inter.borrow_mut().clear())
}

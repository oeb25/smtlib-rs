use bumpalo::Bump;

use crate::ast::Term;

#[derive(Debug)]
pub struct Storage {
    arena: Bump,
}

impl PartialEq for Storage {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(&self.arena, &other.arena)
    }
}

impl Eq for Storage {}

impl Storage {
    pub fn new() -> Storage {
        Storage { arena: Bump::new() }
    }
    pub fn alloc<T>(&self, item: T) -> &T {
        self.arena.alloc(item)
    }
    pub fn alloc_slice<'a, T: Clone>(&'a self, items: &[T]) -> &'a [T] {
        self.arena.alloc_slice_clone(items)
    }
    pub fn alloc_str<'a>(&'a self, src: &str) -> &'a str {
        // TODO: consider adding string interning
        self.arena.alloc_str(src)
    }
    pub fn alloc_term<'a>(&'a self, term: Term<'a>) -> &'a Term<'a> {
        self.alloc(term)
    }
}

impl Default for Storage {
    fn default() -> Self {
        Self::new()
    }
}

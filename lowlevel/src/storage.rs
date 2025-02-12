use bumpalo::Bump;

#[derive(Debug)]
pub struct Storage {
    arena: Bump,
}

impl Storage {
    pub fn new() -> Storage {
        Storage { arena: Bump::new() }
    }
    pub(crate) fn alloc<T>(&self, item: T) -> &T {
        self.arena.alloc(item)
    }
    pub(crate) fn alloc_slice<'a, T: Clone>(&'a self, items: &[T]) -> &'a [T] {
        self.arena.alloc_slice_clone(items)
    }
    pub(crate) fn alloc_str<'a>(&'a self, src: &str) -> &'a str {
        // TODO: consider adding string interning
        self.arena.alloc_str(src)
    }
}

impl Default for Storage {
    fn default() -> Self {
        Self::new()
    }
}

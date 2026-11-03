use std::ptr::NonNull;

struct Node {
    next: Option<NonNull<Node>>,
}

pub struct List {
    head: Option<NonNull<Node>>,
}

impl List {
    pub fn new() -> Self {
        Self { head: None }
    }

    pub fn push(&mut self) {
        let node = Box::new(Node { next: self.head });
        self.head = Some(NonNull::from(Box::leak(node)));
    }

    pub fn clear(&mut self) {
        let mut current = self.head;
        unsafe {
            while let Some(node) = current {
                current = node.as_ref().next;
                drop(Box::from_raw(node.as_ptr()));
            }
        }
        self.head = None;
    }

    pub fn clear_in_closure(&mut self) {
        (|| {
            let mut current = self.head;
            unsafe {
                while let Some(node) = current {
                    current = node.as_ref().next;
                    drop(Box::from_raw(node.as_ptr()));
                }
            }
            self.head = None;
        })()
    }
}

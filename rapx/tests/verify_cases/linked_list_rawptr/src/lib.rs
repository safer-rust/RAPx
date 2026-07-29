#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(unused)]

#[rapx::invariant(any(Null(prev), (Align(prev, Node), ValidPtr(prev, Node, 1), Allocated(prev, Node, 1), Typed(prev, Node), Owning(prev))))]
#[rapx::invariant(any(Null(next), (Align(next, Node), ValidPtr(next, Node, 1), Allocated(next, Node, 1), Typed(next, Node), Owning(next))))]
struct Node {
    value: i32,
    prev: *mut Node,
    next: *mut Node,
}

#[rapx::invariant(any(Null(head), (Align(head, Node), ValidPtr(head, Node, 1), Allocated(head, Node, 1), Typed(head, Node), Owning(head))))]
#[rapx::invariant(any(Null(tail), (Align(tail, Node), ValidPtr(tail, Node, 1), Allocated(tail, Node, 1), Typed(tail, Node), Owning(tail))))]
struct LinkedList {
    head: *mut Node,
    tail: *mut Node,
    len: usize,
}

impl LinkedList {
    #[rapx::verify]
    pub fn new() -> Self {
        LinkedList {
            head: std::ptr::null_mut(),
            tail: std::ptr::null_mut(),
            len: 0,
        }
    }

    #[rapx::verify]
    pub fn len(&self) -> usize {
        self.len
    }

    #[rapx::verify]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    #[rapx::verify]
    pub fn push_back(&mut self, value: i32) {
        let node = Box::into_raw(Box::new(Node {
            value,
            prev: self.tail,
            next: std::ptr::null_mut(),
        }));
        unsafe {
            if self.tail.is_null() {
                self.head = node;
                self.tail = node;
            } else {
                (*self.tail).next = node;
                (*node).prev = self.tail;
                self.tail = node;
            }
        }
        self.len += 1;
    }

    #[rapx::verify]
    pub fn push_front(&mut self, value: i32) {
        let node = Box::into_raw(Box::new(Node {
            value,
            prev: std::ptr::null_mut(),
            next: self.head,
        }));
        unsafe {
            if self.head.is_null() {
                self.head = node;
                self.tail = node;
            } else {
                (*self.head).prev = node;
                (*node).next = self.head;
                self.head = node;
            }
        }
        self.len += 1;
    }

    #[rapx::verify]
    pub fn pop_front(&mut self) -> Option<i32> {
        let old_head = if self.head.is_null() {
            return None;
        } else {
            self.head
        };
        let (value, next) = unsafe {
            let r = &*old_head;
            (r.value, r.next)
        };
        if next.is_null() {
            self.head = std::ptr::null_mut();
            self.tail = std::ptr::null_mut();
        } else {
            self.head = next;
            unsafe {
                (*self.head).prev = std::ptr::null_mut();
            }
        }
        unsafe {
            drop(Box::from_raw(old_head));
        }
        self.len -= 1;
        Some(value)
    }

    #[rapx::verify]
    pub fn pop_back(&mut self) -> Option<i32> {
        let old_tail = if self.tail.is_null() {
            return None;
        } else {
            self.tail
        };
        let (value, prev) = unsafe {
            let r = &*old_tail;
            (r.value, r.prev)
        };
        if prev.is_null() {
            self.head = std::ptr::null_mut();
            self.tail = std::ptr::null_mut();
        } else {
            self.tail = prev;
            unsafe {
                (*self.tail).next = std::ptr::null_mut();
            }
        }
        unsafe {
            drop(Box::from_raw(old_tail));
        }
        self.len -= 1;
        Some(value)
    }

    #[rapx::verify]
    pub fn front(&self) -> Option<i32> {
        if self.head.is_null() {
            None
        } else {
            unsafe { Some((*self.head).value) }
        }
    }

    #[rapx::verify]
    pub fn back(&self) -> Option<i32> {
        if self.tail.is_null() {
            None
        } else {
            unsafe { Some((*self.tail).value) }
        }
    }

    #[rapx::verify]
    pub fn front_mut(&mut self) -> Option<&mut i32> {
        if self.head.is_null() {
            None
        } else {
            unsafe { Some(&mut (*self.head).value) }
        }
    }

    #[rapx::verify]
    pub fn back_mut(&mut self) -> Option<&mut i32> {
        if self.tail.is_null() {
            None
        } else {
            unsafe { Some(&mut (*self.tail).value) }
        }
    }

    #[rapx::verify]
    pub fn clear(&mut self) {
        let mut current = self.head;
        unsafe {
            while !current.is_null() {
                let next = (*current).next;
                drop(Box::from_raw(current));
                current = next;
            }
        }
        self.head = std::ptr::null_mut();
        self.tail = std::ptr::null_mut();
        self.len = 0;
    }

    #[rapx::verify]
    pub fn from_vec(values: Vec<i32>) -> Self {
        let mut list = Self::new();
        for value in values {
            list.push_back(value);
        }
        list
    }
}

impl Drop for LinkedList {
    fn drop(&mut self) {
        let mut current = self.head;
        unsafe {
            while !current.is_null() {
                let next = (*current).next;
                drop(Box::from_raw(current));
                current = next;
            }
        }
    }
}

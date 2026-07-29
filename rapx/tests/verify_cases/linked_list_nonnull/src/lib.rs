#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(unused)]

use std::ptr::NonNull;

#[rapx::invariant(Align(prev.unwrap_some(), Node))]
#[rapx::invariant(Allocated(prev.unwrap_some(), Node, 1))]
#[rapx::invariant(Typed(prev.unwrap_some(), Node))]
#[rapx::invariant(Owning(prev.unwrap_some()))]
#[rapx::invariant(Align(next.unwrap_some(), Node))]
#[rapx::invariant(Allocated(next.unwrap_some(), Node, 1))]
#[rapx::invariant(Typed(next.unwrap_some(), Node))]
#[rapx::invariant(Owning(next.unwrap_some()))]
struct Node {
    value: i32,
    prev: Option<NonNull<Node>>,
    next: Option<NonNull<Node>>,
}

#[rapx::invariant(Align(head.unwrap_some(), Node))]
#[rapx::invariant(Allocated(head.unwrap_some(), Node, 1))]
#[rapx::invariant(Typed(head.unwrap_some(), Node))]
#[rapx::invariant(Owning(head.unwrap_some()))]
#[rapx::invariant(Align(tail.unwrap_some(), Node))]
#[rapx::invariant(Allocated(tail.unwrap_some(), Node, 1))]
#[rapx::invariant(Typed(tail.unwrap_some(), Node))]
#[rapx::invariant(Owning(tail.unwrap_some()))]
struct LinkedList {
    head: Option<NonNull<Node>>,
    tail: Option<NonNull<Node>>,
    len: usize,
}

impl LinkedList {
    #[rapx::verify]
    pub fn new() -> Self { LinkedList { head: None, tail: None, len: 0 } }

    #[rapx::verify]
    pub fn len(&self) -> usize { self.len }

    #[rapx::verify]
    pub fn is_empty(&self) -> bool { self.len == 0 }

    #[rapx::verify]
    pub fn push_back(&mut self, value: i32) {
        let node = Box::new(Node { value, prev: self.tail, next: None });
        let mut node = NonNull::from(Box::leak(node));
        unsafe { match self.tail { None => { self.head = Some(node); self.tail = Some(node); } Some(mut tail) => { tail.as_mut().next = Some(node); self.tail = Some(node); } } }
        self.len += 1;
    }

    #[rapx::verify]
    pub fn push_front(&mut self, value: i32) {
        let node = Box::new(Node { value, prev: None, next: self.head });
        let mut node = NonNull::from(Box::leak(node));
        unsafe { match self.head { None => { self.head = Some(node); self.tail = Some(node); } Some(mut head) => { head.as_mut().prev = Some(node); self.head = Some(node); } } }
        self.len += 1;
    }

    #[rapx::verify]
    pub fn pop_front(&mut self) -> Option<i32> {
        let head = match self.head { Some(h) => h, None => return None };
        let (value, next) = unsafe { let r = head.as_ref(); (r.value, r.next) };
        unsafe { drop(Box::from_raw(head.as_ptr())); }
        match next { None => { self.head = None; self.tail = None; } Some(mut next) => { unsafe { next.as_mut().prev = None; } self.head = Some(next); } }
        self.len -= 1; Some(value)
    }

    #[rapx::verify]
    pub fn pop_back(&mut self) -> Option<i32> {
        let tail = match self.tail { Some(t) => t, None => return None };
        let (value, prev) = unsafe { let r = tail.as_ref(); (r.value, r.prev) };
        unsafe { match prev { Some(mut prev_node) => { let prev_ref = prev_node.as_mut(); match prev_ref.next { Some(owned_tail) => { prev_ref.next = None; drop(Box::from_raw(owned_tail.as_ptr())); } None => {} } self.tail = Some(prev_node); } None => { match self.head { Some(head) => { drop(Box::from_raw(head.as_ptr())); } None => {} } self.head = None; self.tail = None; } } }
        self.len -= 1; Some(value)
    }

    #[rapx::verify]
    pub fn front(&self) -> Option<i32> { self.head.map(|node| unsafe { node.as_ref().value }) }

    #[rapx::verify]
    pub fn back(&self) -> Option<i32> { self.tail.map(|node| unsafe { node.as_ref().value }) }

    #[rapx::verify]
    pub fn front_mut(&mut self) -> Option<&mut i32> { match self.head { Some(mut node) => Some(unsafe { &mut node.as_mut().value }), None => None } }

    #[rapx::verify]
    pub fn back_mut(&mut self) -> Option<&mut i32> { match self.tail { Some(mut node) => Some(unsafe { &mut node.as_mut().value }), None => None } }

    #[rapx::verify]
    pub fn clear(&mut self) {
        let mut current = self.head;
        unsafe { while let Some(node) = current { current = node.as_ref().next; drop(Box::from_raw(node.as_ptr())); } }
        self.head = None; self.tail = None; self.len = 0;
    }

    #[rapx::verify]
    pub fn from_vec(values: Vec<i32>) -> Self { let mut list = Self::new(); for value in values { list.push_back(value); } list }
}

impl Drop for LinkedList {
    fn drop(&mut self) {
        let mut current = self.head;
        unsafe { while let Some(node) = current { current = node.as_ref().next; drop(Box::from_raw(node.as_ptr())); } }
    }
}

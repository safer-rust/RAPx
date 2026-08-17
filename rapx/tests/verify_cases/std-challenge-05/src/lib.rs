#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(unsafe_op_in_unsafe_fn)]
#![allow(dead_code)]

// ========================================================================
// Challenge 5: Verify functions iterating over inductive data type:
//               `alloc::collections::linked_list`
//
// A faithful, self-contained port of
// `library/alloc/src/collections/linked_list.rs` (see
// https://model-checking.github.io/verify-rust-std/challenges/0005-linked-list.html).
//
// The internal representation is a doubly-linked list of `Node`s, an
// inductive (recursive) data type.  The challenge requires *unbounded*
// verification: every function must be memory-safe for linked lists of
// arbitrary shape.  RAPx discharges this obligation through the pointer
// invariants declared on `Node::prev` / `Node::next` and on `LinkedList`
// `head` / `tail`: any node reachable by following `next` (or `prev`)
// from a well-formed list is again a well-formed node.
//
// The port stays faithful to `std`, with two mechanical adaptations required
// for RAPx:
//   * the generic allocator `A: Allocator` is dropped in favor of the
//     global allocator (`Box` / `Box::from_raw` instead of `Box::new_in` /
//     `Box::from_raw_in`);
//   * the challenge lists `retain_mut` as a success criterion, but `std` only
//     exposes `retain` (which already takes `FnMut(&mut T) -> bool`); only the
//     functions that actually exist in `std` are ported here.
// ========================================================================
// ========================================================================

use std::marker::PhantomData;
use std::mem;
use std::ptr::NonNull;

// ========================================================================
// Node
// ========================================================================

#[rapx::invariant(Align(prev.unwrap_some(), Node))]
#[rapx::invariant(Allocated(prev.unwrap_some(), Node, 1))]
#[rapx::invariant(Typed(prev.unwrap_some(), Node))]
#[rapx::invariant(Owning(prev.unwrap_some()))]
#[rapx::invariant(Align(next.unwrap_some(), Node))]
#[rapx::invariant(Allocated(next.unwrap_some(), Node, 1))]
#[rapx::invariant(Typed(next.unwrap_some(), Node))]
#[rapx::invariant(Owning(next.unwrap_some()))]
struct Node<T> {
    next: Option<NonNull<Node<T>>>,
    prev: Option<NonNull<Node<T>>>,
    element: T,
}

impl<T> Node<T> {
    fn new(element: T) -> Self {
        Node { next: None, prev: None, element }
    }

    fn into_element(self: Box<Self>) -> T {
        self.element
    }
}

// ========================================================================
// Iter / IterMut
// ========================================================================

pub struct Iter<'a, T: 'a> {
    head: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
    len: usize,
    marker: PhantomData<&'a Node<T>>,
}

pub struct IterMut<'a, T: 'a> {
    head: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
    len: usize,
    marker: PhantomData<&'a mut Node<T>>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<&'a T> {
        if self.len == 0 {
            None
        } else {
            self.head.map(|node| unsafe {
                // Need an unbound lifetime to get 'a
                let node = &*node.as_ptr();
                self.len -= 1;
                self.head = node.next;
                &node.element
            })
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a T> {
        if self.len == 0 {
            None
        } else {
            self.tail.map(|node| unsafe {
                // Need an unbound lifetime to get 'a
                let node = &*node.as_ptr();
                self.len -= 1;
                self.tail = node.prev;
                &node.element
            })
        }
    }
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    #[inline]
    fn next(&mut self) -> Option<&'a mut T> {
        if self.len == 0 {
            None
        } else {
            self.head.map(|node| unsafe {
                // Need an unbound lifetime to get 'a
                let node = &mut *node.as_ptr();
                self.len -= 1;
                self.head = node.next;
                &mut node.element
            })
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a, T> DoubleEndedIterator for IterMut<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a mut T> {
        if self.len == 0 {
            None
        } else {
            self.tail.map(|node| unsafe {
                // Need an unbound lifetime to get 'a
                let node = &mut *node.as_ptr();
                self.len -= 1;
                self.tail = node.prev;
                &mut node.element
            })
        }
    }
}

// ========================================================================
// CursorMut
// ========================================================================

pub struct CursorMut<'a, T: 'a> {
    index: usize,
    current: Option<NonNull<Node<T>>>,
    list: &'a mut LinkedList<T>,
}

impl<'a, T> CursorMut<'a, T> {
    /// Moves the cursor to the next element of the `LinkedList`.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this will move it to
    /// the first element of the `LinkedList`. If it is pointing to the last
    /// element of the `LinkedList` then this will move it to the "ghost" non-element.
    pub fn move_next(&mut self) {
        match self.current.take() {
            // We had no current element; the cursor was sitting at the start position
            // Next element should be the head of the list
            None => {
                self.current = self.list.head;
                self.index = 0;
            }
            // We had a previous element, so let's go to its next
            Some(current) => unsafe {
                self.current = current.as_ref().next;
                self.index += 1;
            },
        }
    }

    /// Moves the cursor to the previous element of the `LinkedList`.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this will move it to
    /// the last element of the `LinkedList`. If it is pointing to the first
    /// element of the `LinkedList` then this will move it to the "ghost" non-element.
    pub fn move_prev(&mut self) {
        match self.current.take() {
            // No current. We're at the start of the list. Yield None and jump to the end.
            None => {
                self.current = self.list.tail;
                self.index = self.list.len().checked_sub(1).unwrap_or(0);
            }
            // Have a prev. Yield it and go to the previous element.
            Some(current) => unsafe {
                self.current = current.as_ref().prev;
                self.index = self.index.checked_sub(1).unwrap_or_else(|| self.list.len());
            },
        }
    }

    /// Returns a reference to the element that the cursor is currently
    /// pointing to.
    ///
    /// This returns `None` if the cursor is currently pointing to the
    /// "ghost" non-element.
    pub fn current(&mut self) -> Option<&mut T> {
        unsafe { self.current.map(|current| &mut (*current.as_ptr()).element) }
    }

    /// Removes the current element from the `LinkedList`.
    ///
    /// The element that was removed is returned, and the cursor is
    /// moved to point to the next element in the `LinkedList`.
    ///
    /// If the cursor is currently pointing to the "ghost" non-element then no element
    /// is removed and `None` is returned.
    pub fn remove_current(&mut self) -> Option<T> {
        let unlinked_node = self.current?;
        unsafe {
            self.current = unlinked_node.as_ref().next;
            self.list.unlink_node(unlinked_node);
            let unlinked_node = Box::from_raw(unlinked_node.as_ptr());
            Some(unlinked_node.element)
        }
    }
}

// ========================================================================
// ExtractIf
// ========================================================================

pub struct ExtractIf<'a, T: 'a, F: 'a> {
    list: &'a mut LinkedList<T>,
    it: Option<NonNull<Node<T>>>,
    pred: F,
    idx: usize,
    old_len: usize,
}

impl<T, F> Iterator for ExtractIf<'_, T, F>
where
    F: FnMut(&mut T) -> bool,
{
    type Item = T;

    fn next(&mut self) -> Option<T> {
        while let Some(mut node) = self.it {
            unsafe {
                self.it = node.as_ref().next;
                self.idx += 1;

                if (self.pred)(&mut node.as_mut().element) {
                    // `unlink_node` is okay with aliasing `element` references.
                    self.list.unlink_node(node);
                    return Some(Box::from_raw(node.as_ptr()).element);
                }
            }
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.old_len - self.idx))
    }
}

// ========================================================================
// LinkedList
// ========================================================================

#[rapx::invariant(Align(head.unwrap_some(), Node))]
#[rapx::invariant(Allocated(head.unwrap_some(), Node, 1))]
#[rapx::invariant(Typed(head.unwrap_some(), Node))]
#[rapx::invariant(Owning(head.unwrap_some()))]
#[rapx::invariant(Align(tail.unwrap_some(), Node))]
#[rapx::invariant(Allocated(tail.unwrap_some(), Node, 1))]
#[rapx::invariant(Typed(tail.unwrap_some(), Node))]
#[rapx::invariant(Owning(tail.unwrap_some()))]
struct LinkedList<T> {
    head: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
    len: usize,
    marker: PhantomData<Box<Node<T>>>,
}

// private methods
impl<T> LinkedList<T> {
    /// Adds the given node to the front of the list.
    ///
    /// # Safety
    /// `node` must point to a valid node that was boxed and leaked using the list's allocator.
    /// This method takes ownership of the node, so the pointer should not be used again.
    #[inline]
    #[rapx::requires(Align(node, Node))]
    #[rapx::requires(Allocated(node, Node, 1))]
    #[rapx::requires(Typed(node, Node))]
    #[rapx::requires(Owning(node))]
    unsafe fn push_front_node(&mut self, node: NonNull<Node<T>>) {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        unsafe {
            (*node.as_ptr()).next = self.head;
            (*node.as_ptr()).prev = None;
            let node = Some(node);

            match self.head {
                None => self.tail = node,
                // Not creating new mutable (unique!) references overlapping `element`.
                Some(head) => (*head.as_ptr()).prev = node,
            }

            self.head = node;
            self.len += 1;
        }
    }

    /// Removes and returns the node at the front of the list.
    #[inline]
    fn pop_front_node(&mut self) -> Option<Box<Node<T>>> {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        self.head.map(|node| unsafe {
            let node = Box::from_raw(node.as_ptr());
            self.head = node.next;

            match self.head {
                None => self.tail = None,
                // Not creating new mutable (unique!) references overlapping `element`.
                Some(head) => (*head.as_ptr()).prev = None,
            }

            self.len -= 1;
            node
        })
    }

    /// Adds the given node to the back of the list.
    ///
    /// # Safety
    /// `node` must point to a valid node that was boxed and leaked using the list's allocator.
    /// This method takes ownership of the node, so the pointer should not be used again.
    #[inline]
    #[rapx::requires(Align(node, Node))]
    #[rapx::requires(Allocated(node, Node, 1))]
    #[rapx::requires(Typed(node, Node))]
    #[rapx::requires(Owning(node))]
    unsafe fn push_back_node(&mut self, node: NonNull<Node<T>>) {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        unsafe {
            (*node.as_ptr()).next = None;
            (*node.as_ptr()).prev = self.tail;
            let node = Some(node);

            match self.tail {
                None => self.head = node,
                // Not creating new mutable (unique!) references overlapping `element`.
                Some(tail) => (*tail.as_ptr()).next = node,
            }

            self.tail = node;
            self.len += 1;
        }
    }

    /// Removes and returns the node at the back of the list.
    #[inline]
    fn pop_back_node(&mut self) -> Option<Box<Node<T>>> {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        self.tail.map(|node| unsafe {
            let node = Box::from_raw(node.as_ptr());
            self.tail = node.prev;

            match self.tail {
                None => self.head = None,
                // Not creating new mutable (unique!) references overlapping `element`.
                Some(tail) => (*tail.as_ptr()).next = None,
            }

            self.len -= 1;
            node
        })
    }

    /// Unlinks the specified node from the current list.
    ///
    /// Warning: this will not check that the provided node belongs to the current list.
    ///
    /// This method takes care not to create mutable references to `element`, to
    /// maintain validity of aliasing pointers.
    #[inline]
    #[rapx::requires(Align(node, Node))]
    #[rapx::requires(Allocated(node, Node, 1))]
    #[rapx::requires(Typed(node, Node))]
    #[rapx::requires(Owning(node))]
    unsafe fn unlink_node(&mut self, mut node: NonNull<Node<T>>) {
        let node = unsafe { node.as_mut() }; // this one is ours now, we can create an &mut.

        // Not creating new mutable (unique!) references overlapping `element`.
        match node.prev {
            Some(prev) => unsafe { (*prev.as_ptr()).next = node.next },
            // this node is the head node
            None => self.head = node.next,
        };

        match node.next {
            Some(next) => unsafe { (*next.as_ptr()).prev = node.prev },
            // this node is the tail node
            None => self.tail = node.prev,
        };

        self.len -= 1;
    }

    #[inline]
    unsafe fn split_off_after_node(
        &mut self,
        split_node: Option<NonNull<Node<T>>>,
        at: usize,
    ) -> Self {
        // The split node is the new tail node of the first part and owns
        // the head of the second part.
        if let Some(mut split_node) = split_node {
            let second_part_head;
            let second_part_tail;
            unsafe {
                second_part_head = split_node.as_mut().next.take();
            }
            if let Some(mut head) = second_part_head {
                unsafe {
                    head.as_mut().prev = None;
                }
                second_part_tail = self.tail;
            } else {
                second_part_tail = None;
            }

            let second_part = LinkedList {
                head: second_part_head,
                tail: second_part_tail,
                len: self.len - at,
                marker: PhantomData,
            };

            // Fix the tail ptr of the first part
            self.tail = Some(split_node);
            self.len = at;

            second_part
        } else {
            mem::replace(self, LinkedList::new())
        }
    }
}

impl<T> LinkedList<T> {
    #[rapx::verify]
    pub fn new() -> Self {
        LinkedList { head: None, tail: None, len: 0, marker: PhantomData }
    }

    #[rapx::verify]
    pub fn len(&self) -> usize {
        self.len
    }

    #[rapx::verify]
    pub fn is_empty(&self) -> bool {
        self.head.is_none()
    }

    /// Provides a forward iterator.
    #[rapx::verify]
    pub fn iter(&self) -> Iter<'_, T> {
        Iter { head: self.head, tail: self.tail, len: self.len, marker: PhantomData }
    }

    /// Provides a forward iterator with mutable references.
    #[rapx::verify]
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut { head: self.head, tail: self.tail, len: self.len, marker: PhantomData }
    }

    /// Provides a cursor with editing operations at the front element.
    #[rapx::verify]
    pub fn cursor_front_mut(&mut self) -> CursorMut<'_, T> {
        CursorMut { index: 0, current: self.head, list: self }
    }

    /// Provides a cursor with editing operations at the back element.
    #[rapx::verify]
    pub fn cursor_back_mut(&mut self) -> CursorMut<'_, T> {
        CursorMut { index: self.len.checked_sub(1).unwrap_or(0), current: self.tail, list: self }
    }

    /// Adds an element to the front of the list.
    ///
    /// Safe wrapper over `push_front_node` (not part of the challenge's success
    /// criteria, so it is not `#[rapx::verify]`-annotated).
    pub fn push_front(&mut self, elt: T) {
        let node = NonNull::from(Box::leak(Box::new(Node::new(elt))));
        // SAFETY: node is a unique pointer to a node we boxed and leaked.
        unsafe { self.push_front_node(node) }
    }

    /// Adds an element to the back of the list.
    ///
    /// Safe wrapper over `push_back_node` (not part of the challenge's success
    /// criteria, so it is not `#[rapx::verify]`-annotated).
    pub fn push_back(&mut self, elt: T) {
        let node = NonNull::from(Box::leak(Box::new(Node::new(elt))));
        // SAFETY: node is a unique pointer to a node we boxed and leaked.
        unsafe { self.push_back_node(node) }
    }

    /// Removes the first element and returns it, or `None` if the list is
    /// empty.
    #[rapx::verify]
    pub fn pop_front(&mut self) -> Option<T> {
        self.pop_front_node().map(Node::into_element)
    }

    /// Removes the last element from a list and returns it, or `None` if
    /// it is empty.
    #[rapx::verify]
    pub fn pop_back(&mut self) -> Option<T> {
        self.pop_back_node().map(Node::into_element)
    }

    // ====================================================================
    // Challenge function: `clear`
    // ====================================================================
    #[rapx::verify]
    pub fn clear(&mut self) {
        // We need to drop the nodes while keeping the list's allocator (here the
        // global allocator).  We do this by moving (head, tail, len) into a new
        // temporary list and dropping it.
        drop(LinkedList {
            head: self.head.take(),
            tail: self.tail.take(),
            len: mem::take(&mut self.len),
            marker: PhantomData,
        });
    }

    // ====================================================================
    // Challenge function: `contains`
    // ====================================================================
    #[rapx::verify]
    pub fn contains(&self, x: &T) -> bool
    where
        T: PartialEq<T>,
    {
        self.iter().any(|e| e == x)
    }

    // ====================================================================
    // Challenge function: `split_off`
    // ====================================================================
    #[rapx::verify]
    pub fn split_off(&mut self, at: usize) -> LinkedList<T> {
        let len = self.len();
        assert!(at <= len, "Cannot split off at a nonexistent index");
        if at == 0 {
            return mem::replace(self, Self::new());
        } else if at == len {
            return Self::new();
        }

        // Below, we iterate towards the `i-1`th node, either from the start or the end,
        // depending on which would be faster.
        let split_node = if at - 1 <= len - 1 - (at - 1) {
            let mut iter = self.iter_mut();
            // instead of skipping using .skip() (which creates a new struct),
            // we skip manually so we can access the head field without
            // depending on implementation details of Skip
            for _ in 0..at - 1 {
                iter.next();
            }
            iter.head
        } else {
            // better off starting from the end
            let mut iter = self.iter_mut();
            for _ in 0..len - 1 - (at - 1) {
                iter.next_back();
            }
            iter.tail
        };
        unsafe { self.split_off_after_node(split_node, at) }
    }

    // ====================================================================
    // Challenge function: `remove`
    // ====================================================================
    #[rapx::verify]
    pub fn remove(&mut self, at: usize) -> T {
        let len = self.len();
        assert!(at < len, "Cannot remove at an index outside of the list bounds");

        // Below, we iterate towards the node at the given index, either from
        // the start or the end, depending on which would be faster.
        let offset_from_end = len - at - 1;
        if at <= offset_from_end {
            let mut cursor = self.cursor_front_mut();
            for _ in 0..at {
                cursor.move_next();
            }
            cursor.remove_current().unwrap()
        } else {
            let mut cursor = self.cursor_back_mut();
            for _ in 0..offset_from_end {
                cursor.move_prev();
            }
            cursor.remove_current().unwrap()
        }
    }

    // ====================================================================
    // Challenge function: `retain`
    // ====================================================================
    #[rapx::verify]
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut T) -> bool,
    {
        let mut cursor = self.cursor_front_mut();
        while let Some(node) = cursor.current() {
            if !f(node) {
                cursor.remove_current().unwrap();
            } else {
                cursor.move_next();
            }
        }
    }

    // ====================================================================
    // Challenge function: `extract_if`
    // ====================================================================
    #[rapx::verify]
    pub fn extract_if<F>(&mut self, filter: F) -> ExtractIf<'_, T, F>
    where
        F: FnMut(&mut T) -> bool,
    {
        // avoid borrow issues.
        let it = self.head;
        let old_len = self.len;

        ExtractIf { list: self, it, pred: filter, idx: 0, old_len }
    }
}

// ========================================================================
// Drop
// ========================================================================

impl<T> Drop for LinkedList<T> {
    fn drop(&mut self) {
        while self.pop_front_node().is_some() {}
    }
}

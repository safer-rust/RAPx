#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(unused)]

use std::ptr::NonNull;

#[rapx::invariant(Align(prev.unwrap_some(), Node))]
#[rapx::invariant(Align(next.unwrap_some(), Node))]
#[rapx::invariant(Allocated(next.unwrap_some(), Node, 1))]
#[rapx::invariant(Owning(next.unwrap_some()))]
struct Node {
    value: i32,
    prev: Option<NonNull<Node>>,
    next: Option<NonNull<Node>>,
}

#[rapx::invariant(Align(head.unwrap_some(), Node))]
#[rapx::invariant(Align(tail.unwrap_some(), Node))]
#[rapx::invariant(Allocated(head.unwrap_some(), Node, 1))]
#[rapx::invariant(Owning(head.unwrap_some()))]
struct LinkedList {
    head: Option<NonNull<Node>>,
    tail: Option<NonNull<Node>>,
}

impl LinkedList {
    #[rapx::verify]
    fn from_vec(values: Vec<i32>) -> Self {
        let mut list = LinkedList {
            head: None,
            tail: None,
        };

        for value in values {
            let node = Box::new(Node {
                value,
                prev: None,
                next: None,
            });

            let mut node = NonNull::from(Box::leak(node));

            unsafe {
                match list.tail {
                    None => {
                        list.head = Some(node);
                        list.tail = Some(node);
                    }

                    Some(mut tail) => {
                        tail.as_mut().next = Some(node);
                        node.as_mut().prev = Some(tail);
                        list.tail = Some(node);
                    }
                }
            }
        }

        list
    }
}

impl Drop for LinkedList {
    fn drop(&mut self) {
        let mut current = self.head;

        unsafe {
            while let Some(node) = current {
                current = node.as_ref().next;
                drop(Box::from_raw(node.as_ptr()));
            }
        }
    }
}

#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(unused)]

#[rapx::invariant(NonNull(prev))]
#[rapx::invariant(NonNull(next))]
#[rapx::invariant(Align(prev, Node))]
#[rapx::invariant(Align(next, Node))]
#[rapx::invariant(ValidPtr(next, Node, 1))]
#[rapx::invariant(Init(next, Node, 1))]
#[rapx::invariant(Owning(next))]
struct Node {
    value: i32,
    prev: *mut Node,
    next: *mut Node,
}

#[rapx::invariant(NonNull(head))]
#[rapx::invariant(NonNull(tail))]
#[rapx::invariant(Align(head, Node))]
#[rapx::invariant(Align(tail, Node))]
#[rapx::invariant(ValidPtr(head, Node, 1))]
#[rapx::invariant(Init(head, Node, 1))]
#[rapx::invariant(Owning(head))]
struct LinkedList {
    head: *mut Node,
    tail: *mut Node,
}

impl LinkedList {
    #[rapx::verify]
    fn from_vec(values: Vec<i32>) -> Self {
        let mut list = LinkedList {
            head: std::ptr::null_mut(),
            tail: std::ptr::null_mut(),
        };

        for value in values {
            let node = Box::into_raw(Box::new(Node {
                value,
                prev: std::ptr::null_mut(),
                next: std::ptr::null_mut(),
            }));

            unsafe {
                if list.tail.is_null() {
                    list.head = node;
                    list.tail = node;
                } else {
                    (*list.tail).next = node;
                    (*node).prev = list.tail;
                    list.tail = node;
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
            while !current.is_null() {
                let next = (*current).next;
                drop(Box::from_raw(current));
                current = next;
            }
        }
    }
}

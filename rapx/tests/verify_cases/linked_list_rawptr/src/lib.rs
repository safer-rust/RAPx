#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(unused)]

#[rapx::invariant(any(Null(next), (Align(next, Node), ValidPtr(next, Node, 1), Init(next, Node, 1), Owning(next))))]
struct Node {
    value: i32,
    prev: *mut Node,
    next: *mut Node,
}

#[rapx::invariant(any(Null(head), (Align(head, Node), ValidPtr(head, Node, 1), Init(head, Node, 1), Owning(head))))]
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

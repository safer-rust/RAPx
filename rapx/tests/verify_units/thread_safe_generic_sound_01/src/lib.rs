#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// A generic Rc-like type: `Send` needs a `T: Send` bound; `Sync` always fails
// because the raw pointer is not synchronized.
#[rapx::invariant(Owning(ptr))]
#[rapx::invariant(Allocated(ptr))]
pub struct MyRcGeneric<T> {
    ptr: *mut MyRcBoxGeneric<T>,
}

pub struct MyRcBoxGeneric<T> {
    strong: usize,
    value: T,
}

impl<T> MyRcGeneric<T> {
    pub fn inc(&self) {
        unsafe { (*self.ptr).strong += 1 }
    }
}

#[rapx::verify]
unsafe impl<T: Send> Send for MyRcGeneric<T> {}

#[rapx::verify]
unsafe impl<T: Sync> Sync for MyRcGeneric<T> {}

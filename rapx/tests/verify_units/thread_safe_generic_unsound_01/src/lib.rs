#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// A generic Rc-like type without `T: Send`/`T: Sync` bounds: the `T` value
// field is unconstrained, so the impl cannot be proven sound.
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
unsafe impl<T> Send for MyRcGeneric<T> {}

#[rapx::verify]
unsafe impl<T> Sync for MyRcGeneric<T> {}

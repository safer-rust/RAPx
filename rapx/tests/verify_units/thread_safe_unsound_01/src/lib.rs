#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::rc::Rc;

// std `Rc`: a `!Send`/`!Sync` negative type.
pub struct RcHolder {
    rc: Rc<u8>,
}

#[rapx::verify]
unsafe impl Send for RcHolder {}

// An Rc-like type: `Clone` copies the raw pointer (aliasing the pointee), so
// the non-atomic `inc` write is a cross-thread data race.
pub struct MyRc {
    ptr: *mut MyRcBox,
}

pub struct MyRcBox {
    strong: usize,
    value: u8,
}

impl Clone for MyRc {
    fn clone(&self) -> Self {
        self.inc();
        MyRc { ptr: self.ptr }
    }
}

impl MyRc {
    pub fn inc(&self) {
        unsafe { (*self.ptr).strong += 1 }
    }
}

#[rapx::verify]
unsafe impl Send for MyRc {}

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

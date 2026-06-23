#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::marker::PhantomData;

pub struct MutSliceHost<'a, T> {
    ptr: *mut T,
    len: usize,
    _marker: PhantomData<&'a mut [T]>,
}

impl<'a, T> MutSliceHost<'a, T> {
    pub fn new(data: &'a mut [T]) -> Self {
        Self {
            ptr: data.as_mut_ptr(),
            len: data.len(),
            _marker: PhantomData,
        }
    }

    // SOUND: the mutable slice lifetime is tied to this `&mut self` borrow.
    #[rapx::verify]
    pub fn get_mut(&mut self) -> &mut [T] {
        unsafe { std::slice::from_raw_parts_mut(self.ptr, self.len) }
    }
}

#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::marker::PhantomData;

pub struct SliceHost<'a, T> {
    ptr: *const T,
    len: usize,
    _marker: PhantomData<&'a [T]>,
}

impl<'a, T> SliceHost<'a, T> {
    pub fn new(data: &'a [T]) -> Self {
        Self {
            ptr: data.as_ptr(),
            len: data.len(),
            _marker: PhantomData,
        }
    }

    // SOUND: the returned slice lifetime is tied to `&self`, not widened to `'a`.
    #[rapx::verify]
    pub fn get(&self) -> &[T] {
        unsafe { std::slice::from_raw_parts(self.ptr, self.len) }
    }
}

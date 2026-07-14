#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::marker::PhantomData;

pub struct DangerousAliaser<'a, T> {
    ptr: *mut T,
    len: usize,
    _marker: PhantomData<&'a mut [T]>,
}

impl<'a, T> DangerousAliaser<'a, T> {
    pub fn new(data: &'a mut [T]) -> Self {
        Self {
            ptr: data.as_mut_ptr(),
            len: data.len(),
            _marker: PhantomData,
        }
    }

    // UNSOUND: repeated calls manufacture multiple &'a mut [T] aliases.
    #[rapx::verify]
    pub fn get_mut(&mut self) -> &'a mut [T] {
        unsafe { std::slice::from_raw_parts_mut(self.ptr, self.len) }
    }
}

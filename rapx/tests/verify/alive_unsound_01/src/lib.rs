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

    // SOUND: `PhantomData<&'a mut [T]>` ties `'a` to `data`'s lifetime,
    // and `&mut self` prevents concurrent calls.  The raw pointer cannot
    // escape the borrowed context.  RAPx currently reports Alive | Failed
    // because it does not propagate lifetime information through PhantomData
    // and struct fields — a known engine limitation.
    #[rapx::verify]
    pub fn get_mut(&mut self) -> &'a mut [T] {
        unsafe { std::slice::from_raw_parts_mut(self.ptr, self.len) }
    }
}

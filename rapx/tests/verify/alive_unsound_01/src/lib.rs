#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::marker::PhantomData;

#[rapx::invariant(NonNull(ptr))]
#[rapx::invariant(ValidPtr(ptr, T, len))]
#[rapx::invariant(Init(ptr, T, len))]
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
    // and `&mut self` prevents concurrent calls.  Alive | Failed is a
    // verifier limitation (PhantomData lifetime not propagated).
    // NonNull / ValidPtr / Init are unproved due to type mismatch
    // between struct invariant `ValidPtr(ptr, T, len)` and
    // from_raw_parts_mut which needs `ValidPtr(ptr, u8, len * size_of::<T>())`.
    #[rapx::verify]
    pub fn get_mut(&mut self) -> &'a mut [T] {
        unsafe { std::slice::from_raw_parts_mut(self.ptr, self.len) }
    }
}

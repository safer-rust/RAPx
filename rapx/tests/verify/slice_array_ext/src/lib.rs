#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(unsafe_op_in_unsafe_fn)]

use std::slice::{from_raw_parts, from_raw_parts_mut};

pub trait SliceArrayExt<T, const N: usize> {
    fn as_flattened_ext(&self) -> &[T];
    fn as_flattened_mut_ext(&mut self) -> &mut [T];
}

impl<T, const N: usize> SliceArrayExt<T, N> for [[T; N]] {
    #[rapx::verify]
    fn as_flattened_ext(&self) -> &[T] {
        let len = self.len() * N;
        unsafe { from_raw_parts(self.as_ptr() as *const T, len) }
    }

    #[rapx::verify]
    fn as_flattened_mut_ext(&mut self) -> &mut [T] {
        let len = self.len() * N;
        unsafe { from_raw_parts_mut(self.as_mut_ptr() as *mut T, len) }
    }
}

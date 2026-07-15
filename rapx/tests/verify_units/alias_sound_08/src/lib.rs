#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::marker::PhantomData;

pub struct ReadOnlySlot<'a> {
    ptr: *const u32,
    _marker: PhantomData<&'a u32>,
}

impl<'a> ReadOnlySlot<'a> {
    pub fn new(value: &'a u32) -> Self {
        Self {
            ptr: value,
            _marker: PhantomData,
        }
    }

    // SOUND: the returned shared view is read-only and the struct exposes no writer.
    #[rapx::verify]
    pub fn as_slice(&self) -> &[u32] {
        unsafe { std::slice::from_raw_parts(self.ptr, 1) }
    }
}
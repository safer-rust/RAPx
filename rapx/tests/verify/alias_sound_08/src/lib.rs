#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

pub struct ReadOnlySlot {
    ptr: *const u32,
}

impl ReadOnlySlot {
    pub fn new(value: &u32) -> Self {
        Self { ptr: value }
    }

    // SOUND: the returned shared view is read-only and the struct exposes no writer.
    #[rapx::verify]
    pub fn as_slice<'a>(&self) -> &'a [u32] {
        unsafe { std::slice::from_raw_parts(self.ptr, 1) }
    }
}

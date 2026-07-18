#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::invariant(Owning(self.ptr))]
pub struct WriterSlot {
    ptr: *mut u32,
}

impl WriterSlot {
    pub fn new(value: &mut u32) -> Self {
        Self { ptr: value }
    }

    pub fn write_raw(&self, value: u32) {
        unsafe {
            *self.ptr = value;
        }
    }

    // UNSOUND: a public writer can mutate the original pointer while the returned view is live.
    #[rapx::verify]
    pub fn as_slice_mut<'a>(&self) -> &'a mut [u32] {
        unsafe { std::slice::from_raw_parts_mut(self.ptr, 1) }
    }
}

pub fn call_writer_after_view(slot: &WriterSlot) -> u32 {
    let view = slot.as_slice_mut();
    slot.write_raw(29);
    view[0]
}

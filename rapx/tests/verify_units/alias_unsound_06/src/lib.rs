#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::invariant(Owning(self.ptr))]
pub struct RawSlot {
    ptr: *mut u32,
}

impl RawSlot {
    // UNSOUND: the struct keeps the original raw pointer and writes through it while a mutable slice is live.
    #[rapx::verify]
    fn as_slice_mut<'a>(&self) -> &'a mut [u32] {
        unsafe { std::slice::from_raw_parts_mut(self.ptr, 1) }
    }

    fn write_raw(&self, value: u32) {
        unsafe {
            *self.ptr = value;
        }
    }
}

pub fn unsound_struct_method_raw_write_while_slice_live(value: &mut u32) -> u32 {
    let slot = RawSlot { ptr: value };
    let slice = slot.as_slice_mut();
    slot.write_raw(13);
    slice[0]
}

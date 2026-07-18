#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::invariant(Owning(self.ptr))]
pub struct PublicRawSlot {
    pub ptr: *mut u32,
}

impl PublicRawSlot {
    // UNSOUND: the returned mutable slice can outlive this call while `ptr` remains publicly exposed.
    #[rapx::verify]
    pub fn as_slice_mut<'a>(&self) -> &'a mut [u32] {
        unsafe { std::slice::from_raw_parts_mut(self.ptr, 1) }
    }
}

pub fn use_public_raw_after_view(slot: &PublicRawSlot) -> u32 {
    let view = slot.as_slice_mut();
    unsafe {
        *slot.ptr = 17;
    }
    view[0]
}

#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::invariant(Owning(self.ptr))]
pub struct GetterSlot {
    ptr: *mut u32,
}

impl GetterSlot {
    pub fn new(value: &mut u32) -> Self {
        Self { ptr: value }
    }

    pub fn raw_ptr(&self) -> *mut u32 {
        self.ptr
    }

    // UNSOUND: another safe API exposes the same raw pointer while the mutable view may live.
    #[rapx::verify]
    pub fn as_slice_mut<'a>(&self) -> &'a mut [u32] {
        unsafe { std::slice::from_raw_parts_mut(self.ptr, 1) }
    }
}

pub fn use_getter_raw_after_view(slot: &GetterSlot) -> u32 {
    let view = slot.as_slice_mut();
    unsafe {
        *slot.raw_ptr() = 23;
    }
    view[0]
}

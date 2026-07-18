#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

pub trait RawExpose {
    fn raw(&self) -> *mut u32;
}

#[rapx::invariant(Owning(self.ptr))]
pub struct TraitSlot {
    ptr: *mut u32,
}

impl TraitSlot {
    pub fn new(value: &mut u32) -> Self {
        Self { ptr: value }
    }

    // UNSOUND: a safe trait method exposes the same raw field while this view may live.
    #[rapx::verify]
    pub fn as_slice_mut<'a>(&self) -> &'a mut [u32] {
        unsafe { std::slice::from_raw_parts_mut(self.ptr, 1) }
    }
}

impl RawExpose for TraitSlot {
    fn raw(&self) -> *mut u32 {
        self.ptr
    }
}

pub fn use_trait_exposed_raw_after_view(slot: &TraitSlot) -> u32 {
    let view = slot.as_slice_mut();
    unsafe {
        *RawExpose::raw(slot) = 37;
    }
    view[0]
}

#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

pub struct SplitSlot {
    ptr: *mut u32,
}

impl SplitSlot {
    pub fn new(value: &mut u32) -> Self {
        Self { ptr: value }
    }

    pub fn borrow_raw(&self) -> RawHandle {
        RawHandle { ptr: self.ptr }
    }

    // UNSOUND: a second object can carry the original pointer past this producer API.
    #[rapx::verify]
    pub fn as_slice_mut<'a>(&self) -> &'a mut [u32] {
        unsafe { std::slice::from_raw_parts_mut(self.ptr, 1) }
    }
}

pub struct RawHandle {
    ptr: *mut u32,
}

impl RawHandle {
    pub fn write(&self, value: u32) {
        unsafe {
            *self.ptr = value;
        }
    }
}

pub fn raw_handle_after_view(slot: &SplitSlot) -> u32 {
    let handle = slot.borrow_raw();
    let view = slot.as_slice_mut();
    handle.write(31);
    view[0]
}

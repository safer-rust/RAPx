#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(Allocated(_ptr, u32, 1), kind = "precond")]
unsafe fn require_allocated_u32(_ptr: *const u32) {}

fn borrow_first(data: &[u32]) -> *const u32 {
    data.as_ptr()
}

// SOUND: the intra-call returns a pointer into a slice guarded as non-empty.
#[rapx::verify]
pub fn sound_intra_returns_slice_pointer(data: &[u32]) {
    if data.len() > 0 {
        let ptr = borrow_first(data);

        unsafe {
            require_allocated_u32(ptr);
        }
    }
}

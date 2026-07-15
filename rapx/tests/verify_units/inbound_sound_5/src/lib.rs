#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(InBound(_ptr, u32, 1), kind = "precond")]
unsafe fn require_intra_return_inbound(_ptr: *const u32) {}

fn slice_add(data: &[u32], index: usize) -> *const u32 {
    let ptr = data.as_ptr();
    unsafe { ptr.add(index) }
}

// SOUND: the callee returns `data.as_ptr().add(index)`, and the caller supplies the guard.
#[rapx::verify]
pub fn sound_intra_slice_add_guarded(data: &[u32], index: usize) {
    if index < data.len() {
        let current = slice_add(data, index);

        unsafe {
            require_intra_return_inbound(current);
        }
    }
}

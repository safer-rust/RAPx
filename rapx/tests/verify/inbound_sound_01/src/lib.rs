#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(InBound(_ptr, u32, 1), kind = "precond")]
unsafe fn require_ptr_add_inbound(_ptr: *const u32) {}

// SOUND: simulates `ptr.add(index)` followed by an unsafe access guarded by `index < len`.
#[rapx::verify]
pub fn sound_ptr_add_guarded(data: &[u32], index: usize) {
    if index < data.len() {
        let ptr = data.as_ptr();
        let current = unsafe { ptr.add(index) };

        unsafe {
            require_ptr_add_inbound(current);
        }
    }
}

#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(Allocated(_ptr, u32, 1), kind = "precond")]
unsafe fn require_allocated_u32(_ptr: *const u32) {}

// SOUND: each loop-internal pointer is guarded by `i < data.len()`.
#[rapx::verify]
pub fn sound_loop_slice_element_allocated(data: &[u32]) {
    let base = data.as_ptr();
    let mut i = 0_usize;

    while i < data.len() {
        let current = base.wrapping_add(i);

        unsafe {
            require_allocated_u32(current);
        }

        i += 1;
    }
}

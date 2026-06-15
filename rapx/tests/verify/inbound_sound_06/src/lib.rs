#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(InBound(_ptr, u32, 1), kind = "precond")]
unsafe fn require_loop_inbound(_ptr: *const u32) {}

// SOUND: loop-internal access is guarded by the SCC header condition `i < data.len()`.
#[rapx::verify]
pub fn sound_scc_loop_index_guard(data: &[u32]) {
    let ptr = data.as_ptr();
    let mut i = 0usize;

    while i < data.len() {
        let current = unsafe { ptr.add(i) };

        unsafe {
            require_loop_inbound(current);
        }

        i += 1;
    }
}

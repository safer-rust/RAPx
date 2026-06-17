#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(NonNull(_ptr), kind = "precond")]
unsafe fn require_nonnull(_ptr: *const u32) {}

// SOUND: the SCC mutates unrelated state and leaves the reference-derived pointer intact.
#[rapx::verify]
pub fn sound_scc_unrelated_state(limit: usize) {
    let value = 11_u32;
    let ptr = &value as *const u32;
    let mut i = 0;

    while i < limit {
        i += 1;
    }

    unsafe {
        require_nonnull(ptr);
    }
}

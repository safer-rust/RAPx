#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(NonNull(_ptr), kind = "precond")]
unsafe fn require_nonnull(_ptr: *const u32) {}

// UNSOUND: a loop may overwrite the pointer with null before it escapes.
#[rapx::verify]
pub fn unsound_scc_overwrites_with_null(limit: usize) {
    let value = 17_u32;
    let mut ptr = &value as *const u32;
    let mut i = 0;

    while i < limit {
        ptr = 0usize as *const u32;
        i += 1;
    }

    unsafe {
        require_nonnull(ptr);
    }
}

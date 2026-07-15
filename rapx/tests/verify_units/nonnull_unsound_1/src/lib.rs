#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(NonNull(_ptr), kind = "precond")]
unsafe fn require_nonnull(_ptr: *const u32) {}

// UNSOUND: the callsite receives an explicit null pointer.
#[rapx::verify]
pub fn unsound_explicit_null_constant() {
    let ptr = 0usize as *const u32;

    unsafe {
        require_nonnull(ptr);
    }
}

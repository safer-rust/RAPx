#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(NonNull(_ptr), kind = "precond")]
unsafe fn require_nonnull(_ptr: *const u32) {}

// SOUND: a stack reference remains non-null through copy and cast chains.
#[rapx::verify]
pub fn sound_ref_cast_copy_chain() {
    let value = 7_u32;
    let base = &value as *const u32;
    let erased = base as *const u8;
    let restored = erased as *const u32;
    let ptr = restored;

    unsafe {
        require_nonnull(ptr);
    }
}

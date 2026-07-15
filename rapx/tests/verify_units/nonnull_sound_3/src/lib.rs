#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(NonNull(_ptr), kind = "precond")]
unsafe fn require_nonnull(_ptr: *const u32) {}

fn ptr_from_ref(value: &u32) -> *const u32 {
    value as *const u32
}

// SOUND: the local helper returns a pointer derived from a reference argument.
#[rapx::verify]
pub fn sound_intra_helper_from_ref() {
    let value = 9_u32;
    let ptr = ptr_from_ref(&value);

    unsafe {
        require_nonnull(ptr);
    }
}

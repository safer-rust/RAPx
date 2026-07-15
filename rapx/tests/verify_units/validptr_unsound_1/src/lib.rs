#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(ValidPtr(_ptr, u32, 1), kind = "precond")]
unsafe fn require_valid_ptr_one(_ptr: *const u32) {}

// UNSOUND: a non-ZST dangling pointer is aligned/non-null but not allocated.
#[rapx::verify]
pub fn unsound_non_zst_dangling_not_allocated() {
    let ptr = std::ptr::NonNull::<u32>::dangling().as_ptr();

    unsafe {
        require_valid_ptr_one(ptr);
    }
}

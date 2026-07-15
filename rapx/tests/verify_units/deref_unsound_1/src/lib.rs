#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(Deref(_ptr, u32, 1), kind = "precond")]
unsafe fn require_deref_one(_ptr: *const u32) {}

// UNSOUND: one-past provenance is not dereferenceable for one element.
#[rapx::verify]
pub fn unsound_deref_one_past(data: &[u32]) {
    let ptr = unsafe { data.as_ptr().add(data.len()) };

    unsafe {
        require_deref_one(ptr);
    }
}

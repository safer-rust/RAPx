#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(Allocated(_ptr, u32, 1), kind = "precond")]
unsafe fn require_allocated_u32(_ptr: *const u32) {}

// UNSOUND: the Vec allocation is dropped before the pointer is checked.
#[rapx::verify]
pub fn unsound_vec_dropped_before_use() {
    let ptr = {
        let data = vec![1_u32];
        data.as_ptr()
    };

    unsafe {
        require_allocated_u32(ptr);
    }
}

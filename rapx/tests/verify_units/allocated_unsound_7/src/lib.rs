#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(Allocated(_ptr, u32, 1), kind = "precond")]
unsafe fn require_allocated_u32(_ptr: *const u32) {}

// UNSOUND: Vec growth can reallocate, invalidating the previously saved pointer.
#[rapx::verify]
pub fn unsound_vec_reallocates_old_pointer() {
    let mut data = Vec::with_capacity(1);
    data.push(1_u32);
    let ptr = data.as_ptr();

    for value in 2_u32..20 {
        data.push(value);
    }

    unsafe {
        require_allocated_u32(ptr);
    }
}

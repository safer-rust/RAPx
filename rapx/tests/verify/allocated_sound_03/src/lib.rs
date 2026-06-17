#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(Allocated(_ptr, u32, 3), kind = "precond")]
unsafe fn require_three_allocated_u32(_ptr: *const u32) {}

// SOUND: the Vec remains live and the guard proves at least three elements are backed.
#[rapx::verify]
pub fn sound_live_vec_allocated(data: Vec<u32>) {
    if data.len() < 3 {
        return;
    }

    let ptr = data.as_ptr();
    unsafe {
        require_three_allocated_u32(ptr);
    }
}

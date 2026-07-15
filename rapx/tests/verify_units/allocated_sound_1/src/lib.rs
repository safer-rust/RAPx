#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(Allocated(_ptr, u32, 1), kind = "precond")]
unsafe fn require_allocated_u32(_ptr: *const u32) {}

// SOUND: raw pointer is derived from a live stack local.
#[rapx::verify]
pub fn sound_stack_local_allocated() {
    let value = 7_u32;
    let ptr = &value as *const u32;

    unsafe {
        require_allocated_u32(ptr);
    }
}

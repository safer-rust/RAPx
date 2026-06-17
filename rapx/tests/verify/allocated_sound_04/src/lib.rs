#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(Allocated(_ptr, u32, 1), kind = "precond")]
unsafe fn require_allocated_u32(_ptr: *const u32) {}

// SOUND: the Box allocation is still owned by the caller when the raw pointer is checked.
#[rapx::verify]
pub fn sound_live_box_allocated(value: Box<u32>) {
    let ptr = &*value as *const u32;

    unsafe {
        require_allocated_u32(ptr);
    }
}

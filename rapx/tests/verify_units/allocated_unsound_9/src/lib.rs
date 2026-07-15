#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]
#![allow(dangling_pointers_from_locals)]

#[rapx::requires(Allocated(_ptr, u32, 1), kind = "precond")]
unsafe fn require_allocated_u32(_ptr: *const u32) {}

fn dangling_ptr() -> *const u32 {
    let value = 1_u32;
    &value as *const u32
}

// UNSOUND: the intra-call returns a pointer to a dead stack slot.
#[rapx::verify]
pub fn unsound_intra_returns_dangling_pointer() {
    let ptr = dangling_ptr();

    unsafe {
        require_allocated_u32(ptr);
    }
}

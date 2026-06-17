#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(Allocated(_ptr, u32, 1), kind = "precond")]
unsafe fn require_allocated_u32(_ptr: *const u32) {}

// SOUND: both branch targets are live stack allocations.
#[rapx::verify]
pub fn sound_branch_selects_live_local(choose_left: bool) {
    let left = 1_u32;
    let right = 2_u32;
    let ptr = if choose_left {
        &left as *const u32
    } else {
        &right as *const u32
    };

    unsafe {
        require_allocated_u32(ptr);
    }
}

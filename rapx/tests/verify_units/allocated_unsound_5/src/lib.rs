#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(Allocated(_ptr, u32, 1), kind = "precond")]
unsafe fn require_allocated_u32(_ptr: *const u32) {}

// UNSOUND: one branch passes a null pointer to the allocated requirement.
#[rapx::verify]
pub fn unsound_branch_may_select_null(choose_live: bool) {
    let value = 9_u32;
    let live = &value as *const u32;
    let null = std::ptr::null::<u32>();
    let ptr = if choose_live { live } else { null };

    unsafe {
        require_allocated_u32(ptr);
    }
}

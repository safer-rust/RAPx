#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(Allocated(_ptr, u32, 1), kind = "precond")]
unsafe fn require_allocated_u32(_ptr: *const u32) {}

// UNSOUND: the raw pointer escapes after its stack allocation is dead.
#[rapx::verify]
pub fn unsound_stack_scope_ended() {
    let ptr: *const u32;
    {
        let value = 5_u32;
        ptr = &value as *const u32;
    }

    unsafe {
        require_allocated_u32(ptr);
    }
}

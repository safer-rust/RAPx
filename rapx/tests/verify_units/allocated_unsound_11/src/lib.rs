#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(Allocated(_ptr, u32, 1), kind = "precond")]
unsafe fn require_allocated_u32(_ptr: *const u32) {}

// UNSOUND: adjacent stack locals are still distinct objects; pointer arithmetic cannot cross them.
#[rapx::verify]
pub fn unsound_adjacent_stack_objects_do_not_merge() {
    let second = 2_u32;
    let ptr = {
        let first = 1_u32;
        (&first as *const u32).wrapping_add(1)
    };

    unsafe {
        require_allocated_u32(ptr);
    }

    let _keep_second_live = second;
}

#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(Allocated(_ptr, u32, 1), kind = "precond")]
unsafe fn require_allocated_u32(_ptr: *const u32) {}

// UNSOUND: the loop stores a pointer to a temporary whose scope ends before the call.
#[rapx::verify]
pub fn unsound_scc_selects_dead_temporary(stop: bool) {
    let ptr = loop {
        let temporary = 2_u32;
        let selected = &temporary as *const u32;

        if stop {
            break selected;
        }

        break selected;
    };

    unsafe {
        require_allocated_u32(ptr);
    }
}

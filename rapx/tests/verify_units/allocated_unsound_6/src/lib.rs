#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(Allocated(_ptr, u32, 1), kind = "precond")]
unsafe fn require_allocated_u32(_ptr: *const u32) {}

// UNSOUND: the SCC may overwrite a live pointer with null before the callsite.
#[rapx::verify]
pub fn unsound_scc_overwrites_with_null(overwrite: bool) {
    let value = 1_u32;
    let mut ptr = &value as *const u32;

    loop {
        if overwrite {
            ptr = std::ptr::null::<u32>();
        }
        break;
    }

    unsafe {
        require_allocated_u32(ptr);
    }
}

#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(ValidPtr(_ptr, u32, 1), kind = "precond")]
unsafe fn require_valid_ptr_one(_ptr: *const u32) {}

// UNSOUND: one SCC path directly validates a one-past pointer as dereferenceable.
#[rapx::verify]
pub fn unsound_scc_branch_uses_one_past(data: &[u32], choose_bad: bool) {
    let mut seen = false;

    while !seen {
        if choose_bad {
            let ptr = unsafe { data.as_ptr().add(data.len()) };
            unsafe {
                require_valid_ptr_one(ptr);
            }
        } else {
            unsafe {
                require_valid_ptr_one(data.as_ptr());
            }
        }
        seen = true;
    }
}

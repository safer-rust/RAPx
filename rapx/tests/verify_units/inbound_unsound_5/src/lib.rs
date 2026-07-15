#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(InBound(_ptr, u32, 1), kind = "precond")]
unsafe fn require_branch_inbound(_ptr: *const u32) {}

// UNSOUND: only one branch uses the guarded index; the other uses an unguarded one.
#[rapx::verify]
pub fn unsound_branch_selects_unguarded_index(
    data: &[u32],
    guarded: usize,
    unguarded: usize,
    flag: bool,
) {
    if guarded < data.len() {
        let ptr = data.as_ptr();
        let current = if flag {
            unsafe { ptr.add(guarded) }
        } else {
            unsafe { ptr.add(unguarded) }
        };

        unsafe {
            require_branch_inbound(current);
        }
    }
}

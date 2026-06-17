#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(NonNull(_ptr), kind = "precond")]
unsafe fn require_nonnull(_ptr: *const u32) {}

// UNSOUND: one feasible branch selects null before the unsafe call.
#[rapx::verify]
pub fn unsound_branch_selects_null(choose_null: bool) {
    let value = 13_u32;
    let ptr = if choose_null {
        0usize as *const u32
    } else {
        &value as *const u32
    };

    unsafe {
        require_nonnull(ptr);
    }
}

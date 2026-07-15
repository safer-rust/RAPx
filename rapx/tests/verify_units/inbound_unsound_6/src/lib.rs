#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(InBound(_ptr, u32, 1), kind = "precond")]
unsafe fn require_scc_inbound(_ptr: *const u32) {}

// UNSOUND: loop guard `i < data.len()` does not imply `i + 1 < data.len()`.
// At the final iteration (i = data.len() - 1), `ptr.wrapping_add(i + 1)` points
// one element past the end of the allocation — an off-by-one bug.
//
// The SMT can symbolically reason about the arithmetic relationship between
// the guard variable `i` and the access index `i + 1`, so this violation is
// detectable regardless of loop-unrolling depth.
//
// Category 1 (static): single-round expansion already catches the off-by-one
// through the callee contract InBound check.
#[rapx::verify]
pub fn unsound_scc_off_by_one(data: &[u32]) {
    let ptr = data.as_ptr();
    let mut i = 0usize;
    while i < data.len() {
        let current = ptr.wrapping_add(i + 1);
        unsafe {
            require_scc_inbound(current);
        }
        i += 1;
    }
}

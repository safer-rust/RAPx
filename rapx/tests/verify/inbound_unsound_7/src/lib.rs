#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(InBound(_ptr, u32, 1), kind = "precond")]
unsafe fn require_scc_inbound(_ptr: *const u32) {}

// UNSOUND: off-by-one caught at deeper unrolling when `len >= 10` is
// anchored by the early-return guard.
//
// With postfix-repeat=0 (max 1 body exec): the 1-iteration path constrains
// len == 1 via the loop exit, contradicting `len >= 10` from the if-check →
// vacuous Proved → the auto-detector triggers.
//
// With postfix-repeat=1 (max 2 body execs): vacuous Proved for paths with
// len < 10.  With postfix-repeat=9 (max 10 body execs): the 10-iteration
// path has len == 10 and the last InBound at `ptr.wrapping_add(i + 1)` with
// `i = 9` needs len >= 11 → Unknown → UNSOUND.
//
// Category 2 (diverging): round 0 all Proved → auto-detector probes deeper
// → finds Unknown at repeat=9.
#[rapx::verify]
pub fn unsound_len_guard_off_by_one(data: &[u32]) {
    let len = data.len();
    if len < 10 {
        return;
    }
    let ptr = data.as_ptr();
    let mut i = 0usize;
    while i < len {
        let current = ptr.wrapping_add(i + 1);
        unsafe {
            require_scc_inbound(current);
        }
        i += 1;
    }
}

#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code, unused_assignments)]

#[rapx::requires(Align(_ptr, u32), kind = "precond")]
unsafe fn require_align_u32(_ptr: *const u32) {}

// THRESHOLD: repeat=1 only sees aligned states; repeat=2 reaches the delayed unaligned overwrite.
#[rapx::verify]
pub fn repeat2_reveals_delayed_unaligned(data: &[u32], limit: usize) {
    let base = data.as_ptr() as *const u8;
    let bad = base.wrapping_add(1);
    let mut selected = base;
    let mut current = base;
    let mut next = base;
    let mut after_next = base;
    let mut i = 0usize;

    while i < limit {
        selected = current;
        current = next;
        next = after_next;
        after_next = bad;
        i += 1;
    }

    unsafe {
        require_align_u32(selected as *const u32);
    }
}

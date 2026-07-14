#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code, unused_assignments)]

#[derive(Clone, Copy)]
pub enum Selector {
    First,
    Second,
}

#[rapx::requires(Align(_ptr, u32), kind = "precond")]
unsafe fn require_align_arg0(_ptr: *const u32) {}

// UNSOUND: the SCC may compute a final byte offset not divisible by four.
#[rapx::verify]
pub fn unsound_scc_computes_misaligned_offset(data: &[u32], limit: usize, choice: Selector) {
    let base = data.as_ptr() as *const u8;
    let mut byte_offset = 0usize;
    let mut i = 0;

    while i < limit {
        byte_offset = match choice {
            Selector::First => i * 4,
            Selector::Second => i * 4 + 1,
        };

        i += 1;
    }

    let selected = base.wrapping_add(byte_offset);

    unsafe {
        require_align_arg0(selected as *const u32);
    }
}

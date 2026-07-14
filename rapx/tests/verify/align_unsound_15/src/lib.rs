#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code, unused_assignments)]

#[rapx::requires(Align(_ptr, u32), kind = "precond")]
unsafe fn require_align_u32(_ptr: *const u32) {}

// UNSOUND: repeated SCC iterations can overwrite selected as A/U/A/U.
#[rapx::verify]
pub fn unsound_four_phase_scc_alignment(data: &[u32], limit: usize) {
    let base = data.as_ptr() as *const u8;
    let mut selected = base;
    let mut phase = 0usize;
    let mut i = 0usize;

    while i < limit {
        selected = match phase {
            0 => base,                   // aligned
            1 => base.wrapping_add(1), // unaligned
            2 => base.wrapping_add(4), // aligned
            _ => base.wrapping_add(5), // unaligned
        };
        phase = (phase + 1) % 4;
        i += 1;
    }

    unsafe {
        require_align_u32(selected as *const u32);
    }
}

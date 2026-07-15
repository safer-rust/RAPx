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

// SOUND: final value alternates by iteration count, but both offsets align.
#[rapx::verify]
pub fn sound_iteration_count_switches_aligned_offsets(data: &[u32], limit: usize) {
    let base = data.as_ptr() as *const u8;
    let mut selected = base;
    let mut i = 0;

    while i < limit {
        selected = if i % 2 == 0 {
            base
        } else {
            base.wrapping_add(4)
        };

        i += 1;
    }

    unsafe {
        require_align_arg0(selected as *const u32);
    }
}

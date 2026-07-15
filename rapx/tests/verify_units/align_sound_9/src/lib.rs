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

// SOUND: pre-SCC guards and SCC-selected offsets jointly align the final pointer.
// The unsafe API is outside the SCC, after several related path choices.
#[rapx::verify]
pub fn sound_pre_scc_guard_with_scc_offsets(data: &[u8], limit: usize, choice: Selector) {
    let base = data.as_ptr();
    let mut selected = base;
    let mut i = 0;

    if (base as usize) % 4 == 0 {
        while i < limit {
            selected = match choice {
                Selector::First => base,
                Selector::Second => base.wrapping_add(i * 4),
            };

            i += 1;
        }

        unsafe {
            require_align_arg0(selected as *const u32);
        }
    }
}

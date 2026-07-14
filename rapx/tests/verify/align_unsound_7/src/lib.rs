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

// UNSOUND: an SCC-internal guard only protects one branch of the selected value.
// Another enum path still assigns an unaligned byte-shifted pointer.
#[rapx::verify]
pub fn unsound_scc_guard_only_on_one_branch(data: &[u8], limit: usize, choice: Selector) {
    let base = data.as_ptr();
    let mut selected = base;
    let mut i = 0;

    while i < limit {
        selected = match choice {
            Selector::First => {
                if (base as usize) % 4 == 0 {
                    base
                } else {
                    base.wrapping_add(4)
                }
            }
            Selector::Second => base.wrapping_add(1),
        };

        i += 1;
    }

    unsafe {
        require_align_arg0(selected as *const u32);
    }
}

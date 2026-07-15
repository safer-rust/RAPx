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

// UNSOUND: a related SCC path can overwrite the guarded pointer with `base + 1`.
// The pre-SCC base guard must not prove the post-SCC selected pointer.
#[rapx::verify]
pub fn unsound_pre_scc_guard_overwritten_by_scc(data: &[u8], limit: usize, choice: Selector) {
    let base = data.as_ptr();
    let mut selected = base;
    let mut i = 0;

    if (base as usize) % 4 == 0 {
        while i < limit {
            selected = match choice {
                Selector::First => base,
                Selector::Second => base.wrapping_add(1),
            };

            i += 1;
        }

        unsafe {
            require_align_arg0(selected as *const u32);
        }
    }
}

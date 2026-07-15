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

// SOUND: SCC-local branch noise is unrelated to the pointer used after the SCC.
// The final unsafe argument is rebuilt from the aligned slice base.
#[rapx::verify]
pub fn sound_scc_internal_noise_ignored(data: &[u32], limit: usize, choice: Selector) {
    let base = data.as_ptr();
    let mut scratch = base as *const u8;
    let mut i = 0;

    while i < limit {
        if i % 2 == 0 {
            scratch = match choice {
                Selector::First => base as *const u8,
                Selector::Second => (base as *const u8).wrapping_add(1),
            };
        }

        i += 1;
    }

    let _ignore = scratch;
    let selected = data.as_ptr();

    unsafe {
        require_align_arg0(selected);
    }
}

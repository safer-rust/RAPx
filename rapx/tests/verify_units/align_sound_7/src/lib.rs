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

// SOUND: the SCC mutates only scratch state unrelated to the unsafe argument.
#[rapx::verify]
pub fn sound_unrelated_scc_does_not_pollute_align(data: &[u32], limit: usize, choice: Selector) {
    let base = data.as_ptr() as *const u8;
    let mut scratch = base;
    let mut i = 0;

    while i < limit {
        scratch = match choice {
            Selector::First => base.wrapping_add(i * 4),
            Selector::Second => base.wrapping_add(i * 4 + 1),
        };

        i += 1;
    }

    let _ignore = scratch;
    let selected = data.as_ptr();

    unsafe {
        require_align_arg0(selected);
    }
}

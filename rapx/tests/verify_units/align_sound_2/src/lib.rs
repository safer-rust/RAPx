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

// SOUND: both SCC paths produce a u32-aligned pointer before the unsafe API.
#[rapx::verify]
pub fn sound_enum_paths_inside_scc(data: &[u32], limit: usize, choice: Selector) {
    let base = data.as_ptr();
    let mut selected = base;
    let mut i = 0;

    while i < limit {
        selected = match choice {
            Selector::First => base,
            Selector::Second => base.wrapping_add(i),
        };

        i += 1;
    }

    unsafe {
        require_align_arg0(selected);
    }
}

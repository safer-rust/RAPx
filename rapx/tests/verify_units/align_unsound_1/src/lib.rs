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

// UNSOUND: one SCC path leaves `selected` at `base + 1` byte.
#[rapx::verify]
pub fn unsound_enum_paths_inside_scc(data: &[u32], limit: usize, choice: Selector) {
    let base = data.as_ptr() as *const u8;
    let mut selected = base;
    let mut i = 0;

    while i < limit {
        selected = match choice {
            Selector::First => base.wrapping_add(i * 4),
            Selector::Second => base.wrapping_add(i * 4 + 1),
        };

        i += 1;
    }

    unsafe {
        require_align_arg0(selected as *const u32);
    }
}

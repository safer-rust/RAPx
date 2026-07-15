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

// SOUND: SCC source selection changes provenance, but both alternatives align.
#[rapx::verify]
pub fn sound_scc_selects_aligned_source(data: &[u32], limit: usize, choice: Selector) {
    let local = 7_u32;
    let slice_base = data.as_ptr();
    let stack_ptr = &local as *const u32;
    let mut selected = slice_base;
    let mut i = 0;

    while i < limit {
        selected = match choice {
            Selector::First => slice_base.wrapping_add(i),
            Selector::Second => stack_ptr,
        };

        i += 1;
    }

    unsafe {
        require_align_arg0(selected);
    }
}

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

// UNSOUND: one source category is a byte-shifted slice pointer.
#[rapx::verify]
pub fn unsound_scc_selects_mixed_source(data: &[u32], limit: usize, choice: Selector) {
    let local = 11_u32;
    let stack_ptr = &local as *const u32 as *const u8;
    let slice_base = data.as_ptr() as *const u8;
    let mut selected = slice_base;
    let mut i = 0;

    while i < limit {
        selected = match choice {
            Selector::First => {
                if i % 2 == 0 {
                    slice_base
                } else {
                    stack_ptr
                }
            }
            Selector::Second => slice_base.wrapping_add(1),
        };

        i += 1;
    }

    unsafe {
        require_align_arg0(selected as *const u32);
    }
}

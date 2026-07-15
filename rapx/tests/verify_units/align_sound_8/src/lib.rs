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

// SOUND: nested SCC scratch state is unrelated to the stack pointer argument.
#[rapx::verify]
pub fn sound_unrelated_nested_scc_with_bad_scratch(
    outer_limit: usize,
    inner_limit: usize,
    choice: Selector,
) {
    let value = 19_u32;
    let base = &value as *const u32 as *const u8;
    let mut scratch = base;
    let mut outer = 0;

    while outer < outer_limit {
        let mut inner = 0;

        while inner < inner_limit {
            scratch = match choice {
                Selector::First => base,
                Selector::Second => base.wrapping_add(1),
            };

            inner += 1;
        }

        outer += 1;
    }

    let _ignore = scratch;
    let selected = &value as *const u32;

    unsafe {
        require_align_arg0(selected);
    }
}

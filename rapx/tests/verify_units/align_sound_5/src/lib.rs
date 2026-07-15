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

// SOUND: nested SCCs update the selected pointer only through u32 element moves.
#[rapx::verify]
pub fn sound_nested_scc_controller(
    data: &[u32],
    outer_limit: usize,
    inner_limit: usize,
    choice: Selector,
) {
    let base = data.as_ptr();
    let mut selected = base;
    let mut outer = 0;

    while outer < outer_limit {
        let mut p = match choice {
            Selector::First => base,
            Selector::Second => base.wrapping_add(outer),
        };

        let q = base.wrapping_add(outer + 1);
        let mut inner = 0;

        while inner < inner_limit {
            selected = match choice {
                Selector::First => base,
                Selector::Second => p,
            };

            p = q;
            inner += 1;
        }

        outer += 1;
    }

    unsafe {
        require_align_arg0(selected);
    }
}

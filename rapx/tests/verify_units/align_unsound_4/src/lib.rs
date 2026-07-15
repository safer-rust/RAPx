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

// UNSOUND: after two inner iterations, `p = q` can move `selected` to `base + 1`.
#[rapx::verify]
pub fn unsound_nested_scc_controller(
    data: &[u32],
    outer_limit: usize,
    inner_limit: usize,
    choice: Selector,
) {
    let base = data.as_ptr() as *const u8;
    let mut selected = base;
    let mut outer = 0;

    while outer < outer_limit {
        let mut p = base;
        let q = base.wrapping_add(1);
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
        require_align_arg0(selected as *const u32);
    }
}

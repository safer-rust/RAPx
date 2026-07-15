#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[derive(Clone, Copy)]
pub enum Selector {
    First,
    Second,
}

#[rapx::requires(Align(_ptr, u32), kind = "precond")]
unsafe fn require_align_arg0(_ptr: *const u32) {}

fn maybe_unaligned(base: *const u8, choice: Selector) -> *const u32 {
    match choice {
        Selector::First => base as *const u32,
        Selector::Second => base.wrapping_add(1) as *const u32,
    }
}

#[rapx::verify]
pub fn unsound_helper_return_path_selects_bad_ptr(data: &[u8], choice: Selector) {
    let base = data.as_ptr();

    if (base as usize) % 4 == 0 {
        let ptr = maybe_unaligned(base, choice);
        unsafe {
            require_align_arg0(ptr);
        }
    }
}

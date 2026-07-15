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

fn choose_byte_ptr(base: *const u8, offset: usize, choice: Selector) -> *const u32 {
    match choice {
        Selector::First => unsafe { base.add(offset) as *const u32 },
        Selector::Second => base as *const u32,
    }
}

#[rapx::verify]
pub fn sound_helper_return_paths_all_aligned(data: &[u8], offset: usize, choice: Selector) {
    let base = data.as_ptr();

    if (base as usize) % 4 == 0 && offset % 4 == 0 {
        let ptr = choose_byte_ptr(base, offset, choice);
        unsafe {
            require_align_arg0(ptr);
        }
    }
}

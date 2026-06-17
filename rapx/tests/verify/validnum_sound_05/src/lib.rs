#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(ValidNum(_idx < _len), kind = "precond")]
unsafe fn require_index_inside(_idx: usize, _len: usize) {}

// SOUND: the loop-internal call is protected by the loop body's index guard.
#[rapx::verify]
pub fn sound_scc_validnum_index_guard(mut idx: usize, len: usize) {
    loop {
        if idx >= len {
            break;
        }
        unsafe {
            require_index_inside(idx, len);
        }
        idx += 1;
        break;
    }
}

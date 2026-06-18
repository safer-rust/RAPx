#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::ffi::{CStr, c_char};

#[derive(Clone, Copy)]
pub enum Selector {
    Good,
    Bad,
}

static GOOD: &[u8] = b"nested\0";
static BAD: &[u8] = b"nested";

// UNSOUND: nested SCCs can switch the selected pointer from a valid source to an invalid one.
#[rapx::verify]
pub fn unsound_nested_scc_switches_to_invalid(choice: Selector, stop_outer: bool, stop_inner: bool) -> usize {
    let mut selected = GOOD.as_ptr();
    let mut outer = 0;

    while outer < 2 {
        let mut inner = 0;
        while inner < 2 {
            selected = match choice {
                Selector::Good => GOOD.as_ptr(),
                Selector::Bad => BAD.as_ptr(),
            };
            if stop_inner {
                break;
            }
            inner += 1;
        }
        if stop_outer {
            break;
        }
        outer += 1;
    }

    let cstr = unsafe { CStr::from_ptr(selected as *const c_char) };
    cstr.to_bytes().len()
}

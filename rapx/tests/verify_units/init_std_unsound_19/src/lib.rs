#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use core::mem::MaybeUninit;

// UNSOUND when `flag` is false. The initialized and uninitialized prefixes
// have the same numeric summary when they enter the inner SCC.
#[rapx::verify]
pub fn unsound_initialized_true_prefix(flag: bool) -> u8 {
    let mut slot = MaybeUninit::<u8>::uninit();
    let mut result = 0;
    let mut outer = 0;
    while outer < 1 {
        if flag {
            slot.write(7);
        }

        let mut inner = 0;
        while inner < 1 {
            inner += 1;
        }

        result = unsafe { slot.assume_init_read() };
        outer += 1;
    }
    result
}

// UNSOUND when `flag` is true. This reversed branch guards against making the
// result depend on which SwitchInt successor the path enumerator visits first.
#[rapx::verify]
pub fn unsound_initialized_false_prefix(flag: bool) -> u8 {
    let mut slot = MaybeUninit::<u8>::uninit();
    let mut result = 0;
    let mut outer = 0;
    while outer < 1 {
        if !flag {
            slot.write(7);
        }

        let mut inner = 0;
        while inner < 1 {
            inner += 1;
        }

        result = unsafe { slot.assume_init_read() };
        outer += 1;
    }
    result
}

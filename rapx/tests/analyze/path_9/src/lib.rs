#![allow(dead_code)]

use core::mem::MaybeUninit;

// Two prefixes carry different initialization states into the same inner SCC.
// Path enumeration must replay the inner SCC for both prefixes rather than
// treating their equal numeric summaries as an interchangeable VM state.
fn different_memory_prefixes(flag: bool) -> u8 {
    let mut slot = MaybeUninit::<u8>::uninit();
    let ptr = slot.as_mut_ptr();
    let mut result = 0;
    let mut outer = 0;
    while outer < 1 {
        if flag {
            unsafe { ptr.write(7) };
        }

        let mut inner = 0;
        while inner < 1 {
            inner += 1;
        }

        result = inner;
        outer += 1;
    }
    result
}

#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(Allocated(_ptr, u32, 2), kind = "precond")]
unsafe fn require_two_allocated_u32(_ptr: *const u32) {}

// SOUND: SCC branch choices only select between live two-element arrays.
#[rapx::verify]
pub fn sound_scc_selects_live_array(choose_left: bool, stop: bool) {
    let left = [1_u32, 2];
    let right = [3_u32, 4];

    let ptr = loop {
        let selected = if choose_left {
            left.as_ptr()
        } else {
            right.as_ptr()
        };

        if stop {
            break selected;
        }

        break selected;
    };

    unsafe {
        require_two_allocated_u32(ptr);
    }
}

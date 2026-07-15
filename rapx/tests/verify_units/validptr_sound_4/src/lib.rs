#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(ValidPtr(_ptr, u32, 1), kind = "precond")]
unsafe fn require_valid_ptr_one(_ptr: *const u32) {}

// SOUND: each SCC iteration proves one in-bounds element pointer.
#[rapx::verify]
pub fn sound_scc_each_slice_element(data: &[u32]) {
    let mut i = 0;

    while i < data.len() {
        let ptr = unsafe { data.as_ptr().add(i) };

        unsafe {
            require_valid_ptr_one(ptr);
        }

        i += 1;
    }
}

#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::verify]
pub fn unsound_signed_suffix_missing_lower_bound() {
    let arr = [10, 20, 30, 40];

    let ptr = arr.as_ptr();

    unsafe {
        for i in 0..=arr.len() {
            let _value = *ptr.offset(i as isize);
        }
    }
}
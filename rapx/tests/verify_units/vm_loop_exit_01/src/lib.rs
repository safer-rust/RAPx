#![feature(register_tool)]
#![register_tool(rapx)]

#[rapx::verify]
pub fn sound_after_two_iterations() -> u8 {
    let mut i = 0usize;
    while i < 2 {
        i += 1;
    }
    let data = [7_u8];
    unsafe { data.as_ptr().read() }
}

#[rapx::verify]
pub fn unsound_after_two_iterations() -> u8 {
    let mut i = 0usize;
    while i < 2 {
        i += 1;
    }
    let data = [7_u8];
    unsafe { data.as_ptr().add(1).read() }
}

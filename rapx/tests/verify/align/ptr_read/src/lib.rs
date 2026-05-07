#![feature(register_tool)]
#![register_tool(rapx)]

#[rapx::verify]
fn safe_read<T>(ptr: *const T) -> Option<u32> {
    if (ptr as usize) % std::mem::align_of::<u32>() == 0 {
        unsafe {
            let p = ptr as *const u32;
            Some(p.read())
        }
    } else {
        None
    }
}

#[rapx::verify]
fn unsafe_read<T>(ptr: *const T) -> u32 {
    unsafe {
        let p = ptr as *const u32;
        p.read()
    }
}

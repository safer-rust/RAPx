#![feature(register_tool)]
#![register_tool(rapx)]

#[rapx::verify]

fn safe_read<T>(data: &[T], offset: usize) -> Option<u32> {
    let ptr = data.as_ptr() as *const u8;

    if (ptr as usize) % 4 == 0 && offset % 4 == 0 {
        let sound_ptr = unsafe { ptr.add(offset) as *const u32 };
        let value = unsafe { sound_ptr.read() };
        Some(value)
    } else {
        None
    }
}

#[rapx::verify]
fn unsafe_read<T>(data: &[T], offset: usize) -> u32 {
    let ptr = data.as_ptr() as *const u8;

    if (ptr as usize) % 4 == 0 {
        let unsound_ptr = unsafe { ptr.add(offset) as *const u32 };
        unsafe { unsound_ptr.read() }
    } else {
        0
    }
}

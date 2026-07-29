#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(unused)]

struct Wrapper<T> {
    ptr: *const T,
    len: usize,
}

impl<T> Wrapper<T> {
    fn new(ptr: *const T, len: usize) -> Self {
        Self { ptr, len }
    }

    fn set_len(&mut self, len: usize) {
        self.len = len;
    }

    fn read(&self) -> Option<u32> {
        let ptr = self.ptr;

        if self.len == 0 {
            return None;
        }

        if (ptr as usize) % std::mem::align_of::<u32>() == 0 {
            unsafe {
                let p = ptr as *const u32;
                Some(p.read())
            }
        } else {
            None
        }
    }

    fn read_unchecked(&self) -> u32 {
        let ptr = self.ptr;

        unsafe {
            let p = ptr as *const u32;
            p.read()
        }
    }
}

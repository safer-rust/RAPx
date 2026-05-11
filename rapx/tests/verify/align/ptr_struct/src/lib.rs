#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(unused)]

#[rapx::invariant(Align(ptr, T), kind = "precond")]
#[rapx::invariant(InBound(ptr, T, len), kind = "precond")]
#[rapx::invariant(Init(ptr, T, len), kind = "precond")]
struct Wrapper<T> {
    ptr: *const T,
    len: usize,
}

impl<T> Wrapper<T> {
    #[rapx::verify]
    fn new(ptr: *const T, len: usize) -> Self {
        Self { ptr, len }
    }

    #[rapx::verify]
    fn set_len(&mut self, len: usize) {
        self.len = len;
    }

    #[rapx::verify]
    fn safe_read(&self) -> Option<u32> {
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

    #[rapx::verify]
    fn unsafe_read(&self) -> u32 {
        let ptr = self.ptr;

        unsafe {
            let p = ptr as *const u32;
            p.read()
        }
    }
}

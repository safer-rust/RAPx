#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(unused)]

struct Wrapper<T> {
    ptr: *const T,
    len: usize,
}

impl<T> Wrapper<T> {
    #[rapx::requires(Align(ptr, T), kind = "precond")]
    #[rapx::requires(InBound(ptr, T, len), kind = "precond")]
    #[rapx::requires(Init(ptr, T, len), kind = "precond")]
    unsafe fn unsound_new(ptr: *const T, len: usize) -> Self {
        Self { ptr, len }
    }

    #[rapx::requires(InBound(self.ptr, T, len), kind = "precond")]
    #[rapx::requires(Init(self.ptr, T, len), kind = "precond")]
    unsafe fn unsound_set_len(&mut self, len: usize) {
        self.len = len;
    }

    fn sound_read(&self) -> Option<u32> {
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

    #[rapx::requires(Align(self.ptr, u32), kind = "precond")]
    #[rapx::requires(InBound(self.ptr, u32, 1), kind = "precond")]
    #[rapx::requires(Init(self.ptr, u32, 1), kind = "precond")]
    unsafe fn unsound_read(&self) -> u32 {
        let ptr = self.ptr;

        unsafe {
            let p = ptr as *const u32;
            p.read()
        }
    }
}

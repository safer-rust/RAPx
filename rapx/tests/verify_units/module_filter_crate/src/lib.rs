#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code, unused_assignments)]

#[rapx::requires(Align(_ptr, u32), kind = "precond")]
unsafe fn require_align(_ptr: *const u32) {}

pub mod a {
    #[rapx::verify]
    pub fn f(data: &[u32]) {
        let ptr = data.as_ptr();
        unsafe {
            super::require_align(ptr);
        }
    }
}

pub mod b {
    #[rapx::verify]
    pub fn g(data: &[u32]) {
        let ptr = data.as_ptr();
        unsafe {
            super::require_align(ptr);
        }
    }
}

pub mod c {
    #[rapx::verify]
    pub fn h(data: &[u32]) {
        let ptr = data.as_ptr();
        unsafe {
            super::require_align(ptr);
        }
    }
}

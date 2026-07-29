#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(unused)]

use std::ptr::NonNull;

#[rapx::invariant(Allocated(ptr, u8, capacity))]
#[rapx::invariant(Align(ptr, u8))]
#[rapx::invariant(Owning(ptr))]
#[rapx::invariant(InBound(ptr, u8, capacity))]
pub struct BumpAllocator {
    ptr: NonNull<u8>,
    capacity: usize,
    offset: usize,
}

impl BumpAllocator {
    #[rapx::verify]
    pub fn new(capacity: usize) -> Self {
        assert!(capacity > 0);

        let mut buf = vec![0u8; capacity];
        let ptr = NonNull::new(buf.as_mut_ptr()).expect("non-null after vec alloc");

        std::mem::forget(buf);

        Self {
            ptr,
            capacity,
            offset: 0,
        }
    }

    #[rapx::verify]
    pub fn alloc<T>(&mut self, value: T) -> *mut T {
        let align = std::mem::align_of::<T>();
        let size = std::mem::size_of::<T>();

        let start = (self.offset + align - 1) & !(align - 1);

        assert!(start + size <= self.capacity);

        assert!(start % align == 0);

        let p = unsafe { self.ptr.as_ptr().add(start) as *mut T };

        unsafe {
            p.write(value);
        }

        self.offset = start + size;

        p
    }

    #[rapx::verify]
    pub fn reset(&mut self) {
        self.offset = 0;
    }
}

impl Drop for BumpAllocator {
    fn drop(&mut self) {
        unsafe {
            drop(Vec::from_raw_parts(
                self.ptr.as_ptr(),
                self.capacity,
                self.capacity,
            ));
        }
    }
}

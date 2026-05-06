#![feature(register_tool)]
#![register_tool(rapx)]
#![feature(slice_index_methods)]
#![allow(unsafe_op_in_unsafe_fn)]

use std::mem::{align_of, MaybeUninit};
use std::ptr;
use std::slice::{from_raw_parts, from_raw_parts_mut, SliceIndex};

pub trait SliceExt<T> {
    unsafe fn get_unchecked_ext<I>(&self, index: I) -> &I::Output
    where
        I: SliceIndex<[T]>;

    unsafe fn get_unchecked_mut_ext<I>(&mut self, index: I) -> &mut I::Output
    where
        I: SliceIndex<[T]>;

    unsafe fn split_at_unchecked_ext(&self, mid: usize) -> (&[T], &[T]);

    unsafe fn split_at_mut_unchecked_ext(&mut self, mid: usize) -> (&mut [T], &mut [T]);

    unsafe fn swap_unchecked_ext(&mut self, a: usize, b: usize);

    unsafe fn as_chunks_unchecked_ext<const N: usize>(&self) -> &[[T; N]];

    unsafe fn as_chunks_unchecked_mut_ext<const N: usize>(&mut self) -> &mut [[T; N]];

    unsafe fn align_to_ext<U>(&self) -> (&[T], &[U], &[T]);

    unsafe fn align_to_mut_ext<U>(&mut self) -> (&mut [T], &mut [U], &mut [T]);

    unsafe fn get_disjoint_unchecked_mut_ext<I, const N: usize>(
        &mut self,
        indices: [I; N],
    ) -> [&mut I::Output; N]
    where
        I: SliceIndex<[T]> + Clone;
}

impl<T> SliceExt<T> for [T] {
    #[rapx::verify]
    #[rapx::requires(InBound(self.ptr, index), kind = "precond")]
    unsafe fn get_unchecked_ext<I>(&self, index: I) -> &I::Output
    where
        I: SliceIndex<[T]>,
    {
        &*index.get_unchecked(self)
    }

    #[rapx::verify]
    #[rapx::requires(InBound(self.ptr, index), kind = "precond")]
    unsafe fn get_unchecked_mut_ext<I>(&mut self, index: I) -> &mut I::Output
    where
        I: SliceIndex<[T]>,
    {
        &mut *index.get_unchecked_mut(self)
    }

    #[rapx::verify]
    #[rapx::requires(ValidNum(mid, [0,self.len]), kind = "precond")]
    unsafe fn split_at_unchecked_ext(&self, mid: usize) -> (&[T], &[T]) {
        let len = self.len();
        let ptr = self.as_ptr();

        debug_assert!(mid <= len);

        (
            from_raw_parts(ptr, mid),
            from_raw_parts(ptr.add(mid), len - mid),
        )
    }

    #[rapx::verify]
    #[rapx::requires(ValidNum(mid, [0,self.len]), kind = "precond")]
    unsafe fn split_at_mut_unchecked_ext(&mut self, mid: usize) -> (&mut [T], &mut [T]) {
        let len = self.len();
        let ptr = self.as_mut_ptr();

        debug_assert!(mid <= len);

        (
            from_raw_parts_mut(ptr, mid),
            from_raw_parts_mut(ptr.add(mid), len - mid),
        )
    }

    unsafe fn swap_unchecked_ext(&mut self, a: usize, b: usize) {
        let len = self.len();
        debug_assert!(a < len && b < len);

        let ptr = self.as_mut_ptr();
        ptr::swap(ptr.add(a), ptr.add(b));
    }

    #[rapx::verify]
    #[rapx::requires(ValidNum(a, "[0,self.len)"), kind = "precond")]
    #[rapx::requires(ValidNum(b, "[0,self.len)"), kind = "precond")]
    unsafe fn as_chunks_unchecked_ext<const N: usize>(&self) -> &[[T; N]] {
        debug_assert!(N != 0);
        debug_assert!(self.len() % N == 0);

        let new_len = self.len() / N;
        from_raw_parts(self.as_ptr() as *const [T; N], new_len)
    }

    #[rapx::verify]
    #[rapx::requires(ValidNum(a, "[0,self.len)"), kind = "precond")]
    #[rapx::requires(ValidNum(b, "[0,self.len)"), kind = "precond")]
    unsafe fn as_chunks_unchecked_mut_ext<const N: usize>(&mut self) -> &mut [[T; N]] {
        debug_assert!(N != 0);
        debug_assert!(self.len() % N == 0);

        let new_len = self.len() / N;
        from_raw_parts_mut(self.as_mut_ptr() as *mut [T; N], new_len)
    }

    #[rapx::verify]
    unsafe fn align_to_ext<U>(&self) -> (&[T], &[U], &[T]) {
        if std::mem::size_of::<T>() == 0 || std::mem::size_of::<U>() == 0 {
            return (self, &[], &[]);
        }

        let ptr = self.as_ptr();
        let offset = ptr.align_offset(align_of::<U>());

        if offset > self.len() {
            return (self, &[], &[]);
        }

        let (left, rest) = self.split_at(offset);

        let byte_len = rest.len() * std::mem::size_of::<T>();
        let new_len = byte_len / std::mem::size_of::<U>();

        let mid = from_raw_parts(rest.as_ptr() as *const U, new_len);
        let tail_start = rest.len() - (byte_len % std::mem::size_of::<U>()) / std::mem::size_of::<T>();

        let tail = from_raw_parts(rest.as_ptr().add(tail_start), rest.len() - tail_start);

        (left, mid, tail)
    }

    #[rapx::verify]
    unsafe fn align_to_mut_ext<U>(&mut self) -> (&mut [T], &mut [U], &mut [T]) {
        if std::mem::size_of::<T>() == 0 || std::mem::size_of::<U>() == 0 {
            return (self, &mut [], &mut []);
        }

        let ptr = self.as_mut_ptr();
        let offset = ptr.align_offset(align_of::<U>());

        if offset > self.len() {
            return (self, &mut [], &mut []);
        }

        let (left, rest) = self.split_at_mut(offset);

        let byte_len = rest.len() * std::mem::size_of::<T>();
        let new_len = byte_len / std::mem::size_of::<U>();

        let mid = from_raw_parts_mut(rest.as_mut_ptr() as *mut U, new_len);

        let tail_start =
            rest.len() - (byte_len % std::mem::size_of::<U>()) / std::mem::size_of::<T>();

        let tail = from_raw_parts_mut(
            rest.as_mut_ptr().add(tail_start),
            rest.len() - tail_start,
        );

        (left, mid, tail)
    }

    #[rapx::verify]
    #[rapx::requires(InBound(self.ptr, T, indices), kind = "precond")]
    unsafe fn get_disjoint_unchecked_mut_ext<I, const N: usize>(
        &mut self,
        indices: [I; N],
    ) -> [&mut I::Output; N]
    where
        I: SliceIndex<[T]> + Clone,
    {
        let slice: *mut [T] = self;
        let mut arr: MaybeUninit<[&mut I::Output; N]> = MaybeUninit::uninit();
        let arr_ptr = arr.as_mut_ptr() as *mut &mut I::Output;

        for i in 0..N {
            let idx = indices[i].clone();
            let slice_ref: &mut [T] = unsafe { &mut *slice };
            let elem: &mut I::Output = unsafe { slice_ref.get_unchecked_mut(idx) };

            unsafe {
                arr_ptr.add(i).write(elem);
            }
        }

        arr.assume_init()
    }
}

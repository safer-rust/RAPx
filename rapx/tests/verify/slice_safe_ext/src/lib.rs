#![feature(register_tool)]
#![register_tool(rapx)]
#![feature(slice_index_methods)]
#![allow(unsafe_op_in_unsafe_fn)]

use slice_ext::SliceExt;
use std::cmp::Ordering;
use std::mem::swap;
use std::ops::Range;
use std::ptr;
use std::slice::from_raw_parts_mut;

pub trait SliceSafeExt<T> {
    fn first_chunk_ext<const N: usize>(&self) -> Option<&[T; N]>;
    fn first_chunk_mut_ext<const N: usize>(&mut self) -> Option<&mut [T; N]>;
    fn split_first_chunk_ext<const N: usize>(&self) -> Option<(&[T; N], &[T])>;
    fn split_first_chunk_mut_ext<const N: usize>(&mut self) -> Option<(&mut [T; N], &mut [T])>;
    fn split_last_chunk_ext<const N: usize>(&self) -> Option<(&[T], &[T; N])>;
    fn split_last_chunk_mut_ext<const N: usize>(&mut self) -> Option<(&mut [T], &mut [T; N])>;
    fn last_chunk_ext<const N: usize>(&self) -> Option<&[T; N]>;
    fn last_chunk_mut_ext<const N: usize>(&mut self) -> Option<&mut [T; N]>;
    fn as_chunks_ext<const N: usize>(&self) -> (&[[T; N]], &[T]);
    fn as_chunks_mut_ext<const N: usize>(&mut self) -> (&mut [[T; N]], &mut [T]);
    fn as_rchunks_ext<const N: usize>(&self) -> (&[T], &[[T; N]]);
    fn split_at_checked_ext(&self, mid: usize) -> Option<(&[T], &[T])>;
    fn split_at_mut_checked_ext(&mut self, mid: usize) -> Option<(&mut [T], &mut [T])>;
    fn reverse_ext(&mut self);
    fn rotate_left_ext(&mut self, mid: usize);
    fn rotate_right_ext(&mut self, k: usize);
    fn copy_from_slice_ext(&mut self, src: &[T])
    where
        T: Copy;
    fn copy_within_ext(&mut self, src: Range<usize>, dest: usize)
    where
        T: Copy;
    fn swap_with_slice_ext(&mut self, other: &mut [T]);
    fn binary_search_by_ext<F>(&self, f: F) -> Result<usize, usize>
    where
        F: FnMut(&T) -> Ordering;
    fn partition_dedup_by_ext<F>(&mut self, same_bucket: F) -> (&mut [T], &mut [T])
    where
        F: FnMut(&mut T, &mut T) -> bool;
    fn get_disjoint_mut_ext<const N: usize>(
        &mut self,
        indices: [usize; N],
    ) -> Result<[&mut T; N], ()>;
}

impl<T> SliceSafeExt<T> for [T] {
    #[rapx::verify]
    fn first_chunk_ext<const N: usize>(&self) -> Option<&[T; N]> {
        if self.len() < N {
            None
        } else {
            Some(unsafe { &*(self.as_ptr() as *const [T; N]) })
        }
    }

    #[rapx::verify]
    fn first_chunk_mut_ext<const N: usize>(&mut self) -> Option<&mut [T; N]> {
        if self.len() < N {
            None
        } else {
            Some(unsafe { &mut *(self.as_mut_ptr() as *mut [T; N]) })
        }
    }

    #[rapx::verify]
    fn split_first_chunk_ext<const N: usize>(&self) -> Option<(&[T; N], &[T])> {
        let Some((first, tail)) = self.split_at_checked_ext(N) else { return None };
        Some((unsafe { &*(first.as_ptr() as *const [T; N]) }, tail))
    }

    #[rapx::verify]
    fn split_first_chunk_mut_ext<const N: usize>(&mut self) -> Option<(&mut [T; N], &mut [T])> {
        let Some((first, tail)) = self.split_at_mut_checked_ext(N) else { return None };
        Some((unsafe { &mut *(first.as_mut_ptr() as *mut [T; N]) }, tail))
    }

    #[rapx::verify]
    fn split_last_chunk_ext<const N: usize>(&self) -> Option<(&[T], &[T; N])> {
        let Some(index) = self.len().checked_sub(N) else { return None };
        let (init, last) = self.split_at(index);
        Some((init, unsafe { &*(last.as_ptr() as *const [T; N]) }))
    }

    #[rapx::verify]
    fn split_last_chunk_mut_ext<const N: usize>(&mut self) -> Option<(&mut [T], &mut [T; N])> {
        let Some(index) = self.len().checked_sub(N) else { return None };
        let (init, last) = self.split_at_mut(index);
        Some((init, unsafe { &mut *(last.as_mut_ptr() as *mut [T; N]) }))
    }

    #[rapx::verify]
    fn last_chunk_ext<const N: usize>(&self) -> Option<&[T; N]> {
        let Some(index) = self.len().checked_sub(N) else { return None };
        let (_, last) = self.split_at(index);
        Some(unsafe { &*(last.as_ptr() as *const [T; N]) })
    }

    #[rapx::verify]
    fn last_chunk_mut_ext<const N: usize>(&mut self) -> Option<&mut [T; N]> {
        let Some(index) = self.len().checked_sub(N) else { return None };
        let (_, last) = self.split_at_mut(index);
        Some(unsafe { &mut *(last.as_mut_ptr() as *mut [T; N]) })
    }

    #[rapx::verify]
    fn as_chunks_ext<const N: usize>(&self) -> (&[[T; N]], &[T]) {
        assert!(N != 0, "chunk size must be non-zero");
        let len_rounded_down = self.len() / N * N;
        let (multiple_of_n, remainder) = unsafe { self.split_at_unchecked_ext(len_rounded_down) };
        let array_slice = unsafe { multiple_of_n.as_chunks_unchecked_ext() };
        (array_slice, remainder)
    }

    #[rapx::verify]
    fn as_chunks_mut_ext<const N: usize>(&mut self) -> (&mut [[T; N]], &mut [T]) {
        assert!(N != 0, "chunk size must be non-zero");
        let len_rounded_down = self.len() / N * N;
        let (multiple_of_n, remainder) =
            unsafe { self.split_at_mut_unchecked_ext(len_rounded_down) };
        let array_slice = unsafe { multiple_of_n.as_chunks_unchecked_mut_ext() };
        (array_slice, remainder)
    }

    #[rapx::verify]
    fn as_rchunks_ext<const N: usize>(&self) -> (&[T], &[[T; N]]) {
        assert!(N != 0, "chunk size must be non-zero");
        let len = self.len() / N;
        let (remainder, multiple_of_n) = self.split_at(self.len() - len * N);
        let array_slice = unsafe { multiple_of_n.as_chunks_unchecked_ext() };
        (remainder, array_slice)
    }

    #[rapx::verify]
    fn split_at_checked_ext(&self, mid: usize) -> Option<(&[T], &[T])> {
        if mid <= self.len() {
            Some(unsafe { self.split_at_unchecked_ext(mid) })
        } else {
            None
        }
    }

    #[rapx::verify]
    fn split_at_mut_checked_ext(&mut self, mid: usize) -> Option<(&mut [T], &mut [T])> {
        if mid <= self.len() {
            Some(unsafe { self.split_at_mut_unchecked_ext(mid) })
        } else {
            None
        }
    }

    #[rapx::verify]
    fn reverse_ext(&mut self) {
        let half_len = self.len() / 2;
        let len = self.len();
        let ptr = self.as_mut_ptr();

        let (front_half, back_half) = unsafe {
            (
                from_raw_parts_mut(ptr, half_len),
                from_raw_parts_mut(ptr.add(len - half_len), half_len),
            )
        };

        let mut i = 0;
        while i < half_len {
            swap(&mut front_half[i], &mut back_half[half_len - 1 - i]);
            i += 1;
        }
    }

    #[rapx::verify]
    fn rotate_left_ext(&mut self, mid: usize) {
        assert!(mid <= self.len());
        let k = self.len() - mid;
        let p = self.as_mut_ptr();

        unsafe {
            let _mid_ptr = p.add(mid);
            let _all = from_raw_parts_mut(p, mid + k);
        }
    }

    #[rapx::verify]
    fn rotate_right_ext(&mut self, k: usize) {
        assert!(k <= self.len());
        let mid = self.len() - k;
        let p = self.as_mut_ptr();

        unsafe {
            let _mid_ptr = p.add(mid);
            let _all = from_raw_parts_mut(p, mid + k);
        }
    }

    #[rapx::verify]
    fn copy_from_slice_ext(&mut self, src: &[T])
    where
        T: Copy,
    {
        assert!(
            self.len() == src.len(),
            "source slice length does not match destination slice length"
        );
        unsafe {
            ptr::copy_nonoverlapping(src.as_ptr(), self.as_mut_ptr(), self.len());
        }
    }

    #[rapx::verify]
    fn copy_within_ext(&mut self, src: Range<usize>, dest: usize)
    where
        T: Copy,
    {
        let Range { start: src_start, end: src_end } = src;
        assert!(src_start <= src_end, "slice index starts at a larger index than it ends at");
        assert!(src_end <= self.len(), "range end out of bounds");
        let count = src_end - src_start;
        assert!(dest <= self.len() - count, "dest is out of bounds");
        unsafe {
            let ptr = self.as_mut_ptr();
            let src_ptr = ptr.add(src_start);
            let dest_ptr = ptr.add(dest);
            ptr::copy(src_ptr, dest_ptr, count);
        }
    }

    #[rapx::verify]
    fn swap_with_slice_ext(&mut self, other: &mut [T]) {
        assert!(
            self.len() == other.len(),
            "destination and source slices have different lengths"
        );
        unsafe {
            ptr::swap_nonoverlapping(self.as_mut_ptr(), other.as_mut_ptr(), self.len());
        }
    }

    #[rapx::verify]
    fn binary_search_by_ext<F>(&self, mut f: F) -> Result<usize, usize>
    where
        F: FnMut(&T) -> Ordering,
    {
        let mut size = self.len();
        if size == 0 {
            return Err(0);
        }
        let mut base = 0usize;

        while size > 1 {
            let half = size / 2;
            let mid = base + half;

            let cmp = f(unsafe { self.get_unchecked_ext(mid) });

            if cmp != Ordering::Greater {
                base = mid;
            }

            size -= half;
        }

        let cmp = f(unsafe { self.get_unchecked_ext(base) });
        if cmp == Ordering::Equal {
            Ok(base)
        } else {
            Err(base + (cmp == Ordering::Less) as usize)
        }
    }

    #[rapx::verify]
    fn partition_dedup_by_ext<F>(&mut self, mut same_bucket: F) -> (&mut [T], &mut [T])
    where
        F: FnMut(&mut T, &mut T) -> bool,
    {
        let len = self.len();
        if len <= 1 {
            return (self, &mut []);
        }

        let ptr = self.as_mut_ptr();
        let mut next_read: usize = 1;
        let mut next_write: usize = 1;

        unsafe {
            while next_read < len {
                let ptr_read = ptr.add(next_read);
                let prev_ptr_write = ptr.add(next_write - 1);
                if !same_bucket(&mut *ptr_read, &mut *prev_ptr_write) {
                    if next_read != next_write {
                        let ptr_write = prev_ptr_write.add(1);
                        swap(&mut *ptr_read, &mut *ptr_write);
                    }
                    next_write += 1;
                }
                next_read += 1;
            }
        }

        self.split_at_mut(next_write)
    }

    #[rapx::verify]
    fn get_disjoint_mut_ext<const N: usize>(
        &mut self,
        indices: [usize; N],
    ) -> Result<[&mut T; N], ()> {
        get_disjoint_check_valid_ext(&indices, self.len())?;
        unsafe { Ok(self.get_disjoint_unchecked_mut_ext(indices)) }
    }
}

#[rapx::verify]
fn get_disjoint_check_valid_ext<const N: usize>(
    indices: &[usize; N],
    len: usize,
) -> Result<(), ()> {
    let mut i = 0;
    while i < N {
        if indices[i] >= len {
            return Err(());
        }
        let mut j = 0;
        while j < i {
            if indices[i] == indices[j] {
                return Err(());
            }
            j += 1;
        }
        i += 1;
    }
    Ok(())
}

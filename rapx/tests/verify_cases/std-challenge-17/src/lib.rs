#![feature(register_tool)]
#![register_tool(rapx)]
#![feature(slice_index_methods)]
#![feature(portable_simd)]
#![allow(unsafe_op_in_unsafe_fn)]

use std::cmp::Ordering;
use std::mem::{align_of, swap, MaybeUninit};
use std::ops::Range;
use std::ptr;
use std::simd::Simd;
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
        I: SliceIndex<[T]> + Copy;
}

impl<T> SliceExt<T> for [T] {
    #[rapx::verify]
    #[rapx::requires(InBound(self, index))]
    unsafe fn get_unchecked_ext<I>(&self, index: I) -> &I::Output
    where
        I: SliceIndex<[T]>,
    {
        &*index.get_unchecked(self)
    }

    #[rapx::verify]
    #[rapx::requires(InBound(self, index))]
    unsafe fn get_unchecked_mut_ext<I>(&mut self, index: I) -> &mut I::Output
    where
        I: SliceIndex<[T]>,
    {
        &mut *index.get_unchecked_mut(self)
    }

    #[rapx::verify]
    #[rapx::requires(ValidNum(mid, "[0,self.len()]"))]
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
    #[rapx::requires(ValidNum(mid, "[0,self.len()]"))]
    unsafe fn split_at_mut_unchecked_ext(&mut self, mid: usize) -> (&mut [T], &mut [T]) {
        let len = self.len();
        let ptr = self.as_mut_ptr();

        debug_assert!(mid <= len);

        (
            from_raw_parts_mut(ptr, mid),
            from_raw_parts_mut(ptr.add(mid), len - mid),
        )
    }

    #[rapx::verify]
    #[rapx::requires(ValidNum(a, "[0,self.len())"))]
    #[rapx::requires(ValidNum(b, "[0,self.len())"))]
    unsafe fn swap_unchecked_ext(&mut self, a: usize, b: usize) {
        let len = self.len();
        debug_assert!(a < len && b < len);

        let ptr = self.as_mut_ptr();
        ptr::swap(ptr.add(a), ptr.add(b));
    }

    #[rapx::verify]
    #[rapx::requires(ValidNum(N, "[1,)"))]
    #[rapx::requires(ValidNum(self.len() % N == 0))]
    unsafe fn as_chunks_unchecked_ext<const N: usize>(&self) -> &[[T; N]] {
        debug_assert!(N != 0);
        debug_assert!(self.len() % N == 0);

        let new_len = self.len() / N;
        from_raw_parts(self.as_ptr() as *const [T; N], new_len)
    }

    #[rapx::verify]
    #[rapx::requires(ValidNum(N, "[1,)"))]
    #[rapx::requires(ValidNum(self.len() % N == 0))]
    unsafe fn as_chunks_unchecked_mut_ext<const N: usize>(&mut self) -> &mut [[T; N]] {
        debug_assert!(N != 0);
        debug_assert!(self.len() % N == 0);

        let new_len = self.len() / N;
        from_raw_parts_mut(self.as_mut_ptr() as *mut [T; N], new_len)
    }

    #[rapx::verify]
    #[rapx::requires(TransmuteWithoutAlign([T], [U]))]
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
    #[rapx::requires(TransmuteWithoutAlign([T], [U]))]
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
    #[rapx::requires(InBound(self, indices))]
    #[rapx::requires(NonOverlap(indices))]
    unsafe fn get_disjoint_unchecked_mut_ext<I, const N: usize>(
        &mut self,
        indices: [I; N],
    ) -> [&mut I::Output; N]
    where
        I: SliceIndex<[T]> + Copy,
    {
        let slice: *mut [T] = self;
        let mut arr: MaybeUninit<[&mut I::Output; N]> = MaybeUninit::uninit();
        let arr_ptr = arr.as_mut_ptr() as *mut &mut I::Output;

        let mut i = 0;
        while i < N {
            let idx = indices[i];
            let slice_ref: &mut [T] = unsafe { &mut *slice };
            let elem: &mut I::Output = unsafe { slice_ref.get_unchecked_mut(idx) };

            unsafe {
                arr_ptr.add(i).write(elem);
            }
            i += 1;
        }

        arr.assume_init()
    }
}

/// Safe abstractions from `core::slice` (challenge 0017).
///
/// Each method mirrors the corresponding `[T]` method in
/// `library/core/src/slice/mod.rs`. They are safe to call, so they carry no
/// `#[rapx::requires]` contract; RAPx must prove that the internal unsafe
/// operations cannot cause UB. Unsafe primitives are routed through the
/// contract-annotated `SliceExt` `_ext` methods so the whole obligation chain
/// is self-contained within this crate.
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
            // SAFETY: We explicitly check for the correct number of elements.
            Some(unsafe { &*(self.as_ptr() as *const [T; N]) })
        }
    }

    #[rapx::verify]
    fn first_chunk_mut_ext<const N: usize>(&mut self) -> Option<&mut [T; N]> {
        if self.len() < N {
            None
        } else {
            // SAFETY: We explicitly check for the correct number of elements.
            Some(unsafe { &mut *(self.as_mut_ptr() as *mut [T; N]) })
        }
    }

    #[rapx::verify]
    fn split_first_chunk_ext<const N: usize>(&self) -> Option<(&[T; N], &[T])> {
        let Some((first, tail)) = self.split_at_checked_ext(N) else { return None };
        // SAFETY: `split_at_checked_ext` guarantees `first.len() == N`.
        Some((unsafe { &*(first.as_ptr() as *const [T; N]) }, tail))
    }

    #[rapx::verify]
    fn split_first_chunk_mut_ext<const N: usize>(&mut self) -> Option<(&mut [T; N], &mut [T])> {
        let Some((first, tail)) = self.split_at_mut_checked_ext(N) else { return None };
        // SAFETY: `split_at_mut_checked_ext` guarantees `first.len() == N`.
        Some((unsafe { &mut *(first.as_mut_ptr() as *mut [T; N]) }, tail))
    }

    #[rapx::verify]
    fn split_last_chunk_ext<const N: usize>(&self) -> Option<(&[T], &[T; N])> {
        let Some(index) = self.len().checked_sub(N) else { return None };
        let (init, last) = self.split_at(index);
        // SAFETY: `last.len() == self.len() - index == N`.
        Some((init, unsafe { &*(last.as_ptr() as *const [T; N]) }))
    }

    #[rapx::verify]
    fn split_last_chunk_mut_ext<const N: usize>(&mut self) -> Option<(&mut [T], &mut [T; N])> {
        let Some(index) = self.len().checked_sub(N) else { return None };
        let (init, last) = self.split_at_mut(index);
        // SAFETY: `last.len() == self.len() - index == N`.
        Some((init, unsafe { &mut *(last.as_mut_ptr() as *mut [T; N]) }))
    }

    #[rapx::verify]
    fn last_chunk_ext<const N: usize>(&self) -> Option<&[T; N]> {
        let Some(index) = self.len().checked_sub(N) else { return None };
        let (_, last) = self.split_at(index);
        // SAFETY: `last.len() == self.len() - index == N`.
        Some(unsafe { &*(last.as_ptr() as *const [T; N]) })
    }

    #[rapx::verify]
    fn last_chunk_mut_ext<const N: usize>(&mut self) -> Option<&mut [T; N]> {
        let Some(index) = self.len().checked_sub(N) else { return None };
        let (_, last) = self.split_at_mut(index);
        // SAFETY: `last.len() == self.len() - index == N`.
        Some(unsafe { &mut *(last.as_mut_ptr() as *mut [T; N]) })
    }

    #[rapx::verify]
    fn as_chunks_ext<const N: usize>(&self) -> (&[[T; N]], &[T]) {
        assert!(N != 0, "chunk size must be non-zero");
        let len_rounded_down = self.len() / N * N;
        // SAFETY: The rounded-down value is <= the original length.
        let (multiple_of_n, remainder) = unsafe { self.split_at_unchecked_ext(len_rounded_down) };
        // SAFETY: `N != 0` and `multiple_of_n.len()` is a multiple of `N`.
        let array_slice = unsafe { multiple_of_n.as_chunks_unchecked_ext() };
        (array_slice, remainder)
    }

    #[rapx::verify]
    fn as_chunks_mut_ext<const N: usize>(&mut self) -> (&mut [[T; N]], &mut [T]) {
        assert!(N != 0, "chunk size must be non-zero");
        let len_rounded_down = self.len() / N * N;
        // SAFETY: The rounded-down value is <= the original length.
        let (multiple_of_n, remainder) =
            unsafe { self.split_at_mut_unchecked_ext(len_rounded_down) };
        // SAFETY: `N != 0` and `multiple_of_n.len()` is a multiple of `N`.
        let array_slice = unsafe { multiple_of_n.as_chunks_unchecked_mut_ext() };
        (array_slice, remainder)
    }

    #[rapx::verify]
    fn as_rchunks_ext<const N: usize>(&self) -> (&[T], &[[T; N]]) {
        assert!(N != 0, "chunk size must be non-zero");
        let len = self.len() / N;
        let (remainder, multiple_of_n) = self.split_at(self.len() - len * N);
        // SAFETY: `N != 0` and `multiple_of_n.len()` is a multiple of `N`.
        let array_slice = unsafe { multiple_of_n.as_chunks_unchecked_ext() };
        (remainder, array_slice)
    }

    #[rapx::verify]
    fn split_at_checked_ext(&self, mid: usize) -> Option<(&[T], &[T])> {
        if mid <= self.len() {
            // SAFETY: `mid <= self.len()` fulfills `split_at_unchecked`.
            Some(unsafe { self.split_at_unchecked_ext(mid) })
        } else {
            None
        }
    }

    #[rapx::verify]
    fn split_at_mut_checked_ext(&mut self, mid: usize) -> Option<(&mut [T], &mut [T])> {
        if mid <= self.len() {
            // SAFETY: `mid <= self.len()` fulfills `split_at_mut_unchecked`.
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

        // SAFETY: Both are subparts of the original slice: the memory range is
        // valid, and they don't overlap because each is only half of the slice.
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

        // SAFETY: Models `rotate::ptr_rotate(mid, p.add(mid), k)`, whose safety
        // requires the whole range `[p, p.add(mid + k))` to be valid for reads
        // and writes. `p.add(mid)` is in bounds because `mid <= len`.
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

        // SAFETY: See `rotate_left_ext`. `p.add(mid)` is in bounds because
        // `mid = len - k <= len`.
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
        // SAFETY: `self` and `src` have the same length and cannot overlap
        // because mutable references are exclusive.
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
        // SAFETY: the conditions for `ptr::copy` (and `ptr::add`) are checked above.
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
        // SAFETY: `self` and `other` have the same length and cannot overlap
        // because mutable references are exclusive.
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

            // SAFETY: `mid < size <= self.len()`.
            let cmp = f(unsafe { self.get_unchecked_ext(mid) });

            if cmp != Ordering::Greater {
                base = mid;
            }

            size -= half;
        }

        // SAFETY: `base` is always in `[0, self.len())`.
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

        // SAFETY: `next_read` and `next_write` stay within `[0, len)` inside the
        // loop, and `next_read >= next_write`, so `ptr_read` and `prev_ptr_write`
        // never alias, keeping the `&mut *` reborrows sound.
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
        // SAFETY: `get_disjoint_check_valid_ext` checked that all indices are
        // in bounds and pairwise disjoint.
        unsafe { Ok(self.get_disjoint_unchecked_mut_ext(indices)) }
    }
}

/// `as_simd` / `as_simd_mut` need the `SimdElement` bound on `T`, so they
/// live in their own trait.
#[cfg(not(rapx_rustc_ge_196))]
pub trait SliceSimdExt<T: std::simd::SimdElement> {
    fn as_simd_ext<const LANES: usize>(&self) -> (&[T], &[Simd<T, LANES>], &[T])
    where
        std::simd::LaneCount<LANES>: std::simd::SupportedLaneCount,
        Simd<T, LANES>: AsRef<[T; LANES]>;
    fn as_simd_mut_ext<const LANES: usize>(&mut self) -> (&mut [T], &mut [Simd<T, LANES>], &mut [T])
    where
        std::simd::LaneCount<LANES>: std::simd::SupportedLaneCount,
        Simd<T, LANES>: AsMut<[T; LANES]>;
}

#[cfg(not(rapx_rustc_ge_196))]
impl<T: std::simd::SimdElement> SliceSimdExt<T> for [T] {
    #[rapx::verify]
    fn as_simd_ext<const LANES: usize>(&self) -> (&[T], &[Simd<T, LANES>], &[T])
    where
        std::simd::LaneCount<LANES>: std::simd::SupportedLaneCount,
        Simd<T, LANES>: AsRef<[T; LANES]>,
    {
        assert!(LANES != 0, "SIMD lane count must be non-zero");
        unsafe { self.align_to_ext::<Simd<T, LANES>>() }
    }

    #[rapx::verify]
    fn as_simd_mut_ext<const LANES: usize>(&mut self) -> (&mut [T], &mut [Simd<T, LANES>], &mut [T])
    where
        std::simd::LaneCount<LANES>: std::simd::SupportedLaneCount,
        Simd<T, LANES>: AsMut<[T; LANES]>,
    {
        assert!(LANES != 0, "SIMD lane count must be non-zero");
        unsafe { self.align_to_mut_ext::<Simd<T, LANES>>() }
    }
}

#[cfg(rapx_rustc_ge_196)]
pub trait SliceSimdExt<T: std::simd::SimdElement> {
    fn as_simd_ext<const LANES: usize>(&self) -> (&[T], &[Simd<T, LANES>], &[T])
    where
        Simd<T, LANES>: AsRef<[T; LANES]>;
    fn as_simd_mut_ext<const LANES: usize>(&mut self) -> (&mut [T], &mut [Simd<T, LANES>], &mut [T])
    where
        Simd<T, LANES>: AsMut<[T; LANES]>;
}

#[cfg(rapx_rustc_ge_196)]
impl<T: std::simd::SimdElement> SliceSimdExt<T> for [T] {
    #[rapx::verify]
    fn as_simd_ext<const LANES: usize>(&self) -> (&[T], &[Simd<T, LANES>], &[T])
    where
        Simd<T, LANES>: AsRef<[T; LANES]>,
    {
        assert!(LANES != 0, "SIMD lane count must be non-zero");
        unsafe { self.align_to_ext::<Simd<T, LANES>>() }
    }

    #[rapx::verify]
    fn as_simd_mut_ext<const LANES: usize>(&mut self) -> (&mut [T], &mut [Simd<T, LANES>], &mut [T])
    where
        Simd<T, LANES>: AsMut<[T; LANES]>,
    {
        assert!(LANES != 0, "SIMD lane count must be non-zero");
        unsafe { self.align_to_mut_ext::<Simd<T, LANES>>() }
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

/// `as_flattened` / `as_flattened_mut` live on `[[T; N]]`, so they need their
/// own extension trait.
pub trait SliceArrayExt<T, const N: usize> {
    fn as_flattened_ext(&self) -> &[T];
    fn as_flattened_mut_ext(&mut self) -> &mut [T];
}

impl<T, const N: usize> SliceArrayExt<T, N> for [[T; N]] {
    #[rapx::verify]
    fn as_flattened_ext(&self) -> &[T] {
        let len = self.len() * N;
        // SAFETY: `[T; N]` is layout-identical to `N` consecutive `T`s.
        unsafe { from_raw_parts(self.as_ptr() as *const T, len) }
    }

    #[rapx::verify]
    fn as_flattened_mut_ext(&mut self) -> &mut [T] {
        let len = self.len() * N;
        // SAFETY: `[T; N]` is layout-identical to `N` consecutive `T`s.
        unsafe { from_raw_parts_mut(self.as_mut_ptr() as *mut T, len) }
    }
}

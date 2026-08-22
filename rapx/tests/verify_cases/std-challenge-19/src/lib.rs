#![feature(register_tool)]
#![register_tool(rapx)]
#![feature(allocator_api)]
#![feature(ptr_alignment_type)]
#![allow(unsafe_op_in_unsafe_fn)]
#![allow(dead_code)]

// Challenge 19: Verify the safety of `RawVec` functions.
// A faithful, self-contained port of `library/alloc/src/raw_vec/mod.rs`.
// Adaptations: `Cap` -> `usize`, `Unique<u8>` -> `NonNull<u8>`, plus an
// `Allocated(ptr, u8, cap)` invariant so allocator provenance stays provable.

use std::alloc::{Allocator, Global, Layout};
use std::boxed::Box;
use std::marker::PhantomData;
use std::mem::{Alignment, ManuallyDrop, MaybeUninit};
use std::ptr::{self, NonNull};

/// The niche-optimized capacity type is `usize`; see the module doc.
type Cap = usize;

const ZERO_CAP: Cap = 0;

/// One central function responsible for reporting capacity overflows.
fn capacity_overflow() -> ! {
    panic!("capacity overflow");
}

/// The initialization requested for a fresh allocation.
pub enum AllocInit {
    /// The contents of the new memory are uninitialized.
    Uninitialized,
    /// The new memory is guaranteed to be zeroed.
    Zeroed,
}

/// Local replacement for the (unstable) `TryReserveError`/`TryReserveErrorKind`.
pub enum TryReserveErrorExt {
    CapacityOverflow,
    AllocError { layout: Layout },
}

/// Central function for reserve error handling.
fn handle_error_ext(e: TryReserveErrorExt) -> ! {
    match e {
        TryReserveErrorExt::CapacityOverflow => capacity_overflow(),
        TryReserveErrorExt::AllocError { layout } => std::alloc::handle_alloc_error(layout),
    }
}

const fn min_non_zero_cap(size: usize) -> usize {
    if size == 1 {
        8
    } else if size <= 1024 {
        4
    } else {
        1
    }
}

/// `RawVec<T, A>`: the element-typed wrapper around a type-erased buffer.
pub struct RawVec<T, A: Allocator = Global> {
    inner: RawVecInner<A>,
    _marker: PhantomData<T>,
}

/// `RawVecInner<A>`: like `RawVec`, but only generic over the allocator; `Cap` is plain `usize`.
#[rapx::invariant(Allocated(ptr, u8, cap))]
pub struct RawVecInner<A: Allocator = Global> {
    ptr: NonNull<u8>,
    /// Never used for ZSTs; `capacity()` returns `usize::MAX` in that case.
    cap: Cap,
    alloc: A,
}

impl<T, A: Allocator> RawVec<T, A> {
    /// Like `new`, but parameterized over the choice of allocator for the returned `RawVec`.
    #[rapx::verify]
    pub fn new_in_ext(alloc: A) -> Self {
        // Check the assumption made in `current_memory`.
        const { assert!(Layout::new::<T>().size() % Layout::new::<T>().align() == 0) };
        Self { inner: RawVecInner::new_in_ext(alloc, Alignment::of::<T>()), _marker: PhantomData }
    }

    /// Like `with_capacity`, but parameterized over the choice of allocator for the returned `RawVec`.
    #[rapx::verify]
    pub fn with_capacity_in_ext(capacity: usize, alloc: A) -> Self {
        Self {
            inner: RawVecInner::with_capacity_in_ext(capacity, alloc, Layout::new::<T>()),
            _marker: PhantomData,
        }
    }

    /// Converts the buffer into `Box<[MaybeUninit<T>]>` with the specified `len`.
    ///
    /// # Safety
    /// `len` must be between the last requested capacity and `self.capacity()`.
    #[rapx::verify]
    #[rapx::requires(ValidNum(len <= self.capacity_ext()))]
    pub unsafe fn into_box_ext(self, len: usize) -> Box<[MaybeUninit<T>], A> {
        // Sanity-check one half of the safety requirement (we cannot check the
        // other half).
        debug_assert!(len <= self.capacity_ext());

        let me = ManuallyDrop::new(self);
        unsafe {
            let slice = ptr::slice_from_raw_parts_mut(me.ptr_ext() as *mut MaybeUninit<T>, len);
            Box::from_raw_in(slice, ptr::read(&me.inner.alloc))
        }
    }

    /// Reconstitutes a `RawVec` from a pointer, capacity, and allocator.
    ///
    /// # Safety
    /// `ptr` must be allocated via `alloc` with `capacity` (<= `isize::MAX`).
    #[rapx::verify]
    #[rapx::requires(ValidNum(capacity <= isize::MAX))]
    #[rapx::requires(Allocated(ptr, T, capacity))]
    #[rapx::requires(Align(ptr, T))]
    pub unsafe fn from_raw_parts_in_ext(ptr: *mut T, capacity: usize, alloc: A) -> Self {
        // SAFETY: precondition passed to the caller.
        unsafe {
            let ptr = ptr.cast();
            let capacity = new_cap_ext::<T>(capacity);
            Self {
                inner: RawVecInner::from_raw_parts_in_ext(ptr, capacity, alloc),
                _marker: PhantomData,
            }
        }
    }

    /// Convenience method for hoisting the non-null precondition out of `from_raw_parts_in`.
    ///
    /// # Safety
    /// See `from_raw_parts_in`.
    #[rapx::verify]
    #[rapx::requires(ValidNum(capacity <= isize::MAX))]
    #[rapx::requires(Allocated(ptr, T, capacity))]
    #[rapx::requires(Align(ptr, T))]
    pub unsafe fn from_nonnull_in_ext(ptr: NonNull<T>, capacity: usize, alloc: A) -> Self {
        // SAFETY: precondition passed to the caller.
        unsafe {
            let ptr = ptr.cast();
            let capacity = new_cap_ext::<T>(capacity);
            Self {
                inner: RawVecInner::from_nonnull_in_ext(ptr, capacity, alloc),
                _marker: PhantomData,
            }
        }
    }

    /// Gets a raw pointer to the start of the allocation.
    pub fn ptr_ext(&self) -> *mut T {
        self.inner.ptr_ext()
    }

    pub fn non_null_ext(&self) -> NonNull<T> {
        self.inner.non_null_ext()
    }

    /// Gets the capacity of the allocation (`usize::MAX` if `T` is zero-sized).
    pub fn capacity_ext(&self) -> usize {
        self.inner.capacity_ext(std::mem::size_of::<T>())
    }

    /// Returns a shared reference to the allocator backing this `RawVec`.
    pub fn allocator_ext(&self) -> &A {
        self.inner.allocator_ext()
    }
}

impl<T, A: Allocator> Drop for RawVec<T, A> {
    /// Frees the memory owned by the `RawVec` without dropping its contents.
    fn drop(&mut self) {
        // SAFETY: we are in a Drop impl; `self.inner` will not be used again.
        unsafe { self.inner.deallocate_ext(Layout::new::<T>()) }
    }
}

impl<A: Allocator> RawVecInner<A> {
    fn new_in_ext(alloc: A, align: Alignment) -> Self {
        // `ptr` is a non-null, well-aligned dangling pointer (address == align).
        let ptr = NonNull::without_provenance(align.as_nonzero_usize());
        // `cap: 0` means "unallocated". zero-sized types are ignored.
        Self { ptr, cap: ZERO_CAP, alloc }
    }

    fn with_capacity_in_ext(capacity: usize, alloc: A, elem_layout: Layout) -> Self {
        match Self::try_allocate_in_ext(capacity, AllocInit::Uninitialized, alloc, elem_layout) {
            Ok(this) => this,
            Err(err) => handle_error_ext(err),
        }
    }

    #[rapx::verify]
    fn try_allocate_in_ext(
        capacity: usize,
        init: AllocInit,
        alloc: A,
        elem_layout: Layout,
    ) -> Result<Self, TryReserveErrorExt> {
        // We avoid `unwrap_or_else` here because it bloats the amount of
        // LLVM IR generated.
        let layout = match layout_array_ext(capacity, elem_layout) {
            Ok(layout) => layout,
            Err(_) => return Err(TryReserveErrorExt::CapacityOverflow),
        };

        // Don't allocate here because `Drop` will not deallocate when
        // `capacity` is 0.
        if layout.size() == 0 {
            return Ok(Self::new_in_ext(alloc, elem_layout.alignment()));
        }

        let result = match init {
            AllocInit::Uninitialized => alloc.allocate(layout),
            AllocInit::Zeroed => alloc.allocate_zeroed(layout),
        };
        let ptr = match result {
            Ok(ptr) => ptr,
            Err(_) => return Err(TryReserveErrorExt::AllocError { layout }),
        };

        // Allocators currently return a `NonNull<[u8]>` whose length matches
        // the size requested. If that ever changes, the capacity here should
        // change to `ptr.len() / size_of::<T>()`.
        Ok(Self { ptr: ptr.cast(), cap: capacity, alloc })
    }

    unsafe fn from_raw_parts_in_ext(ptr: *mut u8, cap: Cap, alloc: A) -> Self {
        Self { ptr: unsafe { NonNull::new_unchecked(ptr) }, cap, alloc }
    }

    unsafe fn from_nonnull_in_ext(ptr: NonNull<u8>, cap: Cap, alloc: A) -> Self {
        Self { ptr, cap, alloc }
    }

    fn ptr_ext<T>(&self) -> *mut T {
        self.non_null_ext::<T>().as_ptr()
    }

    fn non_null_ext<T>(&self) -> NonNull<T> {
        self.ptr.cast()
    }

    fn capacity_ext(&self, elem_size: usize) -> usize {
        if elem_size == 0 { usize::MAX } else { self.cap }
    }

    fn allocator_ext(&self) -> &A {
        &self.alloc
    }

    /// # Safety
    /// `elem_layout` must be the layout used to construct `self`; its size must be a multiple of its alignment.
    #[rapx::verify]
    #[rapx::requires(ValidNum(elem_layout.size() % elem_layout.align() == 0))]
    unsafe fn current_memory_ext(&self, elem_layout: Layout) -> Option<(NonNull<u8>, Layout)> {
        if elem_layout.size() == 0 || self.cap == 0 {
            None
        } else {
            // This memory has already been allocated so we know it can't
            // overflow, and currently Rust does not support such types, so we
            // skip some checks.
            unsafe {
                let alloc_size = elem_layout.size().unchecked_mul(self.cap);
                let layout = Layout::from_size_align_unchecked(alloc_size, elem_layout.align());
                Some((self.ptr, layout))
            }
        }
    }

    /// # Safety
    /// `elem_layout` must be valid for `self`; its size a multiple of its alignment.
    #[rapx::verify]
    #[rapx::requires(ValidNum(elem_layout.size() % elem_layout.align() == 0))]
    unsafe fn try_reserve_ext(
        &mut self,
        len: usize,
        additional: usize,
        elem_layout: Layout,
    ) -> Result<(), TryReserveErrorExt> {
        if self.needs_to_grow_ext(len, additional, elem_layout) {
            // SAFETY: precondition passed to caller.
            unsafe {
                self.grow_amortized_ext(len, additional, elem_layout)?;
            }
        }
        Ok(())
    }

    /// # Safety
    /// `elem_layout` must be valid for `self`; its size a multiple of its alignment.
    #[rapx::verify]
    #[rapx::requires(ValidNum(elem_layout.size() % elem_layout.align() == 0))]
    unsafe fn try_reserve_exact_ext(
        &mut self,
        len: usize,
        additional: usize,
        elem_layout: Layout,
    ) -> Result<(), TryReserveErrorExt> {
        if self.needs_to_grow_ext(len, additional, elem_layout) {
            // SAFETY: precondition passed to caller.
            unsafe {
                self.grow_exact_ext(len, additional, elem_layout)?;
            }
        }
        Ok(())
    }

    fn needs_to_grow_ext(&self, len: usize, additional: usize, elem_layout: Layout) -> bool {
        additional > self.capacity_ext(elem_layout.size()).wrapping_sub(len)
    }

    /// # Safety
    /// `ptr` must be the buffer from a prior allocation for the given `cap`.
    #[rapx::verify]
    unsafe fn set_ptr_and_cap_ext(&mut self, ptr: NonNull<[u8]>, cap: usize) {
        // Allocators currently return a `NonNull<[u8]>` whose length matches
        // the size requested.
        self.ptr = ptr.cast();
        self.cap = cap;
    }

    /// # Safety
    /// `elem_layout` must be valid for `self` (size a multiple of its alignment); `len + additional` must exceed the current capacity.
    #[rapx::verify]
    #[rapx::requires(ValidNum(elem_layout.size() % elem_layout.align() == 0))]
    unsafe fn grow_amortized_ext(
        &mut self,
        len: usize,
        additional: usize,
        elem_layout: Layout,
    ) -> Result<(), TryReserveErrorExt> {
        // This is ensured by the calling contexts.
        debug_assert!(additional > 0);

        if elem_layout.size() == 0 {
            // Since we return a capacity of `usize::MAX` when `elem_size` is
            // 0, getting to here necessarily means the `RawVec` is overfull.
            return Err(TryReserveErrorExt::CapacityOverflow);
        }

        // Nothing we can really do about these checks, sadly.
        let required_cap = len.checked_add(additional).ok_or(TryReserveErrorExt::CapacityOverflow)?;

        // This guarantees exponential growth. The doubling cannot overflow
        // because `cap <= isize::MAX` and the type of `cap` is `usize`.
        let cap = cmp_max(self.cap * 2, required_cap);
        let cap = cmp_max(min_non_zero_cap(elem_layout.size()), cap);

        // SAFETY: `cap >= len + additional` and the other preconditions passed to the caller.
        let ptr = unsafe { self.finish_grow_ext(cap, elem_layout)? };

        // SAFETY: `finish_grow` would have failed if `cap > isize::MAX`.
        unsafe { self.set_ptr_and_cap_ext(ptr, cap) };
        Ok(())
    }

    /// # Safety
    /// `elem_layout` must be valid for `self` (size a multiple of its alignment); `len + additional` must exceed the current capacity.
    #[rapx::verify]
    #[rapx::requires(ValidNum(elem_layout.size() % elem_layout.align() == 0))]
    unsafe fn grow_exact_ext(
        &mut self,
        len: usize,
        additional: usize,
        elem_layout: Layout,
    ) -> Result<(), TryReserveErrorExt> {
        if elem_layout.size() == 0 {
            // Since we return a capacity of `usize::MAX` when the type size is
            // 0, getting to here necessarily means the `RawVec` is overfull.
            return Err(TryReserveErrorExt::CapacityOverflow);
        }

        let cap = len.checked_add(additional).ok_or(TryReserveErrorExt::CapacityOverflow)?;

        // SAFETY: preconditions passed to caller.
        let ptr = unsafe { self.finish_grow_ext(cap, elem_layout)? };

        // SAFETY: `finish_grow` would have failed if `cap > isize::MAX`.
        unsafe { self.set_ptr_and_cap_ext(ptr, cap) };
        Ok(())
    }

    /// # Safety
    /// `elem_layout` must be valid for `self` (size a multiple of its alignment); `cap` must exceed the current capacity.
    #[rapx::verify]
    #[rapx::requires(ValidNum(elem_layout.size() % elem_layout.align() == 0))]
    unsafe fn finish_grow_ext(
        &self,
        cap: usize,
        elem_layout: Layout,
    ) -> Result<NonNull<[u8]>, TryReserveErrorExt> {
        let new_layout = layout_array_ext(cap, elem_layout)?;

        // Inlined `current_memory_ext`: materialize `self.ptr`'s allocation
        // provenance directly (a black-box call would strip it, leaving
        // `Allocator::grow`'s `Allocated` requirement unprovable).
        let memory = if !(elem_layout.size() == 0 || self.cap == 0) {
            let old_layout = unsafe {
                let alloc_size = elem_layout.size().unchecked_mul(self.cap);
                Layout::from_size_align_unchecked(alloc_size, elem_layout.align())
            };
            debug_assert_eq!(old_layout.align(), new_layout.align());
            // The allocator checks for alignment equality.
            self.alloc.grow(self.ptr, old_layout, new_layout)
        } else {
            self.alloc.allocate(new_layout)
        };

        memory.map_err(|_| TryReserveErrorExt::AllocError { layout: new_layout })
    }

    /// # Safety
    /// `elem_layout` must be valid for `self` (size a multiple of its alignment); `cap` must be <= `self.capacity(...)`.
    #[rapx::verify]
    #[rapx::requires(ValidNum(elem_layout.size() % elem_layout.align() == 0))]
    unsafe fn shrink_ext(&mut self, cap: usize, elem_layout: Layout) -> Result<(), TryReserveErrorExt> {
        assert!(cap <= self.capacity_ext(elem_layout.size()), "Tried to shrink to a larger capacity");
        // SAFETY: just checked this isn't trying to grow.
        unsafe { self.shrink_unchecked_ext(cap, elem_layout) }
    }

    /// `shrink`, but without the capacity check.
    ///
    /// # Safety
    /// `cap <= self.capacity()`.
    #[rapx::verify]
    #[rapx::requires(ValidNum(cap <= self.capacity_ext(elem_layout.size())))]
    #[rapx::requires(ValidNum(elem_layout.size() % elem_layout.align() == 0))]
    unsafe fn shrink_unchecked_ext(
        &mut self,
        cap: usize,
        elem_layout: Layout,
    ) -> Result<(), TryReserveErrorExt> {
        // Inlined `current_memory_ext`: materialize `self.ptr`'s allocation
        // provenance directly (a black-box call would strip it, leaving the
        // allocator's `Allocated` requirement unprovable).
        if elem_layout.size() == 0 || self.cap == 0 {
            return Ok(());
        }
        let (ptr, layout) = {
            let layout = unsafe {
                let alloc_size = elem_layout.size().unchecked_mul(self.cap);
                Layout::from_size_align_unchecked(alloc_size, elem_layout.align())
            };
            (self.ptr, layout)
        };

        // If shrinking to 0, deallocate the buffer. We don't reach this point
        // for the T::IS_ZST case since current_memory() will have returned
        // None.
        if cap == 0 {
            unsafe { self.alloc.deallocate(ptr, layout) };
            // A dangling but well-aligned pointer, mirroring the original
            // `ptr::without_provenance_mut(elem_layout.align())`.
            self.ptr = NonNull::without_provenance(elem_layout.alignment().as_nonzero_usize());
            self.cap = ZERO_CAP;
        } else {
            let ptr = unsafe {
                // Layout cannot overflow here because it would have overflowed
                // earlier when capacity was larger.
                let new_size = elem_layout.size().unchecked_mul(cap);
                let new_layout = Layout::from_size_align_unchecked(new_size, layout.align());
                self.alloc
                    .shrink(ptr, layout, new_layout)
                    .map_err(|_| TryReserveErrorExt::AllocError { layout: new_layout })?
            };
            // SAFETY: if the allocation is valid, then the capacity is too.
            unsafe {
                self.set_ptr_and_cap_ext(ptr, cap);
            }
        }
        Ok(())
    }

    /// # Safety
    /// Deallocates without updating `ptr`/`cap`; do not use the buffer after this returns.
    #[rapx::verify]
    #[rapx::requires(ValidNum(elem_layout.size() % elem_layout.align() == 0))]
    unsafe fn deallocate_ext(&mut self, elem_layout: Layout) {
        // SAFETY: precondition passed to caller.
        if !(elem_layout.size() == 0 || self.cap == 0) {
            unsafe {
                let alloc_size = elem_layout.size().unchecked_mul(self.cap);
                let layout = Layout::from_size_align_unchecked(alloc_size, elem_layout.align());
                self.alloc.deallocate(self.ptr, layout);
            }
        }
    }
}

/// `Cap(cap)`, except if `T` is a ZST then `ZERO_CAP`.
///
/// # Safety: `cap` must be <= `isize::MAX`.
#[rapx::verify]
#[rapx::requires(ValidNum(cap <= isize::MAX))]
unsafe fn new_cap_ext<T>(cap: usize) -> Cap {
    if std::mem::size_of::<T>() == 0 { ZERO_CAP } else { cap }
}

/// Computes the layout for an allocation of `cap` elements of `elem_layout`.
#[rapx::verify]
fn layout_array_ext(cap: usize, elem_layout: Layout) -> Result<Layout, TryReserveErrorExt> {
    match elem_layout.repeat(cap) {
        Ok((layout, _pad)) => Ok(layout),
        Err(_) => Err(TryReserveErrorExt::CapacityOverflow),
    }
}

/// Local `cmp::max` shim (avoids an external `Ord::max` summary).
fn cmp_max(a: usize, b: usize) -> usize {
    if a >= b { a } else { b }
}

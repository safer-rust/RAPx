#![feature(register_tool)]
#![register_tool(rapx)]
#![feature(pointer_is_aligned_to)]
#![feature(slice_ptr_get)]
#![allow(unsafe_op_in_unsafe_fn)]
#![allow(dead_code)]

// Challenge 6: Safety of `NonNull` — a faithful, self-contained port of
// `library/core/src/ptr/non_null.rs`. Raw-pointer operations are delegated to
// `*const T` / `*mut T`, for which RAPx already ships verified contracts.

use std::mem::MaybeUninit;
use std::num::NonZero;
use std::ptr;
use std::slice;

/// `*mut T` but non-zero and hence covariant; `#[repr(transparent)]` over a `*const T`.
struct NonNull<T: ?Sized> {
    pointer: *const T,
}

impl<T: ?Sized> Copy for NonNull<T> {}
impl<T: ?Sized> Clone for NonNull<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: ?Sized> NonNull<T> {
    /// Creates a new `NonNull` without checking for null.
    #[rapx::verify]
    #[rapx::requires(NonNull(ptr))]
    pub const unsafe fn new_unchecked(ptr: *mut T) -> Self {
        // SAFETY: the caller must guarantee that `ptr` is non-null.
        NonNull { pointer: ptr as *const T }
    }

    /// Creates a new `NonNull` if `ptr` is non-null.
    #[rapx::verify]
    pub const fn new(ptr: *mut T) -> Option<Self> {
        if !ptr.is_null() {
            // SAFETY: The pointer is already checked and is not null.
            Some(unsafe { Self::new_unchecked(ptr) })
        } else {
            None
        }
    }

    /// Acquires the underlying `*mut` pointer.
    #[rapx::verify]
    pub const fn as_ptr(self) -> *mut T {
        // SAFETY: `NonNull` is transparent over `*const T`, which has the same
        // layout as `*mut T`.
        self.pointer as *mut T
    }

    /// Returns a shared reference to the value.
    #[rapx::verify]
    #[rapx::requires(Ptr2Ref(self.pointer, T))]
    pub const unsafe fn as_ref<'a>(&self) -> &'a T {
        // SAFETY: the caller must guarantee that `self` meets all the
        // requirements for a reference.
        unsafe { &*self.pointer }
    }

    /// Returns a unique reference to the value.
    #[rapx::verify]
    #[rapx::requires(Ptr2Ref(self.pointer, T))]
    pub const unsafe fn as_mut<'a>(&mut self) -> &'a mut T {
        // SAFETY: the caller must guarantee that `self` meets all the
        // requirements for a mutable reference.
        unsafe { &mut *(self.pointer as *mut T) }
    }

    /// Casts to a pointer of another type.
    #[rapx::verify]
    pub const fn cast<U>(self) -> NonNull<U> {
        // SAFETY: `self` is a `NonNull` pointer which is necessarily non-null.
        NonNull { pointer: self.pointer as *const U }
    }
}

impl<T: Sized> NonNull<T> {
    /// Returns a shared reference to the value, without requiring it to be initialized.
    #[rapx::verify]
    #[rapx::requires(Ptr2Ref(self.pointer, T))]
    pub const unsafe fn as_uninit_ref<'a>(self) -> &'a MaybeUninit<T> {
        // SAFETY: the caller must guarantee that `self` meets all the
        // requirements for a reference.
        unsafe { &*(self.pointer as *const MaybeUninit<T>) }
    }

    /// Returns a unique reference to the value, without requiring it to be initialized.
    #[rapx::verify]
    #[rapx::requires(Ptr2Ref(self.pointer, T))]
    pub const unsafe fn as_uninit_mut<'a>(self) -> &'a mut MaybeUninit<T> {
        // SAFETY: the caller must guarantee that `self` meets all the
        // requirements for a reference.
        unsafe { &mut *(self.pointer as *mut MaybeUninit<T>) }
    }

    /// Creates a new `NonNull` that is dangling, but well-aligned.
    #[rapx::verify]
    pub const fn dangling() -> Self {
        let align = std::mem::align_of::<T>();
        // `align` is a power of two >= 1, hence a non-zero address.
        NonNull { pointer: align as *const T }
    }

    /// Gets the "address" portion of the pointer.
    #[rapx::verify]
    pub fn addr(self) -> NonZero<usize> {
        // SAFETY: the pointer is guaranteed by the type to be non-null,
        // meaning that the address will be non-zero.
        unsafe { NonZero::new_unchecked(self.pointer as usize) }
    }

    /// Creates a new pointer with the given address and the provenance of `self`.
    #[rapx::verify]
    pub fn with_addr(self, addr: NonZero<usize>) -> Self {
        // `addr` is guaranteed to be non-zero.
        NonNull { pointer: addr.get() as *const T }
    }

    /// Creates a new pointer by mapping `self`'s address to a new one.
    #[rapx::verify]
    pub fn map_addr(self, f: impl FnOnce(NonZero<usize>) -> NonZero<usize>) -> Self {
        self.with_addr(f(self.addr()))
    }

    /// Adds an offset to a pointer (convenience for `.offset(count as isize)`).
    #[rapx::verify]
    #[rapx::requires(InBound(self.pointer, T, count))]
    pub const unsafe fn add(self, count: usize) -> Self {
        // SAFETY: the caller must uphold the safety contract for `add`.
        unsafe { NonNull { pointer: self.pointer.add(count) } }
    }

    /// Calculates the offset from a pointer in bytes.
    #[rapx::verify]
    #[rapx::requires(InBound(self.pointer, u8, count))]
    pub const unsafe fn byte_add(self, count: usize) -> Self {
        // SAFETY: the caller must uphold the safety contract for `byte_add`.
        unsafe { NonNull { pointer: self.pointer.byte_add(count) } }
    }

    /// Subtracts an offset from a pointer.
    #[rapx::verify]
    #[rapx::requires(InBound(self.pointer, T, count))]
    pub const unsafe fn sub(self, count: usize) -> Self {
        // SAFETY: the caller must uphold the safety contract for `sub`.
        unsafe { NonNull { pointer: self.pointer.sub(count) } }
    }

    /// Calculates the offset from a pointer in bytes.
    #[rapx::verify]
    #[rapx::requires(InBound(self.pointer, u8, count))]
    pub const unsafe fn byte_sub(self, count: usize) -> Self {
        // SAFETY: the caller must uphold the safety contract for `byte_sub`.
        unsafe { NonNull { pointer: self.pointer.byte_sub(count) } }
    }

    /// Adds an offset to a pointer.
    #[rapx::verify]
    #[rapx::requires(InBound(self.pointer, T, count))]
    pub const unsafe fn offset(self, count: isize) -> Self {
        // SAFETY: the caller must uphold the safety contract for `offset`.
        unsafe { NonNull { pointer: self.pointer.offset(count) } }
    }

    /// Calculates the offset from a pointer in bytes.
    #[rapx::verify]
    #[rapx::requires(InBound(self.pointer, u8, count))]
    pub const unsafe fn byte_offset(self, count: isize) -> Self {
        // SAFETY: the caller must uphold the safety contract for `byte_offset`.
        unsafe { NonNull { pointer: self.pointer.byte_offset(count) } }
    }

    /// Calculates the distance between two pointers within the same allocation.
    #[rapx::verify]
    #[rapx::requires(InBound(self.pointer, T, 1))]
    #[rapx::requires(Size(T, sized))]
    pub const unsafe fn offset_from(self, origin: NonNull<T>) -> isize {
        // SAFETY: the caller must uphold the safety contract for `offset_from`.
        unsafe { self.pointer.offset_from(origin.pointer) }
    }

    /// Calculates the distance between two pointers within the same allocation (in bytes).
    #[rapx::verify]
    #[rapx::requires(InBound(self.pointer, u8, 1))]
    pub const unsafe fn byte_offset_from<U: ?Sized>(self, origin: NonNull<U>) -> isize {
        // SAFETY: the caller must uphold the safety contract for `byte_offset_from`.
        unsafe { self.pointer.byte_offset_from(origin.pointer) }
    }

    /// Calculates the distance between two pointers (`self >= origin`).
    #[rapx::verify]
    #[rapx::requires(ValidNum(self.pointer - subtracted.pointer >= 0))]
    #[rapx::requires(ValidNum((self.pointer - subtracted.pointer) % size_of(T) == 0))]
    pub const unsafe fn offset_from_unsigned(self, subtracted: NonNull<T>) -> usize {
        // SAFETY: the caller must uphold the safety contract for `offset_from_unsigned`.
        unsafe { self.pointer.offset_from_unsigned(subtracted.pointer) }
    }

    /// Reads the value from `self` without moving it.
    #[rapx::verify]
    #[rapx::requires(ValidPtr(self.pointer, T, 1))]
    #[rapx::requires(Align(self.pointer, T))]
    #[rapx::requires(Typed(self.pointer, T))]
    #[rapx::requires(Init(self.pointer, T, 1))]
    #[rapx::requires(any(Trait(T, Copy), Alias(self.pointer, return)))]
    pub const unsafe fn read(self) -> T {
        // SAFETY: the caller must uphold the safety contract for `read`.
        unsafe { ptr::read(self.pointer) }
    }

    /// Performs a volatile read of the value from `self` without moving it.
    #[rapx::verify]
    #[rapx::requires(ValidPtr(self.pointer, T, 1))]
    #[rapx::requires(Align(self.pointer, T))]
    #[rapx::requires(Init(self.pointer, T, 1))]
    #[rapx::requires(any(Trait(T, Copy), Alias(self.pointer, return)))]
    pub unsafe fn read_volatile(self) -> T {
        // SAFETY: the caller must uphold the safety contract for `read_volatile`.
        unsafe { ptr::read_volatile(self.pointer) }
    }

    /// Reads the value from `self` without moving it (may be unaligned).
    #[rapx::verify]
    #[rapx::requires(ValidPtr(self.pointer, T, 1))]
    #[rapx::requires(Init(self.pointer, T, 1))]
    #[rapx::requires(any(Trait(T, Copy), Alias(self.pointer, return)))]
    pub const unsafe fn read_unaligned(self) -> T {
        // SAFETY: the caller must uphold the safety contract for `read_unaligned`.
        unsafe { ptr::read_unaligned(self.pointer) }
    }

    /// Copies `count * size_of::<T>()` bytes from `self` to `dest` (may overlap).
    #[rapx::verify]
    #[rapx::requires(ValidPtr(self.pointer, T, count))]
    #[rapx::requires(Align(self.pointer, T))]
    #[rapx::requires(ValidPtr(dest.pointer, T, count))]
    #[rapx::requires(Align(dest.pointer, T))]
    pub const unsafe fn copy_to(self, dest: NonNull<T>, count: usize) {
        // SAFETY: the caller must uphold the safety contract for `copy`.
        unsafe { ptr::copy(self.pointer, dest.pointer as *mut T, count) }
    }

    /// Copies `count * size_of::<T>()` bytes from `self` to `dest` (may not overlap).
    #[rapx::verify]
    #[rapx::requires(ValidPtr(self.pointer, T, count))]
    #[rapx::requires(Align(self.pointer, T))]
    #[rapx::requires(ValidPtr(dest.pointer, T, count))]
    #[rapx::requires(Align(dest.pointer, T))]
    #[rapx::requires(NonOverlap(dest.pointer, self.pointer, T, count))]
    pub const unsafe fn copy_to_nonoverlapping(self, dest: NonNull<T>, count: usize) {
        // SAFETY: the caller must uphold the safety contract for `copy_nonoverlapping`.
        unsafe { ptr::copy_nonoverlapping(self.pointer, dest.pointer as *mut T, count) }
    }

    /// Copies `count * size_of::<T>()` bytes from `src` to `self` (may overlap).
    #[rapx::verify]
    #[rapx::requires(ValidPtr(self.pointer, T, count))]
    #[rapx::requires(Align(self.pointer, T))]
    #[rapx::requires(ValidPtr(src.pointer, T, count))]
    #[rapx::requires(Align(src.pointer, T))]
    pub const unsafe fn copy_from(self, src: NonNull<T>, count: usize) {
        // SAFETY: the caller must uphold the safety contract for `copy`.
        unsafe { ptr::copy(src.pointer, self.pointer as *mut T, count) }
    }

    /// Copies `count * size_of::<T>()` bytes from `src` to `self` (may not overlap).
    #[rapx::verify]
    #[rapx::requires(ValidPtr(self.pointer, T, count))]
    #[rapx::requires(Align(self.pointer, T))]
    #[rapx::requires(ValidPtr(src.pointer, T, count))]
    #[rapx::requires(Align(src.pointer, T))]
    #[rapx::requires(NonOverlap(self.pointer, src.pointer, T, count))]
    pub const unsafe fn copy_from_nonoverlapping(self, src: NonNull<T>, count: usize) {
        // SAFETY: the caller must uphold the safety contract for `copy_nonoverlapping`.
        unsafe { ptr::copy_nonoverlapping(src.pointer, self.pointer as *mut T, count) }
    }

    /// Executes the destructor (if any) of the pointed-to value.
    #[rapx::verify]
    #[rapx::requires(ValidPtr(self.pointer, T, 1))]
    #[rapx::requires(Align(self.pointer, T))]
    pub unsafe fn drop_in_place(self) {
        // SAFETY: the caller must uphold the safety contract for `drop_in_place`.
        unsafe { ptr::drop_in_place(self.pointer as *mut T) }
    }

    /// Overwrites a memory location with the given value.
    #[rapx::verify]
    #[rapx::requires(ValidPtr(self.pointer, T, 1))]
    #[rapx::requires(Align(self.pointer, T))]
    pub const unsafe fn write(self, val: T) {
        // SAFETY: the caller must uphold the safety contract for `write`.
        unsafe { ptr::write(self.pointer as *mut T, val) }
    }

    /// Invokes memset on the specified pointer.
    #[rapx::verify]
    #[rapx::requires(ValidPtr(self.pointer, T, count))]
    #[rapx::requires(Align(self.pointer, T))]
    #[rapx::requires(Typed(self.pointer, T))]
    pub const unsafe fn write_bytes(self, val: u8, count: usize) {
        // SAFETY: the caller must uphold the safety contract for `write_bytes`.
        unsafe { ptr::write_bytes(self.pointer as *mut u8, val, count) }
    }

    /// Performs a volatile write of a memory location with the given value.
    #[rapx::verify]
    #[rapx::requires(ValidPtr(self.pointer, T, 1))]
    #[rapx::requires(Align(self.pointer, T))]
    pub unsafe fn write_volatile(self, val: T) {
        // SAFETY: the caller must uphold the safety contract for `write_volatile`.
        unsafe { ptr::write_volatile(self.pointer as *mut T, val) }
    }

    /// Overwrites a memory location with the given value (may be unaligned).
    #[rapx::verify]
    #[rapx::requires(ValidPtr(self.pointer, T, 1))]
    pub const unsafe fn write_unaligned(self, val: T) {
        // SAFETY: the caller must uphold the safety contract for `write_unaligned`.
        unsafe { ptr::write_unaligned(self.pointer as *mut T, val) }
    }

    /// Replaces the value at `self` with `src`, returning the old value.
    #[rapx::verify]
    #[rapx::requires(ValidPtr(self.pointer, T, 1))]
    #[rapx::requires(Align(self.pointer, T))]
    #[rapx::requires(Init(self.pointer, T, 1))]
    pub const unsafe fn replace(self, src: T) -> T {
        // SAFETY: the caller must uphold the safety contract for `replace`.
        unsafe { ptr::replace(self.pointer as *mut T, src) }
    }

    /// Swaps the values at two mutable locations of the same type.
    #[rapx::verify]
    #[rapx::requires(ValidPtr(self.pointer, T, 1))]
    #[rapx::requires(Align(self.pointer, T))]
    #[rapx::requires(ValidPtr(with.pointer, T, 1))]
    #[rapx::requires(Align(with.pointer, T))]
    pub const unsafe fn swap(self, with: NonNull<T>) {
        // SAFETY: the caller must uphold the safety contract for `swap`.
        unsafe { ptr::swap(self.pointer as *mut T, with.pointer as *mut T) }
    }

    /// Computes the offset that needs to be applied to the pointer in order to make it aligned to `align`.
    #[rapx::verify]
    pub fn align_offset(self, align: usize) -> usize {
        if !align.is_power_of_two() {
            panic!("align_offset: align is not a power-of-two");
        }
        self.pointer.align_offset(align)
    }

    /// Returns whether the pointer is properly aligned for `T`.
    #[rapx::verify]
    pub fn is_aligned(self) -> bool {
        self.pointer.is_aligned()
    }

    /// Returns whether the pointer is aligned to `align`.
    #[rapx::verify]
    pub fn is_aligned_to(self, align: usize) -> bool {
        self.pointer.is_aligned_to(align)
    }
}

impl<T> NonNull<[T]> {
    /// Creates a non-null raw slice from a thin pointer and a length.
    #[rapx::verify]
    pub const fn slice_from_raw_parts(data: NonNull<T>, len: usize) -> Self {
        // SAFETY: `data` is a `NonNull` pointer which is necessarily non-null.
        unsafe {
            NonNull { pointer: slice::from_raw_parts_mut(data.pointer as *mut T, len) as *const [T] }
        }
    }

    /// Performs the same functionality as `ptr::from_raw_parts`.
    #[rapx::verify]
    pub const fn from_raw_parts(data_pointer: NonNull<()>, metadata: usize) -> Self {
        // SAFETY: the data pointer is non-null, so the assembled wide pointer is non-null.
        unsafe {
            NonNull {
                pointer: slice::from_raw_parts_mut(data_pointer.pointer as *mut T, metadata)
                    as *const [T],
            }
        }
    }

    /// Decomposes a (possibly wide) pointer into its data pointer and metadata.
    #[rapx::verify]
    pub const fn to_raw_parts(self) -> (NonNull<()>, usize) {
        (self.cast(), self.len())
    }

    /// Returns the length of a non-null raw slice.
    #[rapx::verify]
    pub const fn len(self) -> usize {
        self.pointer.len()
    }

    /// Returns `true` if the non-null raw slice has a length of 0.
    #[rapx::verify]
    pub const fn is_empty(self) -> bool {
        self.len() == 0
    }

    /// Returns a non-null pointer to the slice's buffer.
    #[rapx::verify]
    pub const fn as_non_null_ptr(self) -> NonNull<T> {
        self.cast()
    }

    /// Returns a raw pointer to the slice's buffer.
    #[rapx::verify]
    pub const fn as_mut_ptr(self) -> *mut T {
        self.pointer as *mut T
    }

    /// Returns a shared reference to a slice of possibly uninitialized values.
    #[rapx::verify]
    #[rapx::requires(ValidPtr(self.pointer, T, 1))]
    #[rapx::requires(Align(self.pointer, T))]
    #[rapx::requires(Alive(self.pointer, 'a))]
    pub const unsafe fn as_uninit_slice<'a>(self) -> &'a [MaybeUninit<T>] {
        // SAFETY: the caller must uphold the safety contract for `as_uninit_slice`.
        unsafe { slice::from_raw_parts(self.pointer as *const MaybeUninit<T>, self.len()) }
    }

    /// Returns a unique reference to a slice of possibly uninitialized values.
    #[rapx::verify]
    #[rapx::requires(ValidPtr(self.pointer, T, 1))]
    #[rapx::requires(Align(self.pointer, T))]
    #[rapx::requires(Alive(self.pointer, 'a))]
    pub const unsafe fn as_uninit_slice_mut<'a>(self) -> &'a mut [MaybeUninit<T>] {
        // SAFETY: the caller must uphold the safety contract for `as_uninit_slice_mut`.
        unsafe { slice::from_raw_parts_mut(self.pointer as *mut MaybeUninit<T>, self.len()) }
    }

    /// Returns a raw pointer to an element or subslice, without bounds checking.
    #[rapx::verify]
    #[rapx::requires(Allocated(self.pointer, T, 1))]
    pub unsafe fn get_unchecked_mut<I>(self, index: I) -> NonNull<I::Output>
    where
        I: slice::SliceIndex<[T]>,
    {
        // SAFETY: the caller ensures that `self` is dereferenceable and `index` in-bounds.
        unsafe {
            NonNull { pointer: (self.pointer as *mut [T]).get_unchecked_mut(index) as *const I::Output }
        }
    }
}

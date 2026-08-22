#![feature(register_tool)]
#![register_tool(rapx)]
#![feature(core_intrinsics)]
#![feature(ascii_char)]
#![feature(portable_simd)]
#![feature(pointer_is_aligned_to)]
#![allow(unsafe_op_in_unsafe_fn)]
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unnecessary_transmutes)]
#![allow(internal_features)]

// Challenge 1: Verify `core` transmuting methods.
// A faithful, self-contained port of the corresponding `core` transmutation methods.

use std::mem::MaybeUninit;
use std::ptr;

/// `transmute<T, U>`: reinterprets `T` as `U`, requiring equal size.
#[rapx::verify]
#[rapx::requires(ValidTransmute(T, U))]
pub unsafe fn transmute_ext<T, U>(src: T) -> U {
    // NOTE: `mem::transmute` enforces the equal-size check statically; for a
    // generic `T, U` we route through the unchecked intrinsic and express the
    // equal-size requirement as the `ValidTransmute` contract above.
    unsafe { std::intrinsics::transmute_unchecked::<T, U>(src) }
}

/// `transmute_unchecked<T, U>`: `transmute` without the static size check.
#[rapx::verify]
#[rapx::requires(ValidTransmute(T, U))]
pub unsafe fn transmute_unchecked_ext<T, U>(src: T) -> U {
    std::intrinsics::transmute_unchecked::<T, U>(src)
}

/// `MaybeUninit<T>::array_assume_init`: `[MaybeUninit<T>; N]` -> `[T; N]`.
#[rapx::verify]
#[rapx::requires(ValidTransmute([MaybeUninit<T>; N], [T; N]))]
pub unsafe fn array_assume_init_ext<T, const N: usize>(array: [MaybeUninit<T>; N]) -> [T; N] {
    // SAFETY: `MaybeUninit<T>` and `T` have the same layout.
    unsafe { std::intrinsics::transmute_unchecked(array) }
}

/// `MaybeUninit<[T; N]>::transpose`: `MaybeUninit<[T; N]>` -> `[MaybeUninit<T>; N]`.
#[rapx::verify]
#[rapx::requires(ValidTransmute(MaybeUninit<[T; N]>, [MaybeUninit<T>; N]))]
pub unsafe fn transpose_ext<T, const N: usize>(self_: MaybeUninit<[T; N]>) -> [MaybeUninit<T>; N] {
    // SAFETY: `T` and `MaybeUninit<T>` have the same layout.
    unsafe { std::intrinsics::transmute_unchecked(self_) }
}

/// `<[MaybeUninit<T>; N]>::transpose`: `[MaybeUninit<T>; N]` -> `MaybeUninit<[T; N]>`.
#[rapx::verify]
#[rapx::requires(ValidTransmute([MaybeUninit<T>; N], MaybeUninit<[T; N]>))]
pub unsafe fn transpose_array_ext<T, const N: usize>(
    self_: [MaybeUninit<T>; N],
) -> MaybeUninit<[T; N]> {
    // SAFETY: `T` and `MaybeUninit<T>` have the same layout.
    unsafe { std::intrinsics::transmute_unchecked(self_) }
}

/// `MaybeUninit<T>::copy_from_slice` transmute: `&[T]` -> `&[MaybeUninit<T>]`.
#[rapx::verify]
#[rapx::requires(ValidTransmute(T, MaybeUninit<T>))]
pub unsafe fn as_maybe_uninit_slice_ext<T>(src: &[T]) -> &[MaybeUninit<T>] {
    // SAFETY: `&[T]` and `&[MaybeUninit<T>]` have the same layout.
    unsafe { std::mem::transmute::<&[T], &[MaybeUninit<T>]>(src) }
}

pub struct Ipv6Addr {
    octets: [u8; 16],
}

impl Ipv6Addr {
    /// `Ipv6Addr::new`: assembles 8 big-endian `u16` segments into 16 bytes.
    #[rapx::verify]
    pub const fn new_ext(
        a: u16,
        b: u16,
        c: u16,
        d: u16,
        e: u16,
        f: u16,
        g: u16,
        h: u16,
    ) -> Ipv6Addr {
        let addr16 = [
            a.to_be(),
            b.to_be(),
            c.to_be(),
            d.to_be(),
            e.to_be(),
            f.to_be(),
            g.to_be(),
            h.to_be(),
        ];
        Ipv6Addr {
            // SAFETY: `[u16; 8]` is always safe to transmute to `[u8; 16]`.
            octets: unsafe { std::mem::transmute::<[u16; 8], [u8; 16]>(addr16) },
        }
    }

    /// `Ipv6Addr::segments`: splits the 16 bytes into 8 native-endian `u16`s.
    #[rapx::verify]
    pub const fn segments_ext(&self) -> [u16; 8] {
        // SAFETY: `[u8; 16]` is always safe to transmute to `[u16; 8]`.
        let [a, b, c, d, e, f, g, h] = unsafe {
            std::mem::transmute::<[u8; 16], [u16; 8]>(self.octets)
        };
        [
            u16::from_be(a),
            u16::from_be(b),
            u16::from_be(c),
            u16::from_be(d),
            u16::from_be(e),
            u16::from_be(f),
            u16::from_be(g),
            u16::from_be(h),
        ]
    }
}

/// `char::from_u32_unchecked`: `u32` -> `char`, caller guarantees valid scalar.
#[rapx::verify]
#[rapx::requires(ValidTransmute(u32, char))]
pub const unsafe fn from_u32_unchecked_ext(i: u32) -> char {
    // SAFETY: the caller must guarantee that `i` is a valid char value.
    unsafe { std::mem::transmute(i) }
}

/// `char_try_from_u32`: `u32` -> `Result<char, ()>`, checked conversion.
#[rapx::verify]
pub const fn char_try_from_u32_ext(i: u32) -> Result<char, ()> {
    // Optimized surrogate/out-of-range check (see `char::convert`).
    if (i ^ 0xD800).wrapping_sub(0x800) >= 0x110000 - 0x800 {
        Err(())
    } else {
        // SAFETY: checked that it's a legal unicode value.
        Ok(unsafe { std::mem::transmute(i) })
    }
}

/// `char::as_ascii`: `char` -> `Option<ascii::Char>` via `AsciiChar::from_u8_unchecked`.
#[rapx::verify]
pub const fn char_as_ascii_ext(self_: &char) -> Option<std::ascii::Char> {
    if self_.is_ascii() {
        // SAFETY: just checked that this is ASCII.
        Some(unsafe { ascii_char_from_u8_unchecked_ext(*self_ as u8) })
    } else {
        None
    }
}

/// `char::encode_utf16_raw`: encodes a code point into a caller-provided buffer.
#[rapx::verify]
pub const fn encode_utf16_raw_ext(mut code: u32, dst: &mut [u16]) -> &mut [u16] {
    let len = len_utf16_ext(code);
    match (len, &mut *dst) {
        (1, [a, ..]) => {
            *a = code as u16;
        }
        (2, [a, b, ..]) => {
            code -= 0x1_0000;
            *a = (code >> 10) as u16 | 0xD800;
            *b = (code & 0x3FF) as u16 | 0xDC00;
        }
        _ => {
            panic!("encode_utf16: buffer does not have enough bytes");
        }
    };
    // SAFETY: `len` has been tested to be within bounds.
    unsafe { std::slice::from_raw_parts_mut(dst.as_mut_ptr(), len) }
}

const fn len_utf16_ext(code: u32) -> usize {
    if (code & 0xFFFF) == code { 1 } else { 2 }
}

/// `AsciiChar::from_u8_unchecked`: `u8` -> `ascii::Char`, caller guarantees <= 0x7F.
#[rapx::verify]
#[rapx::requires(ValidTransmute(u8, std::ascii::Char))]
pub const unsafe fn ascii_char_from_u8_unchecked_ext(b: u8) -> std::ascii::Char {
    // SAFETY: our safety precondition is that `b` is in-range.
    unsafe { std::mem::transmute(b) }
}

/// `AsciiChar::from_u8`: checked `u8` -> `Option<ascii::Char>`.
#[rapx::verify]
pub const fn ascii_char_from_u8_ext(b: u8) -> Option<std::ascii::Char> {
    if b <= 127 {
        // SAFETY: just checked that `b` is in-range.
        Some(unsafe { ascii_char_from_u8_unchecked_ext(b) })
    } else {
        None
    }
}

/// `str::as_bytes`: `&str` -> `&[u8]` (same layout, fat-pointer transmute).
#[rapx::verify]
pub const fn str_as_bytes_ext(s: &str) -> &[u8] {
    // SAFETY: const sound because we transmute two types with the same layout.
    unsafe { std::mem::transmute::<&str, &[u8]>(s) }
}

/// `str::as_bytes_mut`: `&mut str` -> `&mut [u8]` via raw-pointer cast.
#[rapx::verify]
pub const unsafe fn str_as_bytes_mut_ext(s: &mut str) -> &mut [u8] {
    // SAFETY: `str` has the same layout as `[u8]`; the pointer comes from a mutable reference.
    unsafe { &mut *(s as *mut str as *mut [u8]) }
}

/// `str::make_ascii_uppercase`: safe wrapper over `as_bytes_mut`.
#[rapx::verify]
pub const fn str_make_ascii_uppercase_ext(s: &mut str) {
    // SAFETY: changing ASCII letters only does not invalidate UTF-8.
    let me = unsafe { str_as_bytes_mut_ext(s) };
    bytes_make_ascii_uppercase_ext(me)
}

/// `str::make_ascii_lowercase`: safe wrapper over `as_bytes_mut`.
#[rapx::verify]
pub const fn str_make_ascii_lowercase_ext(s: &mut str) {
    // SAFETY: changing ASCII letters only does not invalidate UTF-8.
    let me = unsafe { str_as_bytes_mut_ext(s) };
    bytes_make_ascii_lowercase_ext(me)
}

const fn bytes_make_ascii_uppercase_ext(bytes: &mut [u8]) {
    let mut i = 0;
    while i < bytes.len() {
        let byte = &mut bytes[i];
        *byte = byte.to_ascii_uppercase();
        i += 1;
    }
}

const fn bytes_make_ascii_lowercase_ext(bytes: &mut [u8]) {
    let mut i = 0;
    while i < bytes.len() {
        let byte = &mut bytes[i];
        *byte = byte.to_ascii_lowercase();
        i += 1;
    }
}

/// Newtype over `usize` mirroring `core::ptr::alignment::Alignment`.
#[derive(Copy, Clone)]
pub struct Alignment(usize);

impl Alignment {
    pub const fn as_usize(self) -> usize {
        self.0
    }

    /// `Alignment::new_unchecked`: `usize` -> `Alignment` via transmute.
    #[rapx::verify]
    #[rapx::requires(ValidNum(align > 0))]
    #[rapx::requires(ValidNum((align & (align - 1)) == 0))]
    pub const unsafe fn new_unchecked_ext(align: usize) -> Alignment {
        // SAFETY: by precondition, `align` is a power of two, hence a valid `Alignment`.
        unsafe { std::mem::transmute::<usize, Alignment>(align) }
    }

    /// `Alignment::new`: checked constructor.
    #[rapx::verify]
    pub const fn new_ext(align: usize) -> Option<Alignment> {
        if align > 0 && (align & (align - 1)) == 0 {
            // SAFETY: just checked that only one bit is set.
            Some(unsafe { Self::new_unchecked_ext(align) })
        } else {
            None
        }
    }
}

pub struct Layout {
    size: usize,
    align: Alignment,
}

impl Layout {
    /// `Layout::from_size_align`: checked constructor using a transmute of `align`.
    #[rapx::verify]
    pub const fn from_size_align_ext(size: usize, align: usize) -> Result<Layout, ()> {
        if align > 0 && (align & (align - 1)) == 0 && size <= usize::MAX - (align - 1) {
            // SAFETY: `align` is a power of two and the size fits.
            unsafe { Ok(Layout { size, align: Alignment::new_unchecked_ext(align) }) }
        } else {
            Err(())
        }
    }

    /// `Layout::from_size_align_unchecked`: unchecked constructor via transmute.
    #[rapx::verify]
    #[rapx::requires(ValidNum(align > 0))]
    #[rapx::requires(ValidNum((align & (align - 1)) == 0))]
    pub const unsafe fn from_size_align_unchecked_ext(size: usize, align: usize) -> Layout {
        // SAFETY: caller guarantees the preconditions on `align`.
        unsafe { Layout { size, align: std::mem::transmute::<usize, Alignment>(align) } }
    }
}

/// `*const T::align_offset`: forwards to the checked std method.
#[rapx::verify]
pub fn align_offset_ext<T>(p: *const T, a: usize) -> usize
where
    T: Sized,
{
    if !a.is_power_of_two() {
        panic!("align_offset: align is not a power-of-two");
    }
    p.align_offset(a)
}

/// `*const T::is_aligned_to`: `p.addr() & (align - 1) == 0`.
#[rapx::verify]
pub fn const_is_aligned_to_ext<T>(p: *const T, align: usize) -> bool {
    if !align.is_power_of_two() {
        panic!("is_aligned_to: align is not a power-of-two");
    }
    p.addr() & (align - 1) == 0
}

/// `*mut T::is_aligned_to`.
#[rapx::verify]
pub fn mut_is_aligned_to_ext<T>(p: *mut T, align: usize) -> bool {
    if !align.is_power_of_two() {
        panic!("is_aligned_to: align is not a power-of-two");
    }
    p.addr() & (align - 1) == 0
}

/// `<[T]>::align_to`: split a slice into (prefix, aligned U-slice, suffix).
#[rapx::verify]
#[rapx::requires(SplitTransmute([T], [U]))]
pub unsafe fn align_to_ext<T, U>(slice: &[T]) -> (&[T], &[U], &[T]) {
    if std::mem::size_of::<T>() == 0 || std::mem::size_of::<U>() == 0 {
        return (slice, &[], &[]);
    }

    let ptr = slice.as_ptr();
    // SAFETY: `align_of::<U>()` is a power of two.
    let offset = ptr.align_offset(std::mem::align_of::<U>());

    if offset > slice.len() {
        return (slice, &[], &[]);
    }

    let (left, rest) = slice.split_at(offset);

    let byte_len = rest.len() * std::mem::size_of::<T>();
    let new_len = byte_len / std::mem::size_of::<U>();

    let mid = std::slice::from_raw_parts(rest.as_ptr() as *const U, new_len);
    let tail_start = rest.len() - (byte_len % std::mem::size_of::<U>()) / std::mem::size_of::<T>();

    let tail = std::slice::from_raw_parts(rest.as_ptr().add(tail_start), rest.len() - tail_start);

    (left, mid, tail)
}

/// `<[T]>::align_to_mut`: mutable counterpart of `align_to`.
#[rapx::verify]
#[rapx::requires(SplitTransmute([T], [U]))]
pub unsafe fn align_to_mut_ext<T, U>(slice: &mut [T]) -> (&mut [T], &mut [U], &mut [T]) {
    if std::mem::size_of::<T>() == 0 || std::mem::size_of::<U>() == 0 {
        return (slice, &mut [], &mut []);
    }

    let ptr = slice.as_mut_ptr();
    // SAFETY: `align_of::<U>()` is a power of two.
    let offset = ptr.align_offset(std::mem::align_of::<U>());

    if offset > slice.len() {
        return (slice, &mut [], &mut []);
    }

    let (left, rest) = slice.split_at_mut(offset);

    let byte_len = rest.len() * std::mem::size_of::<T>();
    let new_len = byte_len / std::mem::size_of::<U>();

    let mid = std::slice::from_raw_parts_mut(rest.as_mut_ptr() as *mut U, new_len);
    let tail_start = rest.len() - (byte_len % std::mem::size_of::<U>()) / std::mem::size_of::<T>();

    let tail = std::slice::from_raw_parts_mut(
        rest.as_mut_ptr().add(tail_start),
        rest.len() - tail_start,
    );

    (left, mid, tail)
}

/// `<[T]>::as_simd`: view a slice as SIMD lanes via `align_to`.
#[cfg(not(rapx_rustc_ge_196))]
#[rapx::verify]
pub fn as_simd_ext<T, const LANES: usize>(
    slice: &[T],
) -> (&[T], &[std::simd::Simd<T, LANES>], &[T])
where
    T: std::simd::SimdElement,
    std::simd::LaneCount<LANES>: std::simd::SupportedLaneCount,
    std::simd::Simd<T, LANES>: AsRef<[T; LANES]>,
{
    assert!(LANES != 0, "SIMD lane count must be non-zero");
    // SAFETY: the SIMD type has the same layout as `[T; LANES]`.
    unsafe { align_to_ext::<T, std::simd::Simd<T, LANES>>(slice) }
}

/// `<[T]>::as_simd`: view a slice as SIMD lanes via `align_to`.
#[cfg(rapx_rustc_ge_196)]
#[rapx::verify]
pub fn as_simd_ext<T, const LANES: usize>(
    slice: &[T],
) -> (&[T], &[std::simd::Simd<T, LANES>], &[T])
where
    T: std::simd::SimdElement,
    std::simd::Simd<T, LANES>: AsRef<[T; LANES]>,
{
    assert!(LANES != 0, "SIMD lane count must be non-zero");
    // SAFETY: the SIMD type has the same layout as `[T; LANES]`.
    unsafe { align_to_ext::<T, std::simd::Simd<T, LANES>>(slice) }
}

/// `<[T]>::as_simd_mut`: mutable counterpart of `as_simd`.
#[cfg(not(rapx_rustc_ge_196))]
#[rapx::verify]
pub fn as_simd_mut_ext<T, const LANES: usize>(
    slice: &mut [T],
) -> (&mut [T], &mut [std::simd::Simd<T, LANES>], &mut [T])
where
    T: std::simd::SimdElement,
    std::simd::LaneCount<LANES>: std::simd::SupportedLaneCount,
    std::simd::Simd<T, LANES>: AsMut<[T; LANES]>,
{
    assert!(LANES != 0, "SIMD lane count must be non-zero");
    // SAFETY: the SIMD type has the same layout as `[T; LANES]`.
    unsafe { align_to_mut_ext::<T, std::simd::Simd<T, LANES>>(slice) }
}

/// `<[T]>::as_simd_mut`: mutable counterpart of `as_simd`.
#[cfg(rapx_rustc_ge_196)]
#[rapx::verify]
pub fn as_simd_mut_ext<T, const LANES: usize>(
    slice: &mut [T],
) -> (&mut [T], &mut [std::simd::Simd<T, LANES>], &mut [T])
where
    T: std::simd::SimdElement,
    std::simd::Simd<T, LANES>: AsMut<[T; LANES]>,
{
    assert!(LANES != 0, "SIMD lane count must be non-zero");
    // SAFETY: the SIMD type has the same layout as `[T; LANES]`.
    unsafe { align_to_mut_ext::<T, std::simd::Simd<T, LANES>>(slice) }
}

const LO_USIZE_EXT: usize = 0x0101_0101_0101_0101;
const HI_USIZE_EXT: usize = 0x8080_8080_8080_8080;

const fn repeat_u8_ext(b: u8) -> usize {
    (b as usize) * LO_USIZE_EXT
}

const fn contains_zero_byte_ext(x: usize) -> bool {
    x.wrapping_sub(LO_USIZE_EXT) & !x & HI_USIZE_EXT != 0
}

/// `memchr_aligned`: find a byte using word-at-a-time scans.
#[rapx::verify]
#[rapx::requires(ValidNum(text.len() >= 2 * std::mem::size_of::<usize>()))]
pub fn memchr_aligned_ext(x: u8, text: &[u8]) -> Option<usize> {
    let len = text.len();
    let ptr = text.as_ptr();
    let mut offset = ptr.align_offset(std::mem::size_of::<usize>());

    if offset > 0 {
        offset = offset.min(len);
        let slice = &text[..offset];
        if let Some(index) = memchr_naive_ext(x, slice) {
            return Some(index);
        }
    }

    let repeated_x = repeat_u8_ext(x);
    while offset <= len - 2 * std::mem::size_of::<usize>() {
        // SAFETY: the loop predicate guarantees at least 2 words remain.
        unsafe {
            let u = *(ptr.add(offset) as *const usize);
            let v = *(ptr.add(offset + std::mem::size_of::<usize>()) as *const usize);
            let zu = contains_zero_byte_ext(u ^ repeated_x);
            let zv = contains_zero_byte_ext(v ^ repeated_x);
            if zu || zv {
                break;
            }
        }
        offset += 2 * std::mem::size_of::<usize>();
    }

    // SAFETY: offset is within bounds.
    let slice = unsafe { std::slice::from_raw_parts(text.as_ptr().add(offset), text.len() - offset) };
    memchr_naive_ext(x, slice).map(|i| offset + i)
}

fn memchr_naive_ext(x: u8, text: &[u8]) -> Option<usize> {
    text.iter().position(|&b| b == x)
}

/// `memrchr`: find the last byte matching `x` using an `align_to` split.
#[rapx::verify]
pub fn memrchr_ext(x: u8, text: &[u8]) -> Option<usize> {
    let len = text.len();
    let ptr = text.as_ptr();
    type Chunk = usize;

    let (min_aligned_offset, max_aligned_offset) = {
        // SAFETY: transmuting `[u8]` to `[usize]` is safe except for size differences handled by `align_to`.
        let (prefix, _, suffix) = unsafe { align_to_ext::<u8, (Chunk, Chunk)>(text) };
        (prefix.len(), len - suffix.len())
    };

    let mut offset = max_aligned_offset;
    if let Some(index) = text[offset..].iter().rposition(|elt| *elt == x) {
        return Some(offset + index);
    }

    let repeated_x = repeat_u8_ext(x);
    let chunk_bytes = std::mem::size_of::<Chunk>();

    while offset > min_aligned_offset {
        // SAFETY: offset stays above min_aligned_offset, leaving >= 2 chunks.
        unsafe {
            let u = *(ptr.add(offset - 2 * chunk_bytes) as *const Chunk);
            let v = *(ptr.add(offset - chunk_bytes) as *const Chunk);
            let zu = contains_zero_byte_ext(u ^ repeated_x);
            let zv = contains_zero_byte_ext(v ^ repeated_x);
            if zu || zv {
                break;
            }
        }
        offset -= 2 * chunk_bytes;
    }

    text[..offset].iter().rposition(|elt| *elt == x)
}

/// `<[T; N] as IntoIterator>::into_iter`: `[T; N]` -> `[MaybeUninit<T>; N]`.
#[rapx::verify]
#[rapx::requires(ValidTransmute([T; N], [MaybeUninit<T>; N]))]
pub unsafe fn array_into_iter_transmute_ext<T, const N: usize>(
    arr: [T; N],
) -> [MaybeUninit<T>; N] {
    // SAFETY: `MaybeUninit<T>` has the same size and alignment as `T`.
    unsafe { std::intrinsics::transmute_unchecked(arr) }
}

/// `array::try_from_fn`: build an array from a fallible closure.
#[rapx::verify]
pub fn array_try_from_fn_ext<T, E, const N: usize, F>(mut cb: F) -> Result<[T; N], E>
where
    F: FnMut(usize) -> Result<T, E>,
{
    let mut array = [const { MaybeUninit::uninit() }; N];
    let mut i = 0;
    while i < N {
        match cb(i) {
            Ok(v) => {
                array[i].write(v);
            }
            Err(e) => {
                // SAFETY: only the first `i` elements are initialized.
                for elem in &mut array[..i] {
                    unsafe { elem.assume_init_drop() };
                }
                return Err(e);
            }
        }
        i += 1;
    }
    // SAFETY: all elements of the array were populated.
    Ok(unsafe { array_assume_init_ext(array) })
}

/// `array::iter_next_chunk`: pull `N` items from an iterator into an array.
#[rapx::verify]
pub fn iter_next_chunk_ext<T, const N: usize>(
    iter: &mut impl Iterator<Item = T>,
) -> Result<[T; N], Vec<T>> {
    let mut array = [const { MaybeUninit::uninit() }; N];
    let mut initialized = 0;
    while initialized < N {
        match iter.next() {
            Some(item) => {
                array[initialized].write(item);
                initialized += 1;
            }
            None => {
                // SAFETY: only the first `initialized` elements are initialized.
                let mut remaining = Vec::with_capacity(initialized);
                for elem in &mut array[..initialized] {
                    unsafe {
                        remaining.push(elem.assume_init_read());
                    }
                }
                return Err(remaining);
            }
        }
    }
    // SAFETY: all elements of `array` were populated.
    Ok(unsafe { array_assume_init_ext(array) })
}

/// `<Filter<I, P> as Iterator>::next_chunk` (dropless path).
#[rapx::verify]
pub fn filter_next_chunk_ext<I, P, const N: usize>(
    iter: I,
    mut predicate: P,
) -> Result<[I::Item; N], Vec<I::Item>>
where
    I: Iterator,
    P: FnMut(&I::Item) -> bool,
{
    let mut array: [MaybeUninit<I::Item>; N] = [const { MaybeUninit::uninit() }; N];
    let mut initialized = 0;

    for element in iter {
        let idx = initialized;
        let keep = predicate(&element);
        if keep {
            // SAFETY: loop conditions ensure the index is in bounds.
            unsafe { array.get_unchecked_mut(idx) }.write(element);
        }
        initialized += keep as usize;

        if initialized >= N {
            // SAFETY: the loop breaks only once the array is fully initialized.
            return Ok(unsafe { array_assume_init_ext(array) });
        }
    }

    // SAFETY: only the first `initialized` elements were populated.
    let mut remaining = Vec::with_capacity(initialized);
    for elem in &mut array[..initialized] {
        unsafe {
            remaining.push(elem.assume_init_read());
        }
    }
    Err(remaining)
}

/// `<FilterMap<I, F> as Iterator>::next_chunk`.
#[rapx::verify]
pub fn filter_map_next_chunk_ext<I, F, B, const N: usize>(
    iter: I,
    mut f: F,
) -> Result<[B; N], Vec<B>>
where
    I: Iterator,
    F: FnMut(I::Item) -> Option<B>,
{
    let mut array: [MaybeUninit<B>; N] = [const { MaybeUninit::uninit() }; N];
    let mut initialized = 0;

    for element in iter {
        let idx = initialized;
        match f(element) {
            Some(val) => {
                initialized += 1;
                // SAFETY: loop conditions ensure the index is in bounds.
                unsafe { array.get_unchecked_mut(idx) }.write(val);
            }
            None => {}
        }
        if initialized >= N {
            // SAFETY: the loop breaks only once the array is fully initialized.
            return Ok(unsafe { array_assume_init_ext(array) });
        }
    }

    // SAFETY: only the first `initialized` elements were populated.
    let mut remaining = Vec::with_capacity(initialized);
    for elem in &mut array[..initialized] {
        unsafe {
            remaining.push(elem.assume_init_read());
        }
    }
    Err(remaining)
}

/// `<char as Step>::forward_checked`.
#[rapx::verify]
pub fn char_forward_checked_ext(start: char, count: usize) -> Option<char> {
    let start = start as u32;
    let mut res = start.checked_add(count as u32)?;
    if start < 0xD800 && 0xD800 <= res {
        res = res.checked_add(0x800)?;
    }
    if res <= char::MAX as u32 {
        // SAFETY: `res` is a valid unicode scalar.
        Some(unsafe { from_u32_unchecked_ext(res) })
    } else {
        None
    }
}

/// `<char as Step>::forward_unchecked`.
#[rapx::verify]
#[rapx::requires(ValidNum((start as u32) < 0xD800 || (start as u32).checked_add(count as u32).is_some()))]
pub unsafe fn char_forward_unchecked_ext(start: char, count: usize) -> char {
    let start_u = start as u32;
    // SAFETY: the caller guarantees this does not overflow the char range.
    let mut res = unsafe { start_u.unchecked_add(count as u32) };
    if start_u < 0xD800 && 0xD800 <= res {
        // SAFETY: the caller guarantees this does not overflow.
        res = unsafe { res.unchecked_add(0x800) };
    }
    // SAFETY: the caller guarantees `res` is a valid char.
    unsafe { from_u32_unchecked_ext(res) }
}

/// `<char as Step>::backward_unchecked`.
#[rapx::verify]
#[rapx::requires(ValidNum((start as u32) >= 0xE000 || (start as u32).checked_sub(count as u32).is_some()))]
pub unsafe fn char_backward_unchecked_ext(start: char, count: usize) -> char {
    let start_u = start as u32;
    // SAFETY: the caller guarantees this does not underflow the char range.
    let mut res = unsafe { start_u.unchecked_sub(count as u32) };
    if start_u >= 0xE000 && 0xE000 > res {
        // SAFETY: the caller guarantees this does not underflow.
        res = unsafe { res.unchecked_sub(0x800) };
    }
    // SAFETY: the caller guarantees `res` is a valid char.
    unsafe { from_u32_unchecked_ext(res) }
}

/// `<Chars as Iterator>::next`: decode the next UTF-8 code point.
#[rapx::verify]
pub fn chars_next_ext(iter: &mut std::str::Chars) -> Option<char> {
    // SAFETY: the `str` invariant guarantees a valid UTF-8 string.
    unsafe {
        next_code_point_ext(&mut iter.as_str().as_bytes().iter().cloned())
            .map(|ch| from_u32_unchecked_ext(ch))
    }
}

/// `<Chars as DoubleEndedIterator>::next_back`: decode the previous code point.
#[rapx::verify]
pub fn chars_next_back_ext(iter: &mut std::str::Chars) -> Option<char> {
    // SAFETY: the `str` invariant guarantees a valid UTF-8 string.
    let bytes: Vec<u8> = iter.as_str().as_bytes().to_vec();
    let mut rev = bytes.iter().cloned().rev();
    unsafe {
        next_code_point_reverse_ext(&mut rev).map(|ch| from_u32_unchecked_ext(ch))
    }
}

const CONT_MASK_EXT: u8 = 0b0011_1111;

const fn utf8_first_byte_ext(byte: u8, width: u32) -> u32 {
    (byte & (0x7F >> width)) as u32
}

const fn utf8_acc_cont_byte_ext(ch: u32, byte: u8) -> u32 {
    (ch << 6) | (byte & CONT_MASK_EXT) as u32
}

const fn utf8_is_cont_byte_ext(byte: u8) -> bool {
    (byte as i8) < -64
}

unsafe fn next_code_point_ext<I: Iterator<Item = u8>>(bytes: &mut I) -> Option<u32> {
    let x = bytes.next()?;
    if x < 128 {
        return Some(x as u32);
    }
    let init = utf8_first_byte_ext(x, 2);
    // SAFETY: `bytes` produces a UTF-8-like string.
    let y = unsafe { bytes.next().unwrap_unchecked() };
    let mut ch = utf8_acc_cont_byte_ext(init, y);
    if x >= 0xE0 {
        // SAFETY: `bytes` produces a UTF-8-like string.
        let z = unsafe { bytes.next().unwrap_unchecked() };
        let y_z = utf8_acc_cont_byte_ext((y & CONT_MASK_EXT) as u32, z);
        ch = init << 12 | y_z;
        if x >= 0xF0 {
            // SAFETY: `bytes` produces a UTF-8-like string.
            let w = unsafe { bytes.next().unwrap_unchecked() };
            ch = (init & 7) << 18 | utf8_acc_cont_byte_ext(y_z, w);
        }
    }
    Some(ch)
}

unsafe fn next_code_point_reverse_ext<I>(bytes: &mut I) -> Option<u32>
where
    I: DoubleEndedIterator<Item = u8>,
{
    let w = match bytes.next_back()? {
        next_byte if next_byte < 128 => return Some(next_byte as u32),
        back_byte => back_byte,
    };
    // SAFETY: `bytes` produces a UTF-8-like string.
    let z = unsafe { bytes.next_back().unwrap_unchecked() };
    let mut ch = utf8_first_byte_ext(z, 2);
    if utf8_is_cont_byte_ext(z) {
        // SAFETY: `bytes` produces a UTF-8-like string.
        let y = unsafe { bytes.next_back().unwrap_unchecked() };
        ch = utf8_first_byte_ext(y, 3);
        if utf8_is_cont_byte_ext(y) {
            // SAFETY: `bytes` produces a UTF-8-like string.
            let x = unsafe { bytes.next_back().unwrap_unchecked() };
            ch = utf8_first_byte_ext(x, 4);
            ch = utf8_acc_cont_byte_ext(ch, y);
        }
        ch = utf8_acc_cont_byte_ext(ch, z);
    }
    ch = utf8_acc_cont_byte_ext(ch, w);
    Some(ch)
}

/// `str::count::do_count_chars`: count characters using `align_to::<usize>`.
#[rapx::verify]
pub fn do_count_chars_ext(s: &str) -> usize {
    const CHUNK_SIZE: usize = 192;
    const UNROLL_INNER: usize = 4;

    // SAFETY: transmuting `[u8]` to `[usize]` is safe except for size differences handled by `align_to`.
    let (head, body, tail) = unsafe { align_to_ext::<u8, usize>(s.as_bytes()) };

    if body.is_empty() || head.len() > std::mem::size_of::<usize>() || tail.len() > std::mem::size_of::<usize>() {
        return char_count_general_case_ext(s.as_bytes());
    }

    let mut total = char_count_general_case_ext(head) + char_count_general_case_ext(tail);
    for chunk in body.chunks(CHUNK_SIZE) {
        let mut counts = 0;
        for &word in chunk {
            counts += contains_non_continuation_byte_ext(word);
        }
        total += sum_bytes_in_usize_ext(counts);
        let _ = UNROLL_INNER;
    }
    total
}

fn contains_non_continuation_byte_ext(w: usize) -> usize {
    ((!w >> 7) | (w >> 6)) & LO_USIZE_EXT
}

fn sum_bytes_in_usize_ext(values: usize) -> usize {
    let pair_sum = (values & 0x00ff_00ff_00ff_00ff) + ((values >> 8) & 0x00ff_00ff_00ff_00ff);
    pair_sum.wrapping_mul(LO_USIZE_EXT) >> 56
}

fn char_count_general_case_ext(s: &[u8]) -> usize {
    s.iter().filter(|&&byte| !utf8_is_cont_byte_ext(byte)).count()
}

pub struct BorrowedBuf<'data> {
    pub buf: &'data mut [u8],
    pub filled: usize,
}

pub struct BorrowedCursor<'a> {
    pub buf: &'a mut BorrowedBuf<'a>,
}

impl<'data> BorrowedBuf<'data> {
    /// `BorrowedBuf::unfilled`: covariance-casting lifetime transmute.
    #[rapx::verify]
    pub fn unfilled_ext<'this>(&'this mut self) -> BorrowedCursor<'this> {
        BorrowedCursor {
            // SAFETY: we never assign into `BorrowedCursor::buf`, so treating its lifetime covariantly is safe.
            buf: unsafe {
                std::mem::transmute::<&'this mut BorrowedBuf<'data>, &'this mut BorrowedBuf<'this>>(
                    self,
                )
            },
        }
    }
}

impl<'a> BorrowedCursor<'a> {
    /// `BorrowedCursor::reborrow`: covariance-casting lifetime transmute.
    #[rapx::verify]
    pub fn reborrow_ext<'this>(&'this mut self) -> BorrowedCursor<'this> {
        BorrowedCursor {
            // SAFETY: we never assign into `BorrowedCursor::buf`, so treating its lifetime covariantly is safe.
            buf: unsafe {
                std::mem::transmute::<&'this mut BorrowedBuf<'a>, &'this mut BorrowedBuf<'this>>(
                    self.buf,
                )
            },
        }
    }
}

#![feature(register_tool)]
#![register_tool(rapx)]
#![feature(allocator_api)]
#![allow(unsafe_op_in_unsafe_fn)]
#![allow(dead_code)]
#![allow(unused_mut)]

// Challenge 10: Memory safety of `String` — a faithful, self-contained port of
// `library/alloc/src/string.rs`. `char` is modelled as a `u32` code point and
// UTF-8 validity is assumed as a trust invariant, exactly as the challenge permits.

use std::alloc::{Allocator, Global, Layout};
use std::mem::ManuallyDrop;
use std::ops::Range;
use std::ptr::{self, NonNull};
use std::slice::{from_raw_parts, from_raw_parts_mut};

/// Error returned by `String::from_utf16*` on invalid input.
#[derive(Clone, Copy, Debug)]
pub struct FromUtf16Error(());

fn capacity_overflow() -> ! {
    panic!("capacity overflow");
}

/// Number of bytes `code` takes up when encoded in UTF-8 (1..=4).
fn char_len_utf8(code: u32) -> usize {
    if code < 0x80 {
        1
    } else if code < 0x800 {
        2
    } else if code < 0x10000 {
        3
    } else {
        4
    }
}

/// Encode `code` into `dst` (at least 4 writable bytes) and return the number of bytes written.
unsafe fn encode_char(code: u32, dst: *mut u8) -> usize {
    if code < 0x80 {
        unsafe { *dst = code as u8 };
        1
    } else if code < 0x800 {
        unsafe {
            *dst = (0xC0 | (code >> 6)) as u8;
            *dst.add(1) = (0x80 | (code & 0x3F)) as u8;
        }
        2
    } else if code < 0x10000 {
        unsafe {
            *dst = (0xE0 | (code >> 12)) as u8;
            *dst.add(1) = (0x80 | ((code >> 6) & 0x3F)) as u8;
            *dst.add(2) = (0x80 | (code & 0x3F)) as u8;
        }
        3
    } else {
        unsafe {
            *dst = (0xF0 | (code >> 18)) as u8;
            *dst.add(1) = (0x80 | ((code >> 12) & 0x3F)) as u8;
            *dst.add(2) = (0x80 | ((code >> 6) & 0x3F)) as u8;
            *dst.add(3) = (0x80 | (code & 0x3F)) as u8;
        }
        4
    }
}

/// Decode the first UTF-8 code point of `slice`, returning `(code_point, len)`; `Some` guarantees `len <= slice.len()`.
fn decode_first_char(slice: &[u8]) -> Option<(u32, usize)> {
    let lead = *slice.first()?;
    if lead < 0x80 {
        return Some((lead as u32, 1));
    }
    let y = *slice.get(1)?;
    let mut code = ((lead as u32) & 0x1F) << 6 | ((y as u32) & 0x3F);
    if lead < 0xE0 {
        return Some((code, 2));
    }
    let z = *slice.get(2)?;
    code = ((lead as u32) & 0x0F) << 12 | ((y as u32) & 0x3F) << 6 | ((z as u32) & 0x3F);
    if lead < 0xF0 {
        return Some((code, 3));
    }
    let w = *slice.get(3)?;
    code = ((lead as u32) & 0x07) << 18
        | ((y as u32) & 0x3F) << 12
        | ((z as u32) & 0x3F) << 6
        | ((w as u32) & 0x3F);
    Some((code, 4))
}

/// Decode the last UTF-8 code point of `slice`, returning `(code_point, len)`; `Some` guarantees `len <= slice.len()`.
fn decode_last_char(slice: &[u8]) -> Option<(u32, usize)> {
    let n = slice.len();
    let last = *slice.get(n.wrapping_sub(1))?;
    if last < 0x80 {
        return Some((last as u32, 1));
    }
    let mut lead_idx = n - 1;
    while lead_idx > 0 && (slice[lead_idx - 1] & 0xC0) == 0x80 {
        lead_idx -= 1;
    }
    let len = n - lead_idx;
    let lead = slice[lead_idx];
    let mut code = (lead as u32) & match len {
        2 => 0x1F,
        3 => 0x0F,
        _ => 0x07,
    };
    let mut i = lead_idx + 1;
    while i < n {
        code = (code << 6) | ((slice[i] as u32) & 0x3F);
        i += 1;
    }
    Some((code, len))
}

/// Memory-safety-relevant part of `is_char_boundary`: `idx <= len` (UTF-8 boundary is assumed).
fn is_char_boundary(len: usize, idx: usize) -> bool {
    idx <= len
}

/// A byte buffer (`Vec<u8>`): a non-null pointer, a length, and a capacity.
#[rapx::invariant(Allocated(ptr, u8, cap))]
#[rapx::invariant(ValidNum(len <= cap))]
#[rapx::invariant(ValidNum(cap <= isize::MAX))]
pub struct Vec {
    ptr: NonNull<u8>,
    len: usize,
    cap: usize,
}

impl Vec {
    pub fn new() -> Vec {
        Vec { ptr: NonNull::dangling(), len: 0, cap: 0 }
    }

    pub fn with_capacity(capacity: usize) -> Vec {
        let mut vec = Vec::new();
        if capacity > 0 {
            vec.reserve(capacity);
        }
        vec
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn capacity(&self) -> usize {
        self.cap
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn as_ptr(&self) -> *const u8 {
        self.ptr.as_ptr()
    }

    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        self.ptr.as_ptr()
    }

    pub fn as_slice(&self) -> &[u8] {
        // SAFETY: `self.ptr` is allocated for `cap >= len` bytes and `len`
        // elements are initialized by the String invariant.
        unsafe { from_raw_parts(self.ptr.as_ptr(), self.len) }
    }

    /// Ensures capacity for `additional` more bytes.
    pub fn reserve(&mut self, additional: usize) {
        let required = self.len.checked_add(additional).unwrap_or_else(|| capacity_overflow());
        if required > self.cap {
            unsafe { self.grow(required) };
        }
    }

    /// Grow the buffer to at least `required` bytes (amortized doubling).
    unsafe fn grow(&mut self, required: usize) {
        let mut new_cap = if self.cap == 0 { 8 } else { self.cap * 2 };
        if new_cap < required {
            new_cap = required;
        }
        let new_layout = Layout::array::<u8>(new_cap).unwrap_or_else(|_| capacity_overflow());
        let new_ptr = if self.cap == 0 {
            match Global.allocate(new_layout) {
                Ok(ptr) => ptr,
                Err(_) => std::alloc::handle_alloc_error(new_layout),
            }
        } else {
            let old_layout = Layout::array::<u8>(self.cap).unwrap_or_else(|_| capacity_overflow());
            // SAFETY: `self.ptr` is the buffer of the current `cap`.
            match unsafe { Global.grow(self.ptr, old_layout, new_layout) } {
                Ok(ptr) => ptr,
                Err(_) => std::alloc::handle_alloc_error(new_layout),
            }
        };
        self.ptr = new_ptr.cast();
        self.cap = new_cap;
    }

    /// Shrink the allocation down to `self.len` bytes.
    unsafe fn shrink_to_fit(&mut self) {
        if self.len == 0 {
            if self.cap != 0 {
                let old_layout = Layout::array::<u8>(self.cap).unwrap();
                // SAFETY: `self.ptr` was allocated with `old_layout`.
                unsafe { Global.deallocate(self.ptr, old_layout) };
                self.ptr = NonNull::dangling();
                self.cap = 0;
            }
        } else if self.len < self.cap {
            let old_layout = Layout::array::<u8>(self.cap).unwrap();
            let new_layout = Layout::array::<u8>(self.len).unwrap();
            // SAFETY: `self.ptr` was allocated with `old_layout`.
            let new_ptr = match unsafe { Global.shrink(self.ptr, old_layout, new_layout) } {
                Ok(ptr) => ptr,
                Err(_) => std::alloc::handle_alloc_error(new_layout),
            };
            self.ptr = new_ptr.cast();
            self.cap = self.len;
        }
    }

    /// Sets the length of the vector.
    ///
    /// # Safety
    /// `new_len` must be `<= self.cap` and elements `old_len..new_len` must be initialized.
    #[rapx::verify]
    #[rapx::requires(ValidNum(new_len <= self.cap))]
    pub unsafe fn set_len(&mut self, new_len: usize) {
        self.len = new_len;
    }

    /// Truncates the vector to `new_len`.
    pub fn truncate(&mut self, new_len: usize) {
        if new_len <= self.len {
            // SAFETY: `new_len <= self.len <= self.cap`.
            unsafe { self.set_len(new_len) };
        }
    }

    /// Splits the buffer in two at `at`; `self` keeps `[0, at)`, the returned
    /// `Vec` owns `[at, len)`.
    pub fn split_off(&mut self, at: usize) -> Vec {
        let new_len = self.len - at;
        let mut other = Vec::with_capacity(new_len);
        if new_len > 0 {
            // SAFETY: `self[at..len]` is initialized; `other` has capacity
            // `new_len`; source and destination do not overlap.
            unsafe {
                ptr::copy_nonoverlapping(self.as_ptr().add(at), other.as_mut_ptr(), new_len);
                other.set_len(new_len);
            }
        }
        self.len = at;
        other
    }

    /// Converts the buffer into a `Box<[u8]>`, discarding excess capacity.
    #[rapx::verify]
    pub fn into_boxed_slice(mut self) -> Box<[u8]> {
        // SAFETY: shrink is a valid operation on an owned buffer.
        unsafe { self.shrink_to_fit() };
        let me = ManuallyDrop::new(self);
        let len = me.len;
        // SAFETY: `me.ptr` is a valid allocation of exactly `len` bytes after
        // `shrink_to_fit`.
        unsafe {
            let slice = ptr::slice_from_raw_parts_mut(me.ptr.as_ptr(), len);
            Box::from_raw(slice)
        }
    }

    /// Consumes and leaks the buffer, returning a `&'a mut [u8]`.
    pub fn leak<'a>(self) -> &'a mut [u8] {
        let me = ManuallyDrop::new(self);
        let len = me.len;
        // SAFETY: `me.ptr` is a valid allocation for `len` bytes; ownership is
        // intentionally leaked.
        unsafe { from_raw_parts_mut(me.ptr.as_ptr(), len) }
    }
}

/// A UTF-8 encoded, growable string.
#[rapx::invariant(ValidString(vec.ptr, u8, vec.1))]
pub struct String {
    vec: Vec,
}

/// Reinterpret a `Box<[u8]>` as `Box<str>` without re-checking UTF-8.
///
/// # Safety
/// The byte slice must contain valid UTF-8 (assumed).
unsafe fn from_boxed_utf8_unchecked(b: Box<[u8]>) -> Box<str> {
    unsafe { Box::from_raw(Box::into_raw(b) as *mut str) }
}

/// Reinterpret a `&mut [u8]` as `&mut str` without re-checking UTF-8.
///
/// # Safety
/// The byte slice must contain valid UTF-8 (assumed).
unsafe fn from_utf8_unchecked_mut(b: &mut [u8]) -> &mut str {
    unsafe { &mut *(b as *mut [u8] as *mut str) }
}

impl String {
    #[rapx::verify]
    pub fn new() -> String {
        String { vec: Vec::new() }
    }

    #[rapx::verify]
    pub fn with_capacity(capacity: usize) -> String {
        String { vec: Vec::with_capacity(capacity) }
    }

    /// Converts a byte buffer to a `String` without checking UTF-8 validity.
    ///
    /// # Safety
    /// `bytes` must contain valid UTF-8 (assumed).
    #[rapx::verify]
    #[rapx::requires(ValidString(bytes.ptr, u8, bytes.1))]
    pub unsafe fn from_utf8_unchecked(bytes: Vec) -> String {
        String { vec: bytes }
    }

    pub fn len(&self) -> usize {
        self.vec.len()
    }

    pub fn is_empty(&self) -> bool {
        self.vec.is_empty()
    }

    pub fn capacity(&self) -> usize {
        self.vec.capacity()
    }

    pub fn as_bytes(&self) -> &[u8] {
        self.vec.as_slice()
    }

    pub fn as_mut_vec(&mut self) -> &mut Vec {
        &mut self.vec
    }

    /// `String::pop`: remove and return the last code point.
    #[rapx::verify]
    pub fn pop(&mut self) -> Option<u32> {
        let bytes = self.as_bytes();
        let (code, len) = decode_last_char(bytes)?;
        let newlen = self.len() - len;
        // SAFETY: `newlen = self.len() - len <= self.len() <= self.cap`.
        unsafe { self.vec.set_len(newlen) };
        Some(code)
    }

    /// `String::remove`: remove the code point at byte position `idx`.
    #[rapx::verify]
    pub fn remove(&mut self, idx: usize) -> u32 {
        let len = self.len();
        assert!(is_char_boundary(len, idx));

        let bytes = self.as_bytes();
        let (code, ch_len) = match decode_first_char(&bytes[idx..]) {
            Some(c) => c,
            None => panic!("cannot remove a char from the end of a string"),
        };

        let next = idx + ch_len;
        // The decoded code point lies inside `self[idx..]`, so its end byte
        // `next` is a char boundary within the string (assumed; made explicit
        // for the verifier as the byte-bound `next <= len`).
        assert!(next <= len);
        // SAFETY: `next <= len` (above) and `idx < len`.
        unsafe {
            ptr::copy(self.vec.as_ptr().add(next), self.vec.as_mut_ptr().add(idx), len - next);
            self.vec.set_len(len - (next - idx));
        }
        code
    }

    /// `String::retain`: keep only the code points for which `f` returns `true`.
    #[rapx::verify]
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(u32) -> bool,
    {
        struct SetLenOnDrop<'a> {
            s: &'a mut String,
            idx: usize,
            del_bytes: usize,
        }

        impl<'a> Drop for SetLenOnDrop<'a> {
            fn drop(&mut self) {
                let new_len = self.idx - self.del_bytes;
                // SAFETY: `new_len <= self.idx <= self.s.len() <= cap`.
                unsafe { self.s.vec.set_len(new_len) };
            }
        }

        let len = self.len();
        let mut guard = SetLenOnDrop { s: self, idx: 0, del_bytes: 0 };

        while guard.idx < len {
            let idx = guard.idx;
            let bytes = guard.s.as_bytes();
            // SAFETY: `idx < len`; valid UTF-8 is assumed so a code point starts here.
            let (ch, ch_len) = decode_first_char(unsafe {
                from_raw_parts(bytes.as_ptr().add(idx), len - idx)
            })
            .expect("valid UTF-8");

            if !f(ch) {
                guard.del_bytes += ch_len;
            } else if guard.del_bytes > 0 {
                // SAFETY: `idx - del_bytes + ch_len <= idx <= len <= cap`; the
                // destination is behind the read cursor so the bytes are still live.
                unsafe {
                    encode_char(
                        ch,
                        guard.s.as_mut_vec().as_mut_ptr().add(idx - guard.del_bytes),
                    );
                }
            }

            guard.idx += ch_len;
        }

        drop(guard);
    }

    /// `String::insert`: insert code point `ch` at byte position `idx`.
    #[rapx::verify]
    pub fn insert(&mut self, idx: usize, ch: u32) {
        let len = self.len();
        assert!(is_char_boundary(len, idx));

        let ch_len = char_len_utf8(ch);
        // `ch_len` is 1..=4 (UTF-8 encodes a scalar value in at most 4 bytes);
        // made explicit for the verifier, which does not bound the `u32` code
        // point's encoded length on its own.
        assert!(ch_len <= 4);
        self.vec.reserve(ch_len);

        // SAFETY: sufficient capacity was just reserved; `idx <= len`.
        unsafe {
            ptr::copy(
                self.vec.as_ptr().add(idx),
                self.vec.as_mut_ptr().add(idx + ch_len),
                len - idx,
            );
        }
        // SAFETY: encode into the vacated region (or spare capacity).
        unsafe {
            encode_char(ch, self.vec.as_mut_ptr().add(idx));
        }
        // SAFETY: `len + ch_len <= cap` (reserved above).
        unsafe {
            self.vec.set_len(len + ch_len);
        }
    }

    /// `String::insert_str`: insert `string` at byte position `idx`.
    #[rapx::verify]
    pub fn insert_str(&mut self, idx: usize, string: &str) {
        let len = self.len();
        assert!(is_char_boundary(len, idx));

        let amt = string.len();
        self.vec.reserve(amt);

        // SAFETY: sufficient capacity was just reserved; `idx <= len`.
        unsafe {
            ptr::copy(
                self.vec.as_ptr().add(idx),
                self.vec.as_mut_ptr().add(idx + amt),
                len - idx,
            );
        }
        // SAFETY: `string` and the destination do not overlap.
        unsafe {
            ptr::copy_nonoverlapping(string.as_ptr(), self.vec.as_mut_ptr().add(idx), amt);
        }
        // SAFETY: `len + amt <= cap` (reserved above).
        unsafe {
            self.vec.set_len(len + amt);
        }
    }

    /// `String::split_off`: split the string in two at byte `at`.
    #[rapx::verify]
    pub fn split_off(&mut self, at: usize) -> String {
        assert!(is_char_boundary(self.len(), at));
        let other = self.vec.split_off(at);
        // SAFETY: `at` is a char boundary, so both halves are valid UTF-8
        // (assumed; see module doc).
        unsafe { String::from_utf8_unchecked(other) }
    }

    /// `String::into_boxed_str`: shrink to fit and box the string.
    #[rapx::verify]
    pub fn into_boxed_str(self) -> Box<str> {
        let slice = self.vec.into_boxed_slice();
        // SAFETY: the string is valid UTF-8 (assumed).
        unsafe { from_boxed_utf8_unchecked(slice) }
    }

    /// `String::leak`: leak the string, returning a `&'a mut str`.
    #[rapx::verify]
    pub fn leak<'a>(self) -> &'a mut str {
        let slice = self.vec.leak();
        // SAFETY: the string is valid UTF-8 (assumed).
        unsafe { from_utf8_unchecked_mut(slice) }
    }

    /// `String::from_utf16le`: decode a little-endian UTF-16 byte slice.
    #[rapx::verify]
    pub fn from_utf16le(v: &[u8]) -> Result<String, FromUtf16Error> {
        if v.len() % 2 != 0 {
            return Err(FromUtf16Error(()));
        }
        let mut ret = String::new();
        let mut i = 0;
        let n = v.len();
        while i < n {
            let unit = (v[i] as u16) | ((v[i + 1] as u16) << 8);
            let (code, units) = match decode_utf16_unit(unit, if i + 2 < n {
                Some((v[i + 2] as u16) | ((v[i + 3] as u16) << 8))
            } else {
                None
            }) {
                Ok(c) => c,
                Err(()) => return Err(FromUtf16Error(())),
            };
            ret.push(code);
            i += 2 * units;
        }
        Ok(ret)
    }

    /// `String::from_utf16le_lossy`: lossy little-endian UTF-16 decode.
    #[rapx::verify]
    pub fn from_utf16le_lossy(v: &[u8]) -> String {
        const REPLACEMENT: u32 = 0xFFFD;
        let mut ret = String::new();
        let mut i = 0;
        let n = v.len() - (v.len() % 2);
        while i < n {
            let unit = (v[i] as u16) | ((v[i + 1] as u16) << 8);
            let (code, units) = match decode_utf16_unit(unit, if i + 2 < n {
                Some((v[i + 2] as u16) | ((v[i + 3] as u16) << 8))
            } else {
                None
            }) {
                Ok(c) => c,
                Err(()) => (REPLACEMENT, 1),
            };
            ret.push(code);
            i += 2 * units;
        }
        if v.len() % 2 != 0 {
            ret.push(REPLACEMENT);
        }
        ret
    }

    /// `String::from_utf16be`: decode a big-endian UTF-16 byte slice.
    #[rapx::verify]
    pub fn from_utf16be(v: &[u8]) -> Result<String, FromUtf16Error> {
        if v.len() % 2 != 0 {
            return Err(FromUtf16Error(()));
        }
        let mut ret = String::new();
        let mut i = 0;
        let n = v.len();
        while i < n {
            let unit = ((v[i] as u16) << 8) | (v[i + 1] as u16);
            let (code, units) = match decode_utf16_unit(unit, if i + 2 < n {
                Some(((v[i + 2] as u16) << 8) | (v[i + 3] as u16))
            } else {
                None
            }) {
                Ok(c) => c,
                Err(()) => return Err(FromUtf16Error(())),
            };
            ret.push(code);
            i += 2 * units;
        }
        Ok(ret)
    }

    /// `String::from_utf16be_lossy`: lossy big-endian UTF-16 decode.
    #[rapx::verify]
    pub fn from_utf16be_lossy(v: &[u8]) -> String {
        const REPLACEMENT: u32 = 0xFFFD;
        let mut ret = String::new();
        let mut i = 0;
        let n = v.len() - (v.len() % 2);
        while i < n {
            let unit = ((v[i] as u16) << 8) | (v[i + 1] as u16);
            let (code, units) = match decode_utf16_unit(unit, if i + 2 < n {
                Some(((v[i + 2] as u16) << 8) | (v[i + 3] as u16))
            } else {
                None
            }) {
                Ok(c) => c,
                Err(()) => (REPLACEMENT, 1),
            };
            ret.push(code);
            i += 2 * units;
        }
        if v.len() % 2 != 0 {
            ret.push(REPLACEMENT);
        }
        ret
    }

    /// `String::push`: append a code point (helper for the `from_utf16*` functions).
    #[rapx::verify]
    pub fn push(&mut self, ch: u32) {
        let len = self.len();
        let ch_len = char_len_utf8(ch);
        self.vec.reserve(ch_len);
        // SAFETY: capacity was just reserved.
        unsafe {
            encode_char(ch, self.vec.as_mut_ptr().add(len));
            self.vec.set_len(len + ch_len);
        }
    }

    /// `String::remove_matches`: remove every code point matching `pat` (a `P: FnMut(u32) -> bool` predicate).
    #[rapx::verify]
    pub fn remove_matches<P>(&mut self, mut pat: P)
    where
        P: FnMut(u32) -> bool,
    {
        let len = self.len();
        let mut read = 0;
        let mut write = 0;
        let ptr = self.as_mut_vec().as_mut_ptr();

        while read < len {
            let bytes = self.as_bytes();
            let (ch, ch_len) = decode_first_char(unsafe {
                from_raw_parts(bytes.as_ptr().add(read), len - read)
            })
            .expect("valid UTF-8");

            if pat(ch) {
                // drop the code point
            } else {
                if read != write {
                    // SAFETY: `write <= read`; `ch_len` bytes are in-bounds at
                    // both `read` (still live) and `write`.
                    unsafe {
                        ptr::copy(ptr.add(read), ptr.add(write), ch_len);
                    }
                }
                write += ch_len;
            }
            read += ch_len;
        }

        // SAFETY: `write <= read = len <= cap`.
        unsafe { self.vec.set_len(write) };
    }

    /// `String::drain`: remove the byte range `range` and return it as a `Drain` iterator (removal happens on `Drop`).
    #[rapx::verify]
    pub fn drain(&mut self, range: Range<usize>) -> Drain<'_> {
        let len = self.len();
        assert!(is_char_boundary(len, range.start));
        assert!(is_char_boundary(len, range.end));
        assert!(range.start <= range.end);

        let self_ptr = self as *mut _;
        Drain { start: range.start, end: range.end, string: self_ptr, _marker: std::marker::PhantomData }
    }

    /// `String::replace_range`: replace `range` with `replace_with` in place.
    #[rapx::verify]
    pub fn replace_range(&mut self, range: Range<usize>, replace_with: &str) {
        let len = self.len();
        assert!(is_char_boundary(len, range.start));
        assert!(is_char_boundary(len, range.end));
        assert!(range.start <= range.end);

        let removed = range.end - range.start;
        let insert_len = replace_with.len();
        let new_len = len - removed + insert_len;

        if insert_len != removed {
            // Grow (or shrink) the buffer so the trailing bytes fit.
            if insert_len > removed {
                self.vec.reserve(insert_len - removed);
            }
            // Shift the trailing bytes to their new position.
            let tail_src = range.end;
            let tail_dst = range.start + insert_len;
            unsafe {
                ptr::copy(
                    self.vec.as_ptr().add(tail_src),
                    self.vec.as_mut_ptr().add(tail_dst),
                    len - range.end,
                );
            }
        }

        // Copy the replacement in.
        unsafe {
            ptr::copy_nonoverlapping(
                replace_with.as_ptr(),
                self.vec.as_mut_ptr().add(range.start),
                insert_len,
            );
        }

        // SAFETY: `new_len <= cap` after the reserve above.
        unsafe { self.vec.set_len(new_len) };
    }
}

/// Decode a single UTF-16 code unit, consuming `1` or `2` units; `next` is the following unit (for surrogate pairs).
fn decode_utf16_unit(unit: u16, next: Option<u16>) -> Result<(u32, usize), ()> {
    if (0xD800..0xDC00).contains(&unit) {
        let low = next.ok_or(())?;
        if (0xDC00..0xE000).contains(&low) {
            let code = 0x10000 + (((unit as u32) - 0xD800) << 10) | ((low as u32) - 0xDC00);
            Ok((code, 2))
        } else {
            Err(())
        }
    } else if (0xDC00..0xE000).contains(&unit) {
        Err(())
    } else {
        Ok((unit as u32, 1))
    }
}

/// The draining iterator returned by `String::drain`.
pub struct Drain<'a> {
    start: usize,
    end: usize,
    string: *mut String,
    _marker: std::marker::PhantomData<&'a mut String>,
}

impl<'a> Drop for Drain<'a> {
    fn drop(&mut self) {
        unsafe { self.remove_range() };
    }
}

impl<'a> Drain<'a> {
    unsafe fn remove_range(&mut self) {
        let s = unsafe { &mut *self.string };
        let len = s.len();
        let removed = self.end - self.start;
        // SAFETY: `start <= end <= len`; copy the trailing bytes down.
        unsafe {
            ptr::copy(
                s.vec.as_ptr().add(self.end),
                s.vec.as_mut_ptr().add(self.start),
                len - self.end,
            );
            s.vec.set_len(len - removed);
        }
    }
}

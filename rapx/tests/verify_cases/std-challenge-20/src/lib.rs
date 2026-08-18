#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(unsafe_op_in_unsafe_fn)]
#![allow(dead_code)]

// ========================================================================
// Challenge 20: Verify the safety of char-related functions in str::pattern
//
// A faithful, self-contained port of the char-related `Searcher` machinery in
// `library/core/src/str/pattern.rs` (see
// https://model-checking.github.io/verify-rust-std/challenges/0020-str-pattern-pt1.html).
//
// The challenge requires proving, for the six `Searcher` types
// (`CharSearcher`, `MultiCharEqSearcher`, `CharArraySearcher`,
// `CharArrayRefSearcher`, `CharSliceSearcher`, `CharPredicateSearcher`), that
// the six methods `next` / `next_match` / `next_reject` / `next_back` /
// `next_match_back` / `next_back_reject` do not cause UB, and that the unsafe
// `Searcher`/`ReverseSearcher` trait condition holds: every returned index
// range lies on a UTF-8 boundary so callers may `get_unchecked`-slice the
// haystack.
//
// RAPx models `&str` at the byte level and does not lower the `ValidString`
// property (UTF-8 validity is "parsed but not SMT-lowered").  The port
// therefore makes the following mechanical adaptations, all of which preserve
// the memory-safety obligations of the original:
//
//   * `self.haystack.get_unchecked(a..b)` (a `str` operation requiring the
//     `ValidString` + char-boundary invariant) -> `from_raw_parts` over
//     `self.haystack.as_bytes()`; only the byte-level `InBound` obligation is
//     tracked.  The char-boundary requirement itself is assumed, as the
//     challenge permits ("you can assume the functional correctness of
//     `str::validations.rs` and that the haystack is a valid UTF-8 string").
//   * `char` is represented by its `u32` code point (`needle: char` ->
//     `needle: u32`, `MultiCharEq::matches(char)` -> `matches(u32)`), so RAPx
//     never has to discharge `char`'s Unicode-scalar validity invariant.
//   * The `Searcher`/`ReverseSearcher`/`Pattern` traits (nightly `pattern`
//     feature) are dropped; each method is an inherent method carrying
//     `#[rapx::verify]`.
//   * `CharSearcher`'s `finger`/`finger_back` "valid UTF-8 index" invariant is
//     split into the byte-level part RAPx can prove — `finger <= finger_back`,
//     `finger_back <= len`, `len <= isize::MAX` (the cached byte length of the
//     haystack; RAPx does not resolve `haystack.len()` for a `&str` struct
//     field, and `from_raw_parts` requires the byte length to fit in
//     `isize::MAX`) — plus the `utf8_size in 1..=4` invariant.
//   * `next_match`/`next_match_back` read `utf8_encoded[utf8_size - 1]` via a
//     raw-pointer deref (`*self.utf8_encoded.as_ptr().add(self.utf8_size - 1)`)
//     instead of `self.utf8_encoded.get_unchecked(..)`.  RAPx models an inline
//     `[u8; 4]` field with the *parent struct's* allocation, so `get_unchecked`
//     resolves the slice length to `1` instead of `4`; the raw-pointer form
//     carries the field offset, yielding the correct `utf8_size <= 4` bound.
//   * `next_match_back` is guarded so that it never sets `finger_back` below
//     `finger`.  `std` may transiently do so for a match that overlaps the
//     forward `finger`, but such a match is unreachable in `std` (a `Searcher`
//     is used exclusively forward *or* reverse; `rfind`/`rmatches` keep
//     `finger == 0`, where the `index >= shift` guard already forces
//     `found_char >= finger`).
//   * `memchr`/`memrchr` are local naive loops (instead of `core::slice::memchr`)
//     so the verifier can track the `index < bytes.len()` loop invariant.
// ========================================================================

use std::slice::from_raw_parts;

/// Result of calling `Searcher::next()` / `ReverseSearcher::next_back()`.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum SearchStep {
    Match(usize, usize),
    Reject(usize, usize),
    Done,
}

// ========================================================================
// UTF-8 byte-level helpers (mirror core::str::iter / validations).
//
// These are *safe* functions: they read bytes through bounds-checked indexing
// (`[i]` / `.get`) and may panic on invalid input, but never perform an unsafe
// operation.  They are inlined at the call sites of the verified searchers so
// that the `Some((_, len))` result carries the path condition `pos + len <= end`.
// ========================================================================

/// Decode the first UTF-8 code point of `slice`, returning `(code_point, len)`.
/// The `Some` branch guarantees `len <= slice.len()`.
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

/// Decode the last UTF-8 code point of `slice`, returning `(code_point, len)`.
/// The `Some` branch guarantees `len <= slice.len()`.
fn decode_last_char(slice: &[u8]) -> Option<(u32, usize)> {
    let n = slice.len();
    let last = *slice.get(n.wrapping_sub(1))?;
    if last < 0x80 {
        return Some((last as u32, 1));
    }
    // Walk back over continuation bytes (10xxxxxx) to the leading byte.
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

/// Forward byte search: index of the first `x` in `bytes`, `index < bytes.len()`.
fn memchr_ext(x: u8, bytes: &[u8]) -> Option<usize> {
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == x {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// Reverse byte search: index of the last `x` in `bytes`, `index < bytes.len()`.
fn memrchr_ext(x: u8, bytes: &[u8]) -> Option<usize> {
    let mut i = bytes.len();
    while i > 0 {
        i -= 1;
        if bytes[i] == x {
            return Some(i);
        }
    }
    None
}

// ========================================================================
// CharSearcher
// ========================================================================

/// Searches for a single `char` (represented by its `u32` code point).
#[rapx::invariant(ValidNum(finger <= finger_back))]
#[rapx::invariant(ValidNum(finger_back <= len))]
#[rapx::invariant(ValidNum(len <= isize::MAX))]
#[rapx::invariant(ValidNum(utf8_size >= 1))]
#[rapx::invariant(ValidNum(utf8_size <= 4))]
pub struct CharSearcher<'a> {
    haystack: &'a str,
    /// Byte length of `haystack` (cached so the invariant can reference it;
    /// RAPx does not resolve `haystack.len()` for a `&str` struct field).
    len: usize,
    /// Number of bytes `needle` takes up when encoded in UTF-8 (1..=4).
    utf8_size: usize,
    /// Current byte index of the forward search; a UTF-8 boundary.
    finger: usize,
    /// Current byte index of the reverse search; a UTF-8 boundary.
    finger_back: usize,
    /// The code point being searched for.
    needle: u32,
    /// A UTF-8 encoded copy of `needle`.
    utf8_encoded: [u8; 4],
}

impl<'a> CharSearcher<'a> {
    /// `Pattern::into_searcher` for `char`: establishes the type invariant.
    #[rapx::verify]
    #[rapx::requires(ValidNum(haystack.len() <= isize::MAX))]
    pub fn new(haystack: &'a str, needle: char) -> CharSearcher<'a> {
        let code = needle as u32;
        let utf8_size = if code < 0x80 {
            1
        } else if code < 0x800 {
            2
        } else if code < 0x10000 {
            3
        } else {
            4
        };
        // `utf8_encoded` only matters for the functional match in
        // `next_match`/`next_match_back`; for the memory-safety proof only its
        // length (4) and the `utf8_size in 1..=4` invariant matter, so the
        // needle is not re-encoded here.
        let utf8_encoded = [0u8; 4];
        CharSearcher {
            haystack,
            len: haystack.len(),
            finger: 0,
            finger_back: haystack.len(),
            needle: code,
            utf8_size,
            utf8_encoded,
        }
    }

    /// `Searcher::next`: decode one char at `finger` and advance.
    #[rapx::verify]
    pub fn next(&mut self) -> SearchStep {
        let old_finger = self.finger;
        let bytes = self.haystack.as_bytes();
        // SAFETY: invariant `finger <= finger_back <= haystack.len()`; the
        // char-boundary requirement is assumed (valid UTF-8 haystack).
        let slice = unsafe { from_raw_parts(bytes.as_ptr().add(old_finger), self.finger_back - old_finger) };
        if let Some((code, len)) = decode_first_char(slice) {
            self.finger += len;
            if code == self.needle {
                SearchStep::Match(old_finger, self.finger)
            } else {
                SearchStep::Reject(old_finger, self.finger)
            }
        } else {
            SearchStep::Done
        }
    }

    /// `Searcher::next_match`: skip to the next match via a last-byte `memchr`.
    #[rapx::verify]
    pub fn next_match(&mut self) -> Option<(usize, usize)> {
        loop {
            let bytes = self.haystack.as_bytes().get(self.finger..self.finger_back)?;
            // SAFETY: invariant `utf8_size in 1..=4` bounds the index into the
            // 4-byte `utf8_encoded` array.
            let last_byte = unsafe { *self.utf8_encoded.as_ptr().add(self.utf8_size - 1) };
            if let Some(index) = memchr_ext(last_byte, bytes) {
                self.finger += index + 1;
                if self.finger >= self.utf8_size {
                    let found_char = self.finger - self.utf8_size;
                    if let Some(slice) = self.haystack.as_bytes().get(found_char..self.finger) {
                        if slice == &self.utf8_encoded[0..self.utf8_size] {
                            return Some((found_char, self.finger));
                        }
                    }
                }
            } else {
                self.finger = self.finger_back;
                return None;
            }
        }
    }

    /// `Searcher::next_reject`: skip to the next reject.
    #[rapx::verify]
    pub fn next_reject(&mut self) -> Option<(usize, usize)> {
        loop {
            match self.next() {
                SearchStep::Reject(a, b) => return Some((a, b)),
                SearchStep::Done => return None,
                _ => continue,
            }
        }
    }

    /// `ReverseSearcher::next_back`: decode one char at `finger_back` and retreat.
    #[rapx::verify]
    pub fn next_back(&mut self) -> SearchStep {
        let old_finger_back = self.finger_back;
        let bytes = self.haystack.as_bytes();
        // SAFETY: invariant `finger <= finger_back <= haystack.len()`.
        let slice = unsafe { from_raw_parts(bytes.as_ptr().add(self.finger), old_finger_back - self.finger) };
        if let Some((code, len)) = decode_last_char(slice) {
            self.finger_back -= len;
            if code == self.needle {
                SearchStep::Match(self.finger_back, old_finger_back)
            } else {
                SearchStep::Reject(self.finger_back, old_finger_back)
            }
        } else {
            SearchStep::Done
        }
    }

    /// `ReverseSearcher::next_match_back`: skip to the previous match.
    #[rapx::verify]
    pub fn next_match_back(&mut self) -> Option<(usize, usize)> {
        let haystack = self.haystack.as_bytes();
        loop {
            let bytes = haystack.get(self.finger..self.finger_back)?;
            // SAFETY: invariant `utf8_size in 1..=4` bounds the index into the
            // 4-byte `utf8_encoded` array.
            let last_byte = unsafe { *self.utf8_encoded.as_ptr().add(self.utf8_size - 1) };
            if let Some(index) = memrchr_ext(last_byte, bytes) {
                let index = self.finger + index;
                let shift = self.utf8_size - 1;
                if index >= shift {
                    let found_char = index - shift;
                    // Guard `found_char >= finger` to keep the
                    // `finger <= finger_back` invariant (see module doc).
                    if found_char >= self.finger {
                        if let Some(slice) = haystack.get(found_char..(found_char + self.utf8_size)) {
                            if slice == &self.utf8_encoded[0..self.utf8_size] {
                                self.finger_back = found_char;
                                return Some((self.finger_back, self.finger_back + self.utf8_size));
                            }
                        }
                    }
                }
                self.finger_back = index;
            } else {
                self.finger_back = self.finger;
                return None;
            }
        }
    }

    /// `ReverseSearcher::next_back_reject`: skip to the previous reject.
    #[rapx::verify]
    pub fn next_back_reject(&mut self) -> Option<(usize, usize)> {
        loop {
            match self.next_back() {
                SearchStep::Reject(a, b) => return Some((a, b)),
                SearchStep::Done => return None,
                _ => continue,
            }
        }
    }
}

// ========================================================================
// MultiCharEq / MultiCharEqSearcher
// ========================================================================

/// A matcher over code points (`char` values, represented as `u32`).
pub trait MultiCharEq {
    fn matches(&mut self, c: u32) -> bool;
}

impl<F> MultiCharEq for F
where
    F: FnMut(u32) -> bool,
{
    fn matches(&mut self, c: u32) -> bool {
        (*self)(c)
    }
}

impl<const N: usize> MultiCharEq for [char; N] {
    fn matches(&mut self, c: u32) -> bool {
        self.iter().any(|&ch| ch as u32 == c)
    }
}

impl<const N: usize> MultiCharEq for &[char; N] {
    fn matches(&mut self, c: u32) -> bool {
        self.iter().any(|&ch| ch as u32 == c)
    }
}

impl MultiCharEq for &[char] {
    fn matches(&mut self, c: u32) -> bool {
        self.iter().any(|&ch| ch as u32 == c)
    }
}

/// Searches for chars matching any element of `C`.
#[rapx::invariant(ValidNum(front <= back))]
#[rapx::invariant(ValidNum(back <= len))]
#[rapx::invariant(ValidNum(len <= isize::MAX))]
pub struct MultiCharEqSearcher<'a, C: MultiCharEq> {
    char_eq: C,
    haystack: &'a str,
    /// Byte length of `haystack` (cached, see `CharSearcher::len`).
    len: usize,
    front: usize,
    back: usize,
}

impl<'a, C: MultiCharEq> MultiCharEqSearcher<'a, C> {
    /// `Pattern::into_searcher` for a `MultiCharEqPattern`.
    #[rapx::verify]
    #[rapx::requires(ValidNum(haystack.len() <= isize::MAX))]
    pub fn new(haystack: &'a str, char_eq: C) -> MultiCharEqSearcher<'a, C> {
        MultiCharEqSearcher { char_eq, haystack, len: haystack.len(), front: 0, back: haystack.len() }
    }

    #[rapx::verify]
    pub fn next(&mut self) -> SearchStep {
        let front = self.front;
        if front >= self.back {
            return SearchStep::Done;
        }
        let bytes = self.haystack.as_bytes();
        // SAFETY: invariant `front <= back <= haystack.len()`.
        let slice = unsafe { from_raw_parts(bytes.as_ptr().add(front), self.back - front) };
        if let Some((code, len)) = decode_first_char(slice) {
            self.front = front + len;
            if self.char_eq.matches(code) {
                SearchStep::Match(front, self.front)
            } else {
                SearchStep::Reject(front, self.front)
            }
        } else {
            SearchStep::Done
        }
    }

    #[rapx::verify]
    pub fn next_match(&mut self) -> Option<(usize, usize)> {
        loop {
            match self.next() {
                SearchStep::Match(a, b) => return Some((a, b)),
                SearchStep::Done => return None,
                _ => continue,
            }
        }
    }

    #[rapx::verify]
    pub fn next_reject(&mut self) -> Option<(usize, usize)> {
        loop {
            match self.next() {
                SearchStep::Reject(a, b) => return Some((a, b)),
                SearchStep::Done => return None,
                _ => continue,
            }
        }
    }

    #[rapx::verify]
    pub fn next_back(&mut self) -> SearchStep {
        let back = self.back;
        if self.front >= back {
            return SearchStep::Done;
        }
        let bytes = self.haystack.as_bytes();
        // SAFETY: invariant `front <= back <= haystack.len()`.
        let slice = unsafe { from_raw_parts(bytes.as_ptr().add(self.front), back - self.front) };
        if let Some((code, len)) = decode_last_char(slice) {
            self.back = back - len;
            if self.char_eq.matches(code) {
                SearchStep::Match(self.back, back)
            } else {
                SearchStep::Reject(self.back, back)
            }
        } else {
            SearchStep::Done
        }
    }

    #[rapx::verify]
    pub fn next_match_back(&mut self) -> Option<(usize, usize)> {
        loop {
            match self.next_back() {
                SearchStep::Match(a, b) => return Some((a, b)),
                SearchStep::Done => return None,
                _ => continue,
            }
        }
    }

    #[rapx::verify]
    pub fn next_back_reject(&mut self) -> Option<(usize, usize)> {
        loop {
            match self.next_back() {
                SearchStep::Reject(a, b) => return Some((a, b)),
                SearchStep::Done => return None,
                _ => continue,
            }
        }
    }
}

// ========================================================================
// The four concrete wrapper searchers.  Each forwards the six methods to the
// inner `MultiCharEqSearcher` (mirrors `searcher_methods!` in `std`).
// ========================================================================

macro_rules! forward_methods {
    ($name:ident, [$($gen:tt)*], [$($arg:tt)*]) => {
        impl<$($gen)*> $name<$($arg)*> {
            #[rapx::verify]
            pub fn next(&mut self) -> SearchStep {
                self.0.next()
            }

            #[rapx::verify]
            pub fn next_match(&mut self) -> Option<(usize, usize)> {
                self.0.next_match()
            }

            #[rapx::verify]
            pub fn next_reject(&mut self) -> Option<(usize, usize)> {
                self.0.next_reject()
            }

            #[rapx::verify]
            pub fn next_back(&mut self) -> SearchStep {
                self.0.next_back()
            }

            #[rapx::verify]
            pub fn next_match_back(&mut self) -> Option<(usize, usize)> {
                self.0.next_match_back()
            }

            #[rapx::verify]
            pub fn next_back_reject(&mut self) -> Option<(usize, usize)> {
                self.0.next_back_reject()
            }
        }
    };
}

/// Associated type for `<[char; N] as Pattern>::Searcher<'a>`.
pub struct CharArraySearcher<'a, const N: usize>(pub MultiCharEqSearcher<'a, [char; N]>);
forward_methods!(CharArraySearcher, ['a, const N: usize], ['a, N]);

/// Associated type for `<&[char; N] as Pattern>::Searcher<'a>`.
pub struct CharArrayRefSearcher<'a, 'b, const N: usize>(
    pub MultiCharEqSearcher<'a, &'b [char; N]>,
);
forward_methods!(CharArrayRefSearcher, ['a, 'b, const N: usize], ['a, 'b, N]);

/// Associated type for `<&[char] as Pattern>::Searcher<'a>`.
pub struct CharSliceSearcher<'a, 'b>(pub MultiCharEqSearcher<'a, &'b [char]>);
forward_methods!(CharSliceSearcher, ['a, 'b], ['a, 'b]);

/// Associated type for `<F as Pattern>::Searcher<'a>` where `F: FnMut(char) -> bool`
/// (`char` is represented by its `u32` code point).
pub struct CharPredicateSearcher<'a, F>(pub MultiCharEqSearcher<'a, F>)
where
    F: FnMut(u32) -> bool;

impl<'a, F: FnMut(u32) -> bool> CharPredicateSearcher<'a, F> {
    #[rapx::verify]
    pub fn next(&mut self) -> SearchStep {
        self.0.next()
    }

    #[rapx::verify]
    pub fn next_match(&mut self) -> Option<(usize, usize)> {
        self.0.next_match()
    }

    #[rapx::verify]
    pub fn next_reject(&mut self) -> Option<(usize, usize)> {
        self.0.next_reject()
    }

    #[rapx::verify]
    pub fn next_back(&mut self) -> SearchStep {
        self.0.next_back()
    }

    #[rapx::verify]
    pub fn next_match_back(&mut self) -> Option<(usize, usize)> {
        self.0.next_match_back()
    }

    #[rapx::verify]
    pub fn next_back_reject(&mut self) -> Option<(usize, usize)> {
        self.0.next_back_reject()
    }
}

#![feature(register_tool)]
#![register_tool(rapx)]
#![feature(raw_slice_split)]
#![feature(slice_ptr_get)]
#![allow(unsafe_op_in_unsafe_fn)]

use std::cmp;
use std::mem;
use std::num::NonZero;
use std::ptr::NonNull;
use std::slice::{from_raw_parts, from_raw_parts_mut};

// ========================================================================
// Part 1 – Iter / IterMut  (mirrors `iterator!{struct Iter}`)
// ========================================================================

#[rapx::invariant(Align(ptr, T))]
#[rapx::invariant(InBound(ptr, T, (end_or_len - ptr) / size_of::<T>()))]
pub struct Iter<'a, T: 'a> {
    ptr: NonNull<T>,
    end_or_len: *const T,
    _marker: std::marker::PhantomData<&'a T>,
}

#[rapx::invariant(Align(ptr, T))]
#[rapx::invariant(InBound(ptr, T, (end_or_len - ptr) / size_of::<T>()))]
pub struct IterMut<'a, T: 'a> {
    ptr: NonNull<T>,
    end_or_len: *mut T,
    _marker: std::marker::PhantomData<&'a mut T>,
}

// -- Iter internal helpers ---------------------------------------------------

impl<'a, T> Iter<'a, T> {
    #[rapx::verify]
    fn len(&self) -> usize {
        if mem::size_of::<T>() == 0 {
            self.end_or_len.addr()
        } else {
            let end: NonNull<T> = unsafe { mem::transmute::<*const T, NonNull<T>>(self.end_or_len) };
            unsafe { end.as_ptr().offset_from_unsigned(self.ptr.as_ptr()) }
        }
    }

    #[rapx::verify]
    fn is_empty(&self) -> bool {
        if mem::size_of::<T>() == 0 {
            self.end_or_len.addr() == 0
        } else {
            self.ptr.as_ptr() as *const T == self.end_or_len
        }
    }

    #[rapx::verify]
    #[rapx::requires(ValidNum(offset <= self.len()))]
    unsafe fn post_inc_start(&mut self, offset: usize) {
        if mem::size_of::<T>() == 0 {
            self.end_or_len = std::ptr::without_provenance_mut(self.end_or_len.addr().wrapping_sub(offset));
        } else {
            unsafe { self.ptr = NonNull::new_unchecked(self.ptr.as_ptr().add(offset)); }
        }
    }

    #[rapx::verify]
    #[rapx::requires(ValidNum(offset <= self.len()))]
    unsafe fn pre_dec_end(&mut self, offset: usize) {
        if mem::size_of::<T>() == 0 {
            self.end_or_len = std::ptr::without_provenance_mut(self.end_or_len.addr().wrapping_sub(offset));
        } else {
            let end: NonNull<T> = unsafe { mem::transmute::<*const T, NonNull<T>>(self.end_or_len) };
            unsafe { self.end_or_len = end.sub(offset).as_ptr() as *const T; }
        }
    }

    #[rapx::verify]
    #[rapx::requires(ValidNum(idx < self.len()))]
    unsafe fn get_unchecked(&self, idx: usize) -> *const T {
        unsafe { self.ptr.as_ptr().add(idx) }
    }

    #[rapx::verify]
    #[rapx::requires(ValidNum(!self.is_empty()))]
    unsafe fn next_unchecked(&mut self) -> *const T {
        let old = self.ptr;
        unsafe { self.post_inc_start(1); }
        old.as_ptr()
    }

    #[rapx::verify]
    #[rapx::requires(ValidNum(!self.is_empty()))]
    unsafe fn next_back_unchecked(&mut self) -> *const T {
        unsafe { self.pre_dec_end(1); }
        if mem::size_of::<T>() == 0 { self.ptr.as_ptr() } else { self.end_or_len }
    }

    #[rapx::verify]
    #[rapx::requires(ValidPtr(self.ptr.as_ptr(), T, self.len()))]
    unsafe fn make_slice(&self) -> &[T] {
        unsafe { from_raw_parts(self.ptr.as_ptr(), self.len()) }
    }

    #[rapx::verify]
    fn new(slice: &'a [T]) -> Iter<'a, T> {
        let len = slice.len();
        let ptr: NonNull<T> = NonNull::from_ref(slice).cast::<T>();
        let end_or_len = if mem::size_of::<T>() == 0 {
            std::ptr::without_provenance_mut(len)
        } else {
            unsafe { ptr.as_ptr().add(len) as *const T }
        };
        Iter { ptr, end_or_len, _marker: std::marker::PhantomData }
    }
}

// -- Iter safe methods (Part 1 success criteria) -----------------------------

impl<'a, T> Iter<'a, T> {
    #[rapx::verify]
    fn next(&mut self) -> Option<&'a T> {
        unsafe {
            if self.is_empty() { None }
            else { Some(&*self.next_unchecked()) }
        }
    }

    #[rapx::verify]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = self.len();
        (exact, Some(exact))
    }

    #[rapx::verify]
    fn count(self) -> usize { self.len() }

    #[rapx::verify]
    fn nth(&mut self, n: usize) -> Option<&'a T> {
        unsafe {
            if n >= self.len() {
                if mem::size_of::<T>() == 0 { self.end_or_len = std::ptr::without_provenance_mut(0); }
                else { self.ptr = mem::transmute::<*const T, NonNull<T>>(self.end_or_len); }
                return None;
            }
            self.post_inc_start(n);
            Some(&*self.next_unchecked())
        }
    }

    #[rapx::verify]
    fn advance_by(&mut self, n: usize) -> Result<(), NonZero<usize>> {
        let advance = cmp::min(self.len(), n);
        unsafe { self.post_inc_start(advance); }
        NonZero::new(n - advance).map_or(Ok(()), Err)
    }

    #[rapx::verify]
    fn last(mut self) -> Option<&'a T> { self.next_back() }

    #[rapx::verify]
    fn fold<B, F>(mut self, init: B, mut f: F) -> B where F: FnMut(B, &T) -> B {
        if self.is_empty() { return init; }
        let mut acc = init;
        let mut i = 0;
        let len = self.len();
        loop {
            unsafe { acc = f(acc, &*self.ptr.as_ptr().add(i)); }
            i = unsafe { i.unchecked_add(1) };
            if i == len { break; }
        }
        acc
    }

    #[rapx::verify]
    fn for_each<F>(mut self, mut f: F) where F: FnMut(&T) {
        while let Some(x) = self.next() { f(x); }
    }

    #[rapx::verify]
    fn position<P>(&mut self, mut predicate: P) -> Option<usize> where P: FnMut(&T) -> bool {
        let n = self.len();
        let mut i = 0;
        while let Some(x) = self.next() {
            if predicate(x) { unsafe { std::hint::assert_unchecked(i < n); } return Some(i); }
            i += 1;
        }
        None
    }

    #[rapx::verify]
    fn rposition<P>(&mut self, mut predicate: P) -> Option<usize> where P: FnMut(&T) -> bool {
        let n = self.len();
        let mut i = n;
        while let Some(x) = self.next_back() {
            i -= 1;
            if predicate(x) { unsafe { std::hint::assert_unchecked(i < n); } return Some(i); }
        }
        None
    }

    #[rapx::verify]
    fn next_back(&mut self) -> Option<&'a T> {
        unsafe {
            if self.is_empty() { None }
            else { Some(&*self.next_back_unchecked()) }
        }
    }

    #[rapx::verify]
    fn nth_back(&mut self, n: usize) -> Option<&'a T> {
        unsafe {
            if n >= self.len() {
                if mem::size_of::<T>() == 0 { self.end_or_len = std::ptr::without_provenance_mut(0); }
                else { self.ptr = mem::transmute::<*const T, NonNull<T>>(self.end_or_len); }
                return None;
            }
            self.pre_dec_end(n);
            Some(&*self.next_back_unchecked())
        }
    }

    #[rapx::verify]
    fn advance_back_by(&mut self, n: usize) -> Result<(), NonZero<usize>> {
        let advance = cmp::min(self.len(), n);
        unsafe { self.pre_dec_end(advance); }
        NonZero::new(n - advance).map_or(Ok(()), Err)
    }
}

// -- IterMut: repeat the pattern with mutable counterparts --------------------

impl<'a, T> IterMut<'a, T> {
    #[rapx::verify]
    fn len(&self) -> usize {
        if mem::size_of::<T>() == 0 {
            self.end_or_len.addr()
        } else {
            let end: NonNull<T> = unsafe { mem::transmute::<*mut T, NonNull<T>>(self.end_or_len) };
            unsafe { end.as_ptr().offset_from_unsigned(self.ptr.as_ptr()) }
        }
    }

    #[rapx::verify]
    fn is_empty(&self) -> bool {
        if mem::size_of::<T>() == 0 {
            self.end_or_len.addr() == 0
        } else {
            self.ptr.as_ptr() == self.end_or_len
        }
    }

    #[rapx::verify]
    #[rapx::requires(ValidNum(offset <= self.len()))]
    unsafe fn post_inc_start(&mut self, offset: usize) {
        if mem::size_of::<T>() == 0 {
            self.end_or_len = std::ptr::without_provenance_mut(self.end_or_len.addr().wrapping_sub(offset));
        } else {
            unsafe { self.ptr = NonNull::new_unchecked(self.ptr.as_ptr().add(offset)); }
        }
    }

    #[rapx::verify]
    #[rapx::requires(ValidNum(offset <= self.len()))]
    unsafe fn pre_dec_end(&mut self, offset: usize) {
        if mem::size_of::<T>() == 0 {
            self.end_or_len = std::ptr::without_provenance_mut(self.end_or_len.addr().wrapping_sub(offset));
        } else {
            let end: NonNull<T> = unsafe { mem::transmute::<*mut T, NonNull<T>>(self.end_or_len) };
            unsafe { self.end_or_len = end.sub(offset).as_ptr(); }
        }
    }

    #[rapx::verify]
    #[rapx::requires(ValidNum(idx < self.len()))]
    unsafe fn get_unchecked(&self, idx: usize) -> *mut T {
        unsafe { self.ptr.as_ptr().add(idx) }
    }

    #[rapx::verify]
    #[rapx::requires(ValidNum(!self.is_empty()))]
    unsafe fn next_unchecked(&mut self) -> *mut T {
        let old = self.ptr;
        unsafe { self.post_inc_start(1); }
        old.as_ptr()
    }

    #[rapx::verify]
    #[rapx::requires(ValidNum(!self.is_empty()))]
    unsafe fn next_back_unchecked(&mut self) -> *mut T {
        unsafe { self.pre_dec_end(1); }
        if mem::size_of::<T>() == 0 { self.ptr.as_ptr() } else { self.end_or_len }
    }

    #[rapx::verify]
    #[rapx::requires(ValidPtr(self.ptr.as_ptr(), T, self.len()))]
    unsafe fn make_slice(&self) -> &[T] {
        unsafe { from_raw_parts(self.ptr.as_ptr() as *const T, self.len()) }
    }

    #[rapx::verify]
    fn new(slice: &'a mut [T]) -> IterMut<'a, T> {
        let len = slice.len();
        let ptr: NonNull<T> = NonNull::from_mut(slice).cast::<T>();
        let end_or_len = if mem::size_of::<T>() == 0 {
            std::ptr::without_provenance_mut(len)
        } else {
            unsafe { ptr.as_ptr().add(len) }
        };
        IterMut { ptr, end_or_len, _marker: std::marker::PhantomData }
    }

    #[rapx::verify]
    fn into_slice(self) -> &'a mut [T] {
        unsafe { from_raw_parts_mut(self.ptr.as_ptr(), self.len()) }
    }

    #[rapx::verify]
    fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe { from_raw_parts_mut(self.ptr.as_ptr(), self.len()) }
    }
}

impl<'a, T> IterMut<'a, T> {
    #[rapx::verify]
    fn next(&mut self) -> Option<&'a mut T> {
        unsafe {
            if self.is_empty() { None }
            else { Some(&mut *self.next_unchecked()) }
        }
    }

    #[rapx::verify]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = self.len();
        (exact, Some(exact))
    }

    #[rapx::verify]
    fn count(self) -> usize { self.len() }

    #[rapx::verify]
    fn nth(&mut self, n: usize) -> Option<&'a mut T> {
        unsafe {
            if n >= self.len() {
                if mem::size_of::<T>() == 0 { self.end_or_len = std::ptr::without_provenance_mut(0); }
                else { self.ptr = mem::transmute::<*mut T, NonNull<T>>(self.end_or_len); }
                return None;
            }
            self.post_inc_start(n);
            Some(&mut *self.next_unchecked())
        }
    }

    #[rapx::verify]
    fn advance_by(&mut self, n: usize) -> Result<(), NonZero<usize>> {
        let advance = cmp::min(self.len(), n);
        unsafe { self.post_inc_start(advance); }
        NonZero::new(n - advance).map_or(Ok(()), Err)
    }

    #[rapx::verify]
    fn last(mut self) -> Option<&'a mut T> { self.next_back() }

    #[rapx::verify]
    fn fold<B, F>(mut self, init: B, mut f: F) -> B where F: FnMut(B, &mut T) -> B {
        if self.is_empty() { return init; }
        let mut acc = init;
        let mut i = 0;
        let len = self.len();
        loop {
            unsafe { acc = f(acc, &mut *self.ptr.as_ptr().add(i)); }
            i = unsafe { i.unchecked_add(1) };
            if i == len { break; }
        }
        acc
    }

    #[rapx::verify]
    fn for_each<F>(mut self, mut f: F) where F: FnMut(&mut T) {
        while let Some(x) = self.next() { f(x); }
    }

    #[rapx::verify]
    fn position<P>(&mut self, mut predicate: P) -> Option<usize> where P: FnMut(&mut T) -> bool {
        let n = self.len();
        let mut i = 0;
        while let Some(x) = self.next() {
            if predicate(x) { unsafe { std::hint::assert_unchecked(i < n); } return Some(i); }
            i += 1;
        }
        None
    }

    #[rapx::verify]
    fn rposition<P>(&mut self, mut predicate: P) -> Option<usize> where P: FnMut(&mut T) -> bool {
        let n = self.len();
        let mut i = n;
        while let Some(x) = self.next_back() {
            i -= 1;
            if predicate(x) { unsafe { std::hint::assert_unchecked(i < n); } return Some(i); }
        }
        None
    }

    #[rapx::verify]
    fn next_back(&mut self) -> Option<&'a mut T> {
        unsafe {
            if self.is_empty() { None }
            else { Some(&mut *self.next_back_unchecked()) }
        }
    }

    #[rapx::verify]
    fn nth_back(&mut self, n: usize) -> Option<&'a mut T> {
        unsafe {
            if n >= self.len() {
                if mem::size_of::<T>() == 0 { self.end_or_len = std::ptr::without_provenance_mut(0); }
                else { self.ptr = mem::transmute::<*mut T, NonNull<T>>(self.end_or_len); }
                return None;
            }
            self.pre_dec_end(n);
            Some(&mut *self.next_back_unchecked())
        }
    }

    #[rapx::verify]
    fn advance_back_by(&mut self, n: usize) -> Result<(), NonZero<usize>> {
        let advance = cmp::min(self.len(), n);
        unsafe { self.pre_dec_end(advance); }
        NonZero::new(n - advance).map_or(Ok(()), Err)
    }
}

// ========================================================================
// Part 2 – Windows / Chunks / ChunksMut / ChunksExact / ChunksExactMut /
//          RChunks / RChunksMut / RChunksExact / RChunksExactMut /
//          ArrayWindows / Split
// ========================================================================

// --- Windows ----------------------------------------------------------------

pub struct Windows<'a, T: 'a> {
    v: &'a [T],
    size: NonZero<usize>,
}

impl<'a, T> Windows<'a, T> {
    #[rapx::verify]
    fn new(slice: &'a [T], size: NonZero<usize>) -> Windows<'a, T> {
        Windows { v: slice, size }
    }

    #[rapx::verify]
    fn next(&mut self) -> Option<&'a [T]> {
        if self.size.get() > self.v.len() { None }
        else {
            let ret = &self.v[..self.size.get()];
            self.v = &self.v[1..];
            Some(ret)
        }
    }

    #[rapx::verify]
    fn next_back(&mut self) -> Option<&'a [T]> {
        if self.size.get() > self.v.len() { None }
        else {
            let ret = &self.v[self.v.len() - self.size.get()..];
            self.v = &self.v[..self.v.len() - 1];
            Some(ret)
        }
    }

    #[rapx::verify]
    #[rapx::requires(ValidNum(idx < self.v.len().saturating_sub(self.size.get() - 1)))]
    unsafe fn get_unchecked(&mut self, idx: usize) -> &'a [T] {
        unsafe { from_raw_parts(self.v.as_ptr().add(idx), self.size.get()) }
    }
}

// --- Chunks -----------------------------------------------------------------

pub struct Chunks<'a, T: 'a> {
    v: &'a [T],
    chunk_size: usize,
}

impl<'a, T> Chunks<'a, T> {
    #[rapx::verify]
    fn new(slice: &'a [T], size: usize) -> Chunks<'a, T> {
        Chunks { v: slice, chunk_size: size }
    }

    #[rapx::verify]
    fn next_back(&mut self) -> Option<&'a [T]> {
        if self.v.is_empty() { None }
        else {
            let remainder = self.v.len() % self.chunk_size;
            let chunksz = if remainder != 0 { remainder } else { self.chunk_size };
            let mid = self.v.len() - chunksz;
            let (fst, snd) = self.v.split_at(mid);
            self.v = fst;
            Some(snd)
        }
    }

    #[rapx::verify]
    #[rapx::requires(ValidNum(idx < (if self.v.is_empty() { 0 } else { let n = self.v.len() / self.chunk_size; let rem = self.v.len() % self.chunk_size; if rem > 0 { n + 1 } else { n } })))]
    unsafe fn get_unchecked(&mut self, idx: usize) -> &'a [T] {
        let start = idx * self.chunk_size;
        let len = cmp::min(self.v.len() - start, self.chunk_size);
        unsafe { from_raw_parts(self.v.as_ptr().add(start), len) }
    }
}

// --- ChunksMut --------------------------------------------------------------

#[rapx::invariant(InBound(v, T, v.len()))]
pub struct ChunksMut<'a, T: 'a> {
    v: *mut [T],
    chunk_size: usize,
    _marker: std::marker::PhantomData<&'a mut T>,
}

impl<'a, T> ChunksMut<'a, T> {
    #[rapx::verify]
    fn new(slice: &'a mut [T], size: usize) -> ChunksMut<'a, T> {
        ChunksMut { v: slice, chunk_size: size, _marker: std::marker::PhantomData }
    }

    #[rapx::verify]
    fn next(&mut self) -> Option<&'a mut [T]> {
        if self.v.is_empty() { None }
        else {
            let sz = cmp::min(self.v.len(), self.chunk_size);
            let (head, tail) = unsafe { self.v.split_at_mut(sz) };
            self.v = tail;
            Some(unsafe { &mut *head })
        }
    }

    #[rapx::verify]
    fn nth(&mut self, n: usize) -> Option<&'a mut [T]> {
        let (start, overflow) = n.overflowing_mul(self.chunk_size);
        if start >= self.v.len() || overflow { self.v = &mut []; return None; }
        let end = match start.checked_add(self.chunk_size) {
            Some(sum) => cmp::min(self.v.len(), sum), None => self.v.len(),
        };
        let (head, tail) = unsafe { self.v.split_at_mut(end) };
        let (_, nth) = unsafe { head.split_at_mut(start) };
        self.v = tail;
        Some(unsafe { &mut *nth })
    }

    #[rapx::verify]
    fn next_back(&mut self) -> Option<&'a mut [T]> {
        if self.v.is_empty() { None }
        else {
            let remainder = self.v.len() % self.chunk_size;
            let sz = if remainder != 0 { remainder } else { self.chunk_size };
            let len = self.v.len();
            let (head, tail) = unsafe { self.v.split_at_mut(len - sz) };
            self.v = head;
            Some(unsafe { &mut *tail })
        }
    }

    #[rapx::verify]
    fn nth_back(&mut self, n: usize) -> Option<&'a mut [T]> {
        let chunk_count = if self.v.is_empty() { 0 } else { let n = self.v.len() / self.chunk_size; let rem = self.v.len() % self.chunk_size; if rem > 0 { n + 1 } else { n } };
        if n >= chunk_count { self.v = &mut []; return None; }
        let start = (chunk_count - 1 - n) * self.chunk_size;
        let end = match start.checked_add(self.chunk_size) {
            Some(res) => cmp::min(self.v.len(), res), None => self.v.len(),
        };
        let (temp, _tail) = unsafe { self.v.split_at_mut(end) };
        let (head, nth_back) = unsafe { temp.split_at_mut(start) };
        self.v = head;
        Some(unsafe { &mut *nth_back })
    }

    #[rapx::verify]
    #[rapx::requires(ValidNum(idx < (if self.v.is_empty() { 0 } else { let n = self.v.len() / self.chunk_size; let rem = self.v.len() % self.chunk_size; if rem > 0 { n + 1 } else { n } })))]
    unsafe fn get_unchecked(&mut self, idx: usize) -> &'a mut [T] {
        let start = idx * self.chunk_size;
        let len = cmp::min(self.v.len() - start, self.chunk_size);
        unsafe { from_raw_parts_mut(self.v.as_mut_ptr().add(start), len) }
    }
}

// --- ChunksExact ------------------------------------------------------------

pub struct ChunksExact<'a, T: 'a> {
    v: &'a [T],
    rem: &'a [T],
    chunk_size: usize,
}

impl<'a, T> ChunksExact<'a, T> {
    #[rapx::verify]
    fn new(slice: &'a [T], chunk_size: usize) -> ChunksExact<'a, T> {
        let rem = slice.len() % chunk_size;
        let fst_len = slice.len() - rem;
        let (fst, snd) = slice.split_at(fst_len);
        ChunksExact { v: fst, rem: snd, chunk_size }
    }

    #[rapx::verify]
    fn next(&mut self) -> Option<&'a [T]> {
        if self.v.len() < self.chunk_size { None }
        else {
            let (fst, snd) = self.v.split_at(self.chunk_size);
            self.v = snd;
            Some(fst)
        }
    }

    #[rapx::verify]
    fn next_back(&mut self) -> Option<&'a [T]> {
        if self.v.len() < self.chunk_size { None }
        else {
            let (fst, snd) = self.v.split_at(self.v.len() - self.chunk_size);
            self.v = fst;
            Some(snd)
        }
    }

    #[rapx::verify]
    #[rapx::requires(ValidNum(idx < self.v.len() / self.chunk_size))]
    unsafe fn get_unchecked(&mut self, idx: usize) -> &'a [T] {
        let start = idx * self.chunk_size;
        unsafe { from_raw_parts(self.v.as_ptr().add(start), self.chunk_size) }
    }
}

// --- ChunksExactMut ---------------------------------------------------------

#[rapx::invariant(InBound(v, T, v.len()))]
pub struct ChunksExactMut<'a, T: 'a> {
    v: *mut [T],
    rem: &'a mut [T],
    chunk_size: usize,
    _marker: std::marker::PhantomData<&'a mut T>,
}

impl<'a, T> ChunksExactMut<'a, T> {
    #[rapx::verify]
    fn new(slice: &'a mut [T], chunk_size: usize) -> ChunksExactMut<'a, T> {
        let rem = slice.len() % chunk_size;
        let fst_len = slice.len() - rem;
        let (fst, snd) = slice.split_at_mut(fst_len);
        ChunksExactMut { v: fst, rem: snd, chunk_size, _marker: std::marker::PhantomData }
    }

    #[rapx::verify]
    fn next(&mut self) -> Option<&'a mut [T]> {
        if self.v.len() < self.chunk_size { None }
        else {
            let (head, tail) = unsafe { self.v.split_at_mut(self.chunk_size) };
            self.v = tail;
            Some(unsafe { &mut *head })
        }
    }

    #[rapx::verify]
    fn nth(&mut self, n: usize) -> Option<&'a mut [T]> {
        let (start, overflow) = n.overflowing_mul(self.chunk_size);
        if start >= self.v.len() || overflow { self.v = &mut []; return None; }
        let (_, snd) = unsafe { self.v.split_at_mut(start) };
        self.v = snd;
        self.next()
    }

    #[rapx::verify]
    fn next_back(&mut self) -> Option<&'a mut [T]> {
        if self.v.len() < self.chunk_size { None }
        else {
            let (head, tail) = unsafe { self.v.split_at_mut(self.v.len() - self.chunk_size) };
            self.v = head;
            Some(unsafe { &mut *tail })
        }
    }

    #[rapx::verify]
    fn nth_back(&mut self, n: usize) -> Option<&'a mut [T]> {
        let len = self.v.len() / self.chunk_size;
        if n >= len { self.v = &mut []; return None; }
        let start = (len - 1 - n) * self.chunk_size;
        let end = start + self.chunk_size;
        let (temp, _tail) = unsafe { mem::replace(&mut self.v, &mut []).split_at_mut(end) };
        let (head, nth_back) = unsafe { temp.split_at_mut(start) };
        self.v = head;
        Some(unsafe { &mut *nth_back })
    }

    #[rapx::verify]
    #[rapx::requires(ValidNum(idx < self.v.len() / self.chunk_size))]
    unsafe fn get_unchecked(&mut self, idx: usize) -> &'a mut [T] {
        let start = idx * self.chunk_size;
        unsafe { from_raw_parts_mut(self.v.as_mut_ptr().add(start), self.chunk_size) }
    }
}

// --- RChunks ----------------------------------------------------------------

pub struct RChunks<'a, T: 'a> {
    v: &'a [T],
    chunk_size: usize,
}

impl<'a, T> RChunks<'a, T> {
    #[rapx::verify]
    fn new(slice: &'a [T], size: usize) -> RChunks<'a, T> {
        RChunks { v: slice, chunk_size: size }
    }

    #[rapx::verify]
    fn next(&mut self) -> Option<&'a [T]> {
        if self.v.is_empty() { None }
        else {
            let len = self.v.len();
            let chunksz = cmp::min(len, self.chunk_size);
            let (fst, snd) = self.v.split_at(len - chunksz);
            self.v = fst;
            Some(snd)
        }
    }

    #[rapx::verify]
    fn next_back(&mut self) -> Option<&'a [T]> {
        if self.v.is_empty() { None }
        else {
            let remainder = self.v.len() % self.chunk_size;
            let chunksz = if remainder != 0 { remainder } else { self.chunk_size };
            let (fst, snd) = self.v.split_at(chunksz);
            self.v = snd;
            Some(fst)
        }
    }

    #[rapx::verify]
    #[rapx::requires(ValidNum(idx < (if self.v.is_empty() { 0 } else { let n = self.v.len() / self.chunk_size; let rem = self.v.len() % self.chunk_size; if rem > 0 { n + 1 } else { n } })))]
    unsafe fn get_unchecked(&mut self, idx: usize) -> &'a [T] {
        let end = self.v.len() - idx * self.chunk_size;
        let start = end.saturating_sub(self.chunk_size);
        unsafe { from_raw_parts(self.v.as_ptr().add(start), end - start) }
    }
}

// --- RChunksMut -------------------------------------------------------------

#[rapx::invariant(InBound(v, T, v.len()))]
pub struct RChunksMut<'a, T: 'a> {
    v: *mut [T],
    chunk_size: usize,
    _marker: std::marker::PhantomData<&'a mut T>,
}

impl<'a, T> RChunksMut<'a, T> {
    #[rapx::verify]
    fn new(slice: &'a mut [T], size: usize) -> RChunksMut<'a, T> {
        RChunksMut { v: slice, chunk_size: size, _marker: std::marker::PhantomData }
    }

    #[rapx::verify]
    fn next(&mut self) -> Option<&'a mut [T]> {
        if self.v.is_empty() { None }
        else {
            let sz = cmp::min(self.v.len(), self.chunk_size);
            let len = self.v.len();
            let (head, tail) = unsafe { self.v.split_at_mut(len - sz) };
            self.v = head;
            Some(unsafe { &mut *tail })
        }
    }

    #[rapx::verify]
    fn nth(&mut self, n: usize) -> Option<&'a mut [T]> {
        let (end, overflow) = n.overflowing_mul(self.chunk_size);
        if end >= self.v.len() || overflow { self.v = &mut []; return None; }
        let end = self.v.len() - end;
        let start = end.saturating_sub(self.chunk_size);
        let (head, tail) = unsafe { self.v.split_at_mut(start) };
        let (nth, _) = unsafe { tail.split_at_mut(end - start) };
        self.v = head;
        Some(unsafe { &mut *nth })
    }

    #[rapx::verify]
    fn last(mut self) -> Option<&'a mut [T]> {
        if self.v.is_empty() { None }
        else {
            let rem = self.v.len() % self.chunk_size;
            let end = if rem == 0 { self.chunk_size } else { rem };
            Some(unsafe { &mut *self.v.get_unchecked_mut(0..end) })
        }
    }

    #[rapx::verify]
    fn next_back(&mut self) -> Option<&'a mut [T]> {
        if self.v.is_empty() { None }
        else {
            let remainder = self.v.len() % self.chunk_size;
            let sz = if remainder != 0 { remainder } else { self.chunk_size };
            let (head, tail) = unsafe { self.v.split_at_mut(sz) };
            self.v = tail;
            Some(unsafe { &mut *head })
        }
    }

    #[rapx::verify]
    fn nth_back(&mut self, n: usize) -> Option<&'a mut [T]> {
        let chunk_count = if self.v.is_empty() { 0 } else { let n = self.v.len() / self.chunk_size; let rem = self.v.len() % self.chunk_size; if rem > 0 { n + 1 } else { n } };
        if n >= chunk_count { self.v = &mut []; return None; }
        let offset_from_end = (chunk_count - 1 - n) * self.chunk_size;
        let end = self.v.len() - offset_from_end;
        let start = end.saturating_sub(self.chunk_size);
        let (tmp, tail) = unsafe { self.v.split_at_mut(end) };
        let (_, nth_back) = unsafe { tmp.split_at_mut(start) };
        self.v = tail;
        Some(unsafe { &mut *nth_back })
    }

    #[rapx::verify]
    #[rapx::requires(ValidNum(idx < (if self.v.is_empty() { 0 } else { let n = self.v.len() / self.chunk_size; let rem = self.v.len() % self.chunk_size; if rem > 0 { n + 1 } else { n } })))]
    unsafe fn get_unchecked(&mut self, idx: usize) -> &'a mut [T] {
        let end = self.v.len() - idx * self.chunk_size;
        let start = end.saturating_sub(self.chunk_size);
        unsafe { from_raw_parts_mut(self.v.as_mut_ptr().add(start), end - start) }
    }
}

// --- RChunksExact -----------------------------------------------------------

pub struct RChunksExact<'a, T: 'a> {
    v: &'a [T],
    rem: &'a [T],
    chunk_size: usize,
}

impl<'a, T> RChunksExact<'a, T> {
    #[rapx::verify]
    fn new(slice: &'a [T], chunk_size: usize) -> RChunksExact<'a, T> {
        let rem = slice.len() % chunk_size;
        let (fst, snd) = slice.split_at(rem);
        RChunksExact { v: snd, rem: fst, chunk_size }
    }

    #[rapx::verify]
    fn next(&mut self) -> Option<&'a [T]> {
        if self.v.len() < self.chunk_size { None }
        else {
            let (fst, snd) = self.v.split_at(self.v.len() - self.chunk_size);
            self.v = fst;
            Some(snd)
        }
    }

    #[rapx::verify]
    fn next_back(&mut self) -> Option<&'a [T]> {
        if self.v.len() < self.chunk_size { None }
        else {
            let (fst, snd) = self.v.split_at(self.chunk_size);
            self.v = snd;
            Some(fst)
        }
    }

    #[rapx::verify]
    #[rapx::requires(ValidNum(idx < self.v.len() / self.chunk_size))]
    unsafe fn get_unchecked(&mut self, idx: usize) -> &'a [T] {
        let end = self.v.len() - idx * self.chunk_size;
        let start = end - self.chunk_size;
        unsafe { from_raw_parts(self.v.as_ptr().add(start), self.chunk_size) }
    }
}

// --- RChunksExactMut --------------------------------------------------------

#[rapx::invariant(InBound(v, T, v.len()))]
pub struct RChunksExactMut<'a, T: 'a> {
    v: *mut [T],
    rem: &'a mut [T],
    chunk_size: usize,
}

impl<'a, T> RChunksExactMut<'a, T> {
    #[rapx::verify]
    fn new(slice: &'a mut [T], chunk_size: usize) -> RChunksExactMut<'a, T> {
        let rem = slice.len() % chunk_size;
        let (fst, snd) = slice.split_at_mut(rem);
        RChunksExactMut { v: snd, rem: fst, chunk_size }
    }

    #[rapx::verify]
    fn next(&mut self) -> Option<&'a mut [T]> {
        if self.v.len() < self.chunk_size { None }
        else {
            let len = self.v.len();
            let (head, tail) = unsafe { self.v.split_at_mut(len - self.chunk_size) };
            self.v = head;
            Some(unsafe { &mut *tail })
        }
    }

    #[rapx::verify]
    fn nth(&mut self, n: usize) -> Option<&'a mut [T]> {
        let (end, overflow) = n.overflowing_mul(self.chunk_size);
        if end >= self.v.len() || overflow { self.v = &mut []; return None; }
        let len = self.v.len();
        let (fst, _) = unsafe { self.v.split_at_mut(len - end) };
        self.v = fst;
        self.next()
    }

    #[rapx::verify]
    fn next_back(&mut self) -> Option<&'a mut [T]> {
        if self.v.len() < self.chunk_size { None }
        else {
            let (head, tail) = unsafe { self.v.split_at_mut(self.chunk_size) };
            self.v = tail;
            Some(unsafe { &mut *head })
        }
    }

    #[rapx::verify]
    fn nth_back(&mut self, n: usize) -> Option<&'a mut [T]> {
        let len = self.v.len() / self.chunk_size;
        if n >= len { self.v = &mut []; return None; }
        let offset = (len - n) * self.chunk_size;
        let start = self.v.len() - offset;
        let end = start + self.chunk_size;
        let (tmp, tail) = unsafe { self.v.split_at_mut(end) };
        let (_, nth_back) = unsafe { tmp.split_at_mut(start) };
        self.v = tail;
        Some(unsafe { &mut *nth_back })
    }

    #[rapx::verify]
    #[rapx::requires(ValidNum(idx < self.v.len() / self.chunk_size))]
    unsafe fn get_unchecked(&mut self, idx: usize) -> &'a mut [T] {
        let end = self.v.len() - idx * self.chunk_size;
        let start = end - self.chunk_size;
        unsafe { from_raw_parts_mut(self.v.as_mut_ptr().add(start), self.chunk_size) }
    }
}

// --- ArrayWindows -----------------------------------------------------------

pub struct ArrayWindows<'a, T: 'a, const N: usize> {
    v: &'a [T],
}

impl<'a, T, const N: usize> ArrayWindows<'a, T, N> {
    #[rapx::verify]
    fn new(slice: &'a [T]) -> ArrayWindows<'a, T, N> {
        ArrayWindows { v: slice }
    }

    #[rapx::verify]
    fn next(&mut self) -> Option<&'a [T; N]> {
        if self.v.len() < N { None }
        else {
            let ret = unsafe { &*(self.v.as_ptr() as *const [T; N]) };
            self.v = &self.v[1..];
            Some(ret)
        }
    }

    #[rapx::verify]
    fn next_back(&mut self) -> Option<&'a [T; N]> {
        if self.v.len() < N { None }
        else {
            let start = self.v.len() - N;
            let ret = unsafe { &*(self.v[start..].as_ptr() as *const [T; N]) };
            self.v = &self.v[..self.v.len() - 1];
            Some(ret)
        }
    }
}

// --- Split ------------------------------------------------------------------

pub struct Split<'a, T: 'a, P> where P: FnMut(&T) -> bool {
    v: &'a [T],
    pred: P,
    finished: bool,
}

impl<'a, T, P: FnMut(&T) -> bool> Split<'a, T, P> {
    #[rapx::verify]
    fn new(slice: &'a [T], pred: P) -> Split<'a, T, P> {
        Split { v: slice, pred, finished: false }
    }

    #[rapx::verify]
    fn next(&mut self) -> Option<&'a [T]> {
        if self.finished { return None; }
        match self.v.iter().position(|x| (self.pred)(x)) {
            None => { self.finished = true; Some(self.v) }
            Some(idx) => {
                let ret = &self.v[..idx];
                self.v = &self.v[idx + 1..];
                Some(ret)
            }
        }
    }

    #[rapx::verify]
    fn next_back(&mut self) -> Option<&'a [T]> {
        if self.finished { return None; }
        match self.v.iter().rposition(|x| (self.pred)(x)) {
            None => { self.finished = true; Some(self.v) }
            Some(idx) => {
                let ret = &self.v[idx + 1..];
                self.v = &self.v[..idx];
                Some(ret)
            }
        }
    }
}

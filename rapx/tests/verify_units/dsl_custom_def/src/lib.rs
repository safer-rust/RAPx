#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use rapx_macros::def_contract;
use std::ptr::NonNull;

// ── 1. Basic def: a named contract combining primitives. ──────────────
#[def_contract]
fn my_safe_read(p: Ptr, T: Ty, n: Expr) -> bool {
    NonNull(p) && Align(p, T) && Allocated(p, T, n)
}

#[rapx::requires(my_safe_read(ptr, u8, len))]
pub unsafe fn read_byte(ptr: *const u8, len: usize) -> u8 {
    unsafe { *ptr }
}

#[rapx::verify]
pub fn sound_read(buf: &[u8]) -> u8 {
    unsafe { read_byte(buf.as_ptr(), buf.len()) }
}

// ── 2. size_of(T): the formal `T` is substituted by the call-site type. ──
#[def_contract]
fn layout_limit(p: Ptr, T: Ty, n: Expr) -> bool {
    ValidNum(size_of(T) * n <= isize::MAX)
}

#[rapx::requires(layout_limit(ptr, u32, len))]
unsafe fn require_layout_limit(ptr: *const u32, len: usize) {}

#[rapx::verify]
pub fn sound_layout_limit(data: &[u32]) {
    if data.len() <= 1024 {
        unsafe { require_layout_limit(data.as_ptr(), data.len()); }
    }
}

// ── 3. min(a, b): bracket-aware splitting + formal substitution. ─────────
#[def_contract]
fn bounded(n: Expr, cap: Expr) -> bool {
    ValidNum(min(n, cap) <= cap)
}

#[rapx::requires(bounded(x, y))]
unsafe fn require_bounded(x: usize, y: usize) {}

#[rapx::verify]
pub fn sound_bounded(x: usize, y: usize) {
    unsafe { require_bounded(x, y); }
}

// ── 4. p.unwrap_some(): the receiver is substituted by the field place. ──
#[def_contract]
fn some_aligned(h: Ptr, T: Ty) -> bool {
    Align(h.unwrap_some(), T)
}

struct Node {
    value: u32,
}

#[rapx::invariant(some_aligned(head, Node))]
struct List {
    head: Option<NonNull<Node>>,
}

impl List {
    #[rapx::verify]
    fn new() -> Self {
        List { head: None }
    }

    #[rapx::verify]
    fn push(&mut self, value: u32) {
        let node = Box::new(Node { value });
        self.head = Some(NonNull::from(Box::leak(node)));
    }
}

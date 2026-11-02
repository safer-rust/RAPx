#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(NonNull(_ptr), kind = "precond")]
unsafe fn require_nonnull(_ptr: *const u8) {}

// A single-implementor trait: its only impl returns a provably non-null pointer.
pub trait SingleSource {
    fn ptr(&self) -> *const u8;
}

struct Dangling;

impl SingleSource for Dangling {
    fn ptr(&self) -> *const u8 {
        std::ptr::NonNull::<u8>::dangling().as_ptr()
    }
}

// A multi-implementor trait: the default limit inlines one impl.
pub trait MultiSource {
    fn ptr(&self) -> *const u8;
}

struct Da;
struct Db;
struct Dc;
struct Dd;

impl MultiSource for Da {
    fn ptr(&self) -> *const u8 {
        std::ptr::NonNull::<u8>::dangling().as_ptr()
    }
}

impl MultiSource for Db {
    fn ptr(&self) -> *const u8 {
        std::ptr::NonNull::<u8>::dangling().as_ptr()
    }
}

impl MultiSource for Dc {
    fn ptr(&self) -> *const u8 {
        std::ptr::NonNull::<u8>::dangling().as_ptr()
    }
}

impl MultiSource for Dd {
    fn ptr(&self) -> *const u8 {
        std::ptr::null()
    }
}

// SOUND: the sole `SingleSource` impl is inlined, so `p = dangling()` is NonNull.
#[rapx::verify]
pub fn single_impl_sound(x: &dyn SingleSource) {
    let p = x.ptr();
    unsafe {
        require_nonnull(p);
    }
}

// SOUND (under the default limit of 1): the call is truncated to `Da`, so
// NonNull is proved. `Dd` returns null and would fail, but is dropped by the
// limit. With `--trait-impl-limit 4`, all impls are inlined and the null branch
// makes this UNSOUND.
#[rapx::verify]
pub fn multi_impl_truncated(x: &dyn MultiSource) {
    let p = x.ptr();
    unsafe {
        require_nonnull(p);
    }
}

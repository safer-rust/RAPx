// ============================================================
// RAPx builtin contract definitions (compound macros)
//
// Each compound is defined with Rust function syntax; its body is a
// boolean combination of the 21 primitive safety properties (see
// primitive-sp.md §2.2). Users can define new tags with #[def_contract]
// in their own crate using the same syntax.
// ============================================================

// ── Compound safety properties (primitive-sp.md §2.2) ──

/// The pointer can be safely dereferenced: in-bounds and within a live allocation.
fn Deref(p: Ptr, T: Ty, n: Expr) -> bool {
    Allocated(p, T, n) && InBound(p, T, n)
}

/// A valid pointer: vacuously true for ZSTs, otherwise Deref.
fn ValidPtr(p: Ptr, T: Ty, n: Expr) -> bool {
    Size(T, 0) || Deref(p, T, n)
}

/// A raw pointer meets all requirements for sound &/&mut conversion:
/// initialized, aligned, no aliasing conflict.
fn Ptr2Ref(p: Ptr, T: Ty) -> bool {
    Init(p, T, 1) && Align(p, T) && Alias(p)
}

/// The pointer matches the layout's size/alignment from a prior allocation.
fn Layout(p: Ptr, l: Ptr) -> bool {
    Allocated(p)
}

// ============================================================
// RAPx builtin contract definitions (compound properties)
//
// Each compound is defined as a `Name(params) { body }` block whose body is a
// boolean combination of the primitive safety properties (see
// primitive-sp.md §2.2). Users can define new tags with the `pred!` macro in
// their own crate using the same syntax.
// ============================================================

// ── Compound safety properties (primitive-sp.md §2.2) ──

/// The pointer can be safely dereferenced: in-bounds and within a live allocation.
Deref(p: Ptr, T: Ty, n: Expr) { Allocated(p, T, n) && InBound(p, T, n) }

/// A valid pointer: vacuously true for ZSTs, otherwise Deref.
ValidPtr(p: Ptr, T: Ty, n: Expr) { Size(T, 0) || Deref(p, T, n) }

/// A raw pointer meets all requirements for sound `&T`/`&mut T` conversion:
/// initialized, non-null, dereferenceable, aligned, no aliasing conflict.
Ptr2Ref(p: Ptr, T: Ty) { Init(p, T, 1) && NonNull(p) && ValidPtr(p, T, 1) && Align(p, T) && Alias(p) }

/// A raw pointer meets all requirements for sound `&MaybeUninit<T>` /
/// `&mut MaybeUninit<T>` conversion: type-valid (the content need *not* be
/// initialized — `Init` is deliberately absent), non-null, dereferenceable,
/// aligned, no aliasing conflict.
Ptr2RefUninit(p: Ptr, T: Ty) { Typed(p, T) && NonNull(p) && ValidPtr(p, T, 1) && Align(p, T) && Alias(p) }

/// The pointer matches the `Layout` it was allocated with (`realloc`/`dealloc`
/// require "the same layout that was used to allocate the block"): aligned to
/// `layout.align()`, and pointing at `layout.size()` heap bytes.
Layout(p: Ptr, layout: Ptr) { ValidNum(p % layout.align == 0) && Allocated(p, u8, layout.size, global) }

/// A pointer to an unsized value whose metadata is read (`size_of_val`,
/// `align_of_val`, `for_value_raw`, `min_align_of_val`). Enforces non-null;
/// the pointee's alignment/validity is not checked because the single-argument
/// form carries no element type.
ValidTraitObj(p: Ptr) { NonNull(p) }

/// `InBound` with ZST-aware element counting: `0` elements when `T` is a
/// zero-sized type (so the bounds check is vacuous and never divides by
/// `size_of(T)`), otherwise `(end_or_len - ptr) / size_of(T)` elements.
ZstAwareInBound(ptr: Ptr, T: Ty, end_or_len: Expr) { InBound(ptr, T, if size_of(T) == 0 { 0 } else { (end_or_len - ptr) / size_of(T) }) }

// ── Auto-trait (Send/Sync) type-level compounds ──

/// A raw pointer field `ptr` that is `Allocated` and `Owning` (discharged by the
/// struct's `#[rapx::invariant(Allocated(ptr))]` / `#[rapx::invariant(Owning(ptr))]`
/// annotations) and whose updates are read-only (`NoInternalMut`), exclusive
/// (`UniInternalMut`), or atomic (`AtomicUpdate`).
TamedRawPtr(T: Ty, ptr: Ptr) { Allocated(ptr, T, 1) && Owning(ptr) && (NoInternalMut(T) || UniInternalMut(T) || AtomicUpdate(T)) }

// ============================================================
// RAPx builtin subsumption rules (primitive safety properties)
//
// Unlike `std-compound-properties.rs` (which defines `Name ≡ body`
// *equivalences*), this file declares *one-way weakenings*: asserting the
// left-hand primitive as a fact also asserts the right-hand conjunction.
// The syntax is the same `Name(params) { body }` shape, re-parsed by
// `parse_compounds`, but the head is an existing primitive tag and the body is
// a pure conjunction of weaker primitive calls (parameters map positionally to
// the head's arguments).
// ============================================================

/// Reading a valid `T` value at `p` requires the pointer to be non-null, to
/// point at a live allocation, and to be in-bounds, and entails the type
/// invariant — so `Init(p, T, n)` also asserts `NonNull(p) ∧ Allocated(p, T, n)
/// ∧ InBound(p, T, n) ∧ Typed(p, T)`.
Init(p: Ptr, T: Ty, n: Expr) { NonNull(p) && Allocated(p, T, n) && InBound(p, T, n) && Typed(p, T) }

/// A pointer into a live allocation is non-null (a null address is not
/// allocated by any allocator).
Allocated(p: Ptr, T: Ty, n: Expr) { NonNull(p) }

/// A pointer to a typed value is non-null (a typed value cannot live at null).
Typed(p: Ptr, T: Ty) { NonNull(p) }

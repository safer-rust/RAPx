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
//
// Only *content/type-hierarchy* weakenings live here.  The pointer-validity
// primitives (`NonNull`, `Allocated`, `InBound`) are deliberately NOT implied
// by `Init`/`Typed`: they are orthogonal requirements that contracts state
// explicitly (e.g. the `Ptr2Ref` compound).  See primitive-sp.md §3.3.3/§3.3.5.
// ============================================================

/// Reading a valid `T` value at `p` entails the type invariant, so
/// `Init(p, T, n)` also asserts `Typed(p, T)` — but *not* the pointer-validity
/// primitives (`NonNull`/`Allocated`/`InBound`), which are orthogonal.
Init(p: Ptr, T: Ty, n: Expr) { Typed(p, T) }

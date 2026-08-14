// ============================================================
// RAPx user extension contracts (compound macros)
//
// Define your own compound contracts here as `Name(params) { body }` blocks
// (boolean combinations of the 21 primitives). They take effect after
// recompiling rapx. This complements the in-crate `pred!` path: here is where
// a rapx deployment pre-seeds extensions.
//
// Same syntax as std-contracts.rs:
//
// MyTag(p: Ptr, T: Ty, n: Expr) { NonNull(p) && Align(p, T) && Allocated(p, T, n) }
// ============================================================

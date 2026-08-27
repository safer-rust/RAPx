// ============================================================
// RAPx user extension contracts (compound properties)
//
// Define your own compound properties here as `Name(params) { body }` blocks
// (boolean combinations of the primitives). They take effect after
// recompiling rapx. This complements the in-crate `pred!` path: here is where
// a rapx deployment pre-seeds extensions.
//
// Same syntax as std-compound-properties.rs:
//
// MyTag(p: Ptr, T: Ty, n: Expr) { NonNull(p) && Align(p, T) && Allocated(p, T, n) }
// ============================================================

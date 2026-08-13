// ============================================================
// RAPx user extension contracts (compound macros)
//
// Define your own compound contracts here with Rust function syntax
// (boolean combinations of the 21 primitives). They take effect after
// recompiling rapx. This complements the in-crate `#[def_contract]` path:
// here is where a rapx deployment pre-seeds extensions.
//
// Same syntax as std-contracts.rs:
//
// fn MyTag(p: Ptr, T: Ty, n: Expr) -> bool {
//     NonNull(p) && Align(p, T) && Allocated(p, T, n)
// }
// ============================================================

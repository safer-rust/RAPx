/// Centralized compatibility shims for compiler API differences across nightly
/// versions.
///
/// When a type or function moves between modules or changes interface across
/// rustc versions, add a re-export here (gated by `#[cfg]`).  All other
/// modules import from this crate instead of writing their own `#[cfg]` blocks.
///
/// # How to add a new compat item
///
/// 1. Add a cfg flag in `build.rs` (e.g. `rustc_foo_moved`).
/// 2. Register it with `emit_check_cfg` in `build.rs`.
/// 3. Add the re-export below.
/// 4. Update call-sites to `use crate::compat::Foo;`.
pub use rustc_hash::FxHashMap;
pub use rustc_hash::FxHashSet;

/// `Spanned` was moved from `rustc_span::source_map` to `rustc_span` root
/// in rustc 1.97.
#[cfg(rustc_spanned_at_root)]
pub use rustc_span::Spanned;
#[cfg(not(rustc_spanned_at_root))]
pub use rustc_span::source_map::Spanned;

//! Procedural macros for RAPx contract definitions.
//!
//! The `#[def_contract]` attribute turns a Rust-function-shaped contract into a
//! `#[rapx::def_contract("...")]` tool attribute that the RAPx verifier reads
//! from the crate's MIR/HIR metadata.
//!
//! ```rust
//! #![register_tool(rapx)]
//! use rapx_macros::def_contract;
//!
//! #[def_contract]
//! fn my_safe_read(p: Ptr, T: Ty, n: Expr) -> bool {
//!     NonNull(p) && Align(p, T) && Allocated(p, T, n)
//! }
//! ```
//!
//! The body is a boolean combination of the 21 primitive safety properties
//! (`NonNull`, `Align`, `Allocated`, ...) and other `def`s.  The function is
//! *not* compiled as Rust — it is serialized into a `def` string that the
//! verifier expands at analysis time.

use proc_macro::TokenStream;
use quote::quote;

/// Serialize a Rust-function-shaped contract into a `#[rapx::def_contract]`
/// tool attribute carrying the function's source text.  The RAPx verifier
/// parses this text with `syn` at analysis time.
#[proc_macro_attribute]
pub fn def_contract(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let item_str = item.to_string();
    quote! {
        #[rapx::def_contract(#item_str)]
        const _: () = ();
    }
    .into()
}

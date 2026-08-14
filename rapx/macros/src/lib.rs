//! Procedural macros for RAPx contract definitions.
//!
//! The `pred!` macro serializes a named compound contract into a
//! `#[rapx::def_contract("...")]` tool attribute that the RAPx verifier reads
//! from the crate's MIR/HIR metadata.
//!
//! ```rust
//! #![register_tool(rapx)]
//! use rapx_macros::pred;
//!
//! pred!(my_safe_read(p: Ptr, T: Ty, n: Expr) { NonNull(p) && Align(p, T) && Allocated(p, T, n) });
//! ```
//!
//! The body is a boolean combination of the 21 primitive safety properties
//! (`NonNull`, `Align`, `Allocated`, ...) and other `def`s.  The expression is
//! *not* compiled as Rust — it is serialized into a `def` string that the
//! verifier expands at analysis time.

use proc_macro::TokenStream;
use quote::quote;

/// Serialize a `Name(params) { body }` contract block into a
/// `#[rapx::def_contract]` tool attribute carrying the block's source text.
/// The RAPx verifier parses this text at analysis time.
#[proc_macro]
pub fn pred(input: TokenStream) -> TokenStream {
    let def_str = input.to_string();
    quote! {
        #[rapx::def_contract(#def_str)]
        const _: () = ();
    }
    .into()
}

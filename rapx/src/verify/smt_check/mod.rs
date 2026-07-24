//! SMT checking package for the staged verifier.
//!
//! The package is split into:
//!
//! - `common`: the shared SMT entry point, query/result types, and term model.
//! - one SP-specific module per safety property family, such as `align`.
//!
//! SP-specific modules should only lower verifier properties into common SMT
//! obligations. They should not construct independent solver APIs.

mod alias;
mod align;
mod alive;
mod allocated;
pub(crate) mod common;
mod deref;
mod field_invariant;
mod model;
mod in_bound;
mod init;
mod non_null;
mod non_overlap;
mod owning;
mod provenance;
mod ptr2ref;
mod split_transmute;
mod typed;
mod valid_cstr;
mod valid_num;
mod valid_ptr;
mod valid_transmute;

pub use common::{SmtCheckResult, SmtChecker, SmtObligation, SmtQuery};

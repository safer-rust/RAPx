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
mod allocated;
mod common;
mod deref;
mod in_bound;
mod init;
mod non_null;
mod non_overlap;
mod valid_num;
mod valid_ptr;

pub use common::{SmtCheckResult, SmtChecker, SmtObligation, SmtQuery};

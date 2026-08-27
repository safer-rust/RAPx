//! pest parser for the contract DSL.
//!
//! The grammar (`grammar.pest`) is the single source of truth for the
//! contract-DSL surface.  This module only wires the derived parser; the
//! semantic conversion (`Pairs<Rule>` → `ContractExpr` / `Property`) lives in
//! `pest_conv.rs`.

use pest_derive::Parser;

/// Parser derived from `grammar.pest`.
#[derive(Parser)]
#[grammar = "verify/contract/grammar.pest"]
pub(crate) struct ContractParser;



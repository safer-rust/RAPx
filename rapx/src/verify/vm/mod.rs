//! Symbolic MIR Virtual Machine.
//!
//! This module replaces the pattern-matching `ForwardVerifier` with a
//! semantic MIR executor.  Instead of deriving ad-hoc `StateFact`s from
//! MIR patterns, the VM executes retained MIR items and directly builds
//! symbolic state (`VmState`) with Z3 terms for every value.

pub(crate) mod alias;
pub(crate) mod alias_hazard;
pub(crate) mod alias_tree;
pub(crate) mod arithmetic;
pub(crate) mod call;
pub(crate) mod container;
pub(crate) mod contracts;
pub(crate) mod contract_eval;
pub(crate) mod display;
pub(crate) mod effects;
pub(crate) mod comparison_simulator;
pub(crate) mod exec;
pub(crate) mod iterator;
pub(crate) mod materialize;
pub(crate) mod memory;
pub(crate) mod method_cache;
pub(crate) mod parameters;
pub(crate) mod query;
pub(crate) mod range;
pub(crate) mod region;
pub(crate) mod rules;
pub(crate) mod state;

pub(crate) use self::state::VmState;

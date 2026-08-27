//! The staged verification pipeline.
//!
//! Contract-based, path-sensitive verification of safety properties: collect
//! targets and contracts, extract SCC-aware paths, slice them backward, execute
//! the relevant MIR symbolically, and discharge each property with Z3.

pub(crate) mod alias_hazard;
pub(crate) mod call_summary;
pub(crate) mod contract;
pub(crate) mod def_use;
pub(crate) mod display;
pub(crate) mod driver;
pub(crate) mod engine;
pub(crate) mod loop_sensitivity;
pub(crate) mod path_extractor;

pub(crate) mod property_checker;
pub(crate) mod report;
pub(crate) mod slicer;
pub(crate) mod target;
pub(crate) mod cstr_const_bytes;

pub(crate) mod vm;

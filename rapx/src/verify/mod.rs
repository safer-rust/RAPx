//! The staged verification pipeline.
//!
//! Contract-based, path-sensitive verification of safety properties: collect
//! targets and contracts, extract SCC-aware paths, slice them backward, execute
//! the relevant MIR symbolically, and discharge each property with Z3.

pub mod alias_hazard;
pub mod call_summary;
pub mod contract;
pub mod def_use;
pub mod display;
pub mod driver;
pub mod engine;
pub mod loop_sensitivity;
pub mod path_extractor;

pub mod property_checker;
pub mod report;
pub mod slicer;
pub mod target;
pub mod cstr_const_bytes;

pub mod vm;

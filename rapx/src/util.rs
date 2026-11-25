//! Shared logging, source, filesystem, and compiler utilities.

#[macro_use]
pub mod log;
pub(crate) mod def_path;
pub(crate) mod def_use;
pub(crate) mod draw_dot;
pub mod fs;
pub(crate) mod fn_info;
pub(crate) mod mir_scan;
pub(crate) mod mir_utils;
pub(crate) mod name;
pub(crate) mod path;
pub(crate) mod show_mir;
pub mod source;
pub mod span;
pub(crate) mod resolve;

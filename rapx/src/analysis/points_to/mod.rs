//! Unified points-to and value-flow graph.
//!
//! The [`graph::PtsGraph`] provides a path-sensitive points-to representation
//! used by both the MoP alias analysis, SafeDrop, and the verify/SMT pipeline.
//! It records pointer-to-source relationships together with value-copy tracking
//! and union-find alias partitions.
//!
//! # Slot registration
//! [`builder::from_body`] pre-registers all MIR locals and their type-determined
//! field slots up to configurable depth limits.
//!
//! # PlaceKey adapters
//! `PtsGraph` exposes PlaceKey-oriented methods (`insert_place_edge`,
//! `get_place_source`, `resolve_place`, `place_edges`) for consumers in the
//! verify pipeline that work with `crate::helpers::def_use::PlaceKey` rather
//! than [`slot::Slot`].
//!
//! # Edge sources
//! * `Rvalue::Ref`     — `&_x`  / `&mut _x`   → `_x`
//! * `Rvalue::RawPtr`  — `&raw const/mut _x`  → `_x`
//! * `ptr::add/sub/offset` / `as_ptr` / `into_raw` / `cast` / `from_raw_parts`
//!   / NonNull constructors / ownership reconstruction — return → arg 0

pub mod builder;
pub mod graph;
pub mod slot;

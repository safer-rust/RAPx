//! Property-specific verification modules for Senryx contracts.
//!
//! The parent module only wires checker modules into the crate. Each child file
//! owns one safety-property family and implements the corresponding
//! `BodyVisitor` APIs used by call-site dispatch.

/// Alignment contract checks and alignment-state refinement.
pub mod align;
/// Boundary, length and zero-sized-type helper checks.
pub mod bounds;
/// Initialization contract checks.
pub mod init;
/// Miscellaneous property placeholders that still need precise models.
pub mod misc;
/// Non-null pointer checks.
pub mod non_null;
/// Composite pointer validity and dereferenceability checks.
pub mod pointer;
/// Type-compatibility checks.
pub mod typed;

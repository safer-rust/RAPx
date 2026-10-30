//! Owned SafeDrop output records for AI review.
//!
//! These types define the JSON format only; collecting compiler state and writing
//! reports are separate steps. Source spans and MIR IDs must be converted while
//! the compiler context is alive.

use std::num::NonZeroU32;

use serde::{Deserialize, Serialize};

/// The same bug kinds used by SafeDrop's in-memory bug records.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BugType {
    UseAfterFree,
    DoubleFree,
    DanglingPointer,
    UseAfterFreeAndDoubleFree,
}

/// Analysis status for one compilation unit, independent of the Cargo exit code.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RunStatus {
    /// Requested analysis finished; fixed capability boundaries still apply.
    Completed,
    Partial,
    Skipped,
}

/// One compilation unit. Having no finding files is meaningful only together
/// with the execution status and limitations; it is not a safety proof.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SafeDropProfile {
    /// Crate name and target kind, e.g. demo-lib or demo-bin.
    pub unit: String,
    pub rapx_version: String,
    pub rustc_version: Option<String>,
    pub working_directory: String,
    pub status: RunStatus,
    pub analyzed_functions: usize,
    /// Events actually observed in this run; fixed capability boundaries live in the skill.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub limitations: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SafeDropFunction {
    pub source: Option<String>,
    /// The whole function MIR included in each finding file for this function.
    pub mir: String,
}

/// A candidate reported by SafeDrop, kept separate from the AI's later verdict.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SafeDropFinding {
    /// Identity within this compilation unit; not a cross-run matching fingerprint.
    /// Format: `sd-<crate name>-<target kind>-<zero-based report index>`.
    pub id: String,
    /// Full function name corresponding to the file's function context.
    pub function: String,
    pub bug_type: BugType,
    /// Original SafeDrop heuristic (currently 0, 50, or 99), not a probability.
    pub confidence: usize,
    pub during_unwind: bool,
    /// The span recorded in TyBug; it may cover the whole function rather than
    /// the exact triggering statement. Unresolved locations remain None.
    pub location: Option<SourceLocation>,
    pub drop_site: SafeDropSite,
    /// A use, a second release, or a dangling value at function exit, depending
    /// on bug_type. Exit checks may have no recorded basic block.
    pub trigger_site: SafeDropSite,
    /// Representative state captured at detection, before DFS rollback.
    pub witness: Option<SafeDropWitness>,
}

/// SafeDrop's selected path prefix and relevant abstract state, not a proven
/// executable counterexample. Value IDs are scoped to this function and run.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SafeDropWitness {
    pub path_prefix: Vec<usize>,
    /// Drop-state propagation through values; this is not a CFG path.
    pub drop_propagation: Vec<usize>,
    pub values: Vec<SafeDropValue>,
    /// Move destination/source value IDs relevant to the captured values.
    pub owner_transfers: Vec<(usize, usize)>,
    /// Snapshot events collected into the profile when writing, not repeated in JSON.
    #[serde(skip)]
    pub limitations: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SafeDropValue {
    pub value_index: usize,
    pub local: usize,
    pub name: Option<String>,
    /// Type of the MIR local; field projections are described separately.
    pub local_type: Option<String>,
    pub fields: Vec<usize>,
    pub kind: Option<String>,
    pub may_drop: bool,
    pub needs_drop: bool,
    pub is_dropped: bool,
    pub has_dropped_field: bool,
    /// Results of may_alias, not proofs of concrete address equality.
    pub may_alias: Vec<usize>,
    /// Debug names of abstract locations (Slot/Null), not concrete addresses.
    pub direct_pointees: Vec<String>,
}

/// A SafeDrop LocalSpot with its best available source mapping.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SafeDropSite {
    pub local: Option<usize>,
    pub basic_block: Option<usize>,
    /// May be a block-level span; it does not assert an exact event position.
    pub location: Option<SourceLocation>,
}

/// A mapped source span with one-based character coordinates, not byte offsets.
/// Unknown spans use None at the call site, never zero coordinates.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceLocation {
    pub path: String,
    pub start_line: NonZeroU32,
    pub start_column: NonZeroU32,
    /// Exclusive end position.
    pub end_line: NonZeroU32,
    pub end_column: NonZeroU32,
    /// Digest of the whole source file, including its algorithm, when captured.
    pub source_digest: Option<String>,
}

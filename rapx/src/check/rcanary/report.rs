//! Owned rCanary diagnostics and context for review outside the compiler.

use std::{collections::BTreeMap, num::NonZeroU32};

use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RunStatus {
    Completed,
    Partial,
    Skipped,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RCanaryProfile {
    pub unit: String,
    pub rapx_version: String,
    pub rustc_version: Option<String>,
    pub working_directory: String,
    pub status: RunStatus,
    pub analyzed_functions: usize,
    pub skipped_functions: usize,
    pub checked_returns: usize,
    pub finding_count: usize,
    pub solver_timeout_ms: u64,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub limitations: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RCanaryFunction {
    pub source: Option<String>,
    pub mir: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SourceLocation {
    pub path: String,
    pub start_line: NonZeroU32,
    pub start_column: NonZeroU32,
    /// Exclusive end position; coordinates are one-based characters.
    pub end_line: NonZeroU32,
    pub end_column: NonZeroU32,
    pub source_digest: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BugType {
    MemoryLeak,
}

/// One warning at a return check, not a proven leaking allocation or path.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RCanaryFinding {
    /// Unit-local identity, not a stable cross-run fingerprint.
    pub id: String,
    pub function: String,
    pub bug_type: BugType,
    pub location: Option<SourceLocation>,
    pub return_site: RCanarySite,
    /// Calls matching rCanary's owner-to-pointer/reference heuristic so far.
    /// These are not proven allocation sites or all on a single execution path.
    pub source_sites: Vec<RCanarySite>,
    pub solver: SolverEvidence,
    pub locals: Vec<RCanaryLocal>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RCanarySite {
    pub basic_block: usize,
    pub location: Option<SourceLocation>,
    pub mir: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SolverEvidence {
    pub result: String,
    /// Actual asserted solver constraints, without the goal's debug markers.
    /// No model exists for unsat; an unsat core is not collected.
    pub constraints: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RCanaryLocal {
    pub local: usize,
    pub name: Option<String>,
    pub local_type: String,
    pub state: String,
    pub bit_width: usize,
    /// Symbolic bit-vector expression, not a concrete residual allocation.
    pub ownership_bits: Option<String>,
    pub layout: Vec<String>,
    pub taint: Vec<String>,
    /// Whether this local was required to be zero by this return check.
    pub checked_at_return: bool,
}

/// In-memory aggregation only; never serialized as a single large report.
#[derive(Default)]
pub(crate) struct AnalysisReport {
    pub functions: BTreeMap<String, RCanaryFunction>,
    pub findings: Vec<RCanaryFinding>,
    pub analyzed_functions: usize,
    pub skipped_functions: usize,
    pub checked_returns: usize,
    pub limitations: Vec<String>,
}

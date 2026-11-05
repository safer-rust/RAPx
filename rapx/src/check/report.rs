//! Shared metadata for package-local analyzer reports. Evidence stays analyzer-specific.

use std::{env, process::Command};

use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Analyzer {
    Safedrop,
    Rcanary,
    Opt,
}

/// Completion within the analyzer's model, independent of the Cargo exit code.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RunStatus {
    Completed,
    Partial,
    Skipped,
}

/// Flattened into each analyzer's profile.json; written after all finding files.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReportProfile {
    pub analyzer: Analyzer,
    pub unit: String,
    pub rapx_version: String,
    pub rustc_version: Option<String>,
    pub working_directory: String,
    pub status: RunStatus,
    pub analyzed_functions: usize,
    pub finding_count: usize,
    /// Events observed in this run; fixed capability boundaries belong in the skill.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub limitations: Vec<String>,
}

impl ReportProfile {
    pub fn new(
        analyzer: Analyzer,
        unit: String,
        status: RunStatus,
        analyzed_functions: usize,
        finding_count: usize,
        limitations: Vec<String>,
    ) -> Self {
        Self {
            analyzer,
            unit,
            rapx_version: env!("CARGO_PKG_VERSION").into(),
            rustc_version: Command::new("rustc")
                .arg("--version")
                .output()
                .ok()
                .filter(|out| out.status.success())
                .map(|out| String::from_utf8_lossy(&out.stdout).trim().to_owned()),
            working_directory: env::current_dir()
                .expect("Current working directory invalid.")
                .to_string_lossy()
                .into_owned(),
            status,
            analyzed_functions,
            finding_count,
            limitations,
        }
    }
}

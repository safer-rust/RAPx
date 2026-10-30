//! SafeDrop report directories and JSON file I/O.

use std::{
    collections::BTreeMap,
    env, fs, io,
    path::{Path, PathBuf},
};

use serde::Serialize;

use super::report::{SafeDropFinding, SafeDropFunction, SafeDropProfile};

#[derive(Serialize)]
struct FindingReport<'a> {
    function: &'a SafeDropFunction,
    finding: &'a SafeDropFinding,
}

/// Create this unit's directory in its Cargo package, preserving existing output.
pub fn create_unit_directory(unit: &str) -> io::Result<Option<PathBuf>> {
    if !valid_name(unit) {
        return Err(io::Error::other("Invalid SafeDrop crate/target name"));
    }
    // Cargo already provides the package directory, even when invoked elsewhere.
    let crate_directory = match env::var_os("CARGO_MANIFEST_DIR") {
        Some(path) => PathBuf::from(path),
        None => env::current_dir()?,
    };
    let directory = crate_directory.join(unit);
    match fs::create_dir(&directory) {
        Ok(()) => Ok(Some(directory)),
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
            rap_warn!(
                "SafeDrop report directory {} already exists; skipping analysis for {unit}. Move the existing directory before running a fresh analysis.",
                directory.display()
            );
            Ok(None)
        }
        Err(error) => Err(error),
    }
}

/// Publish the profile only after every self-contained finding file was written.
pub fn write_reports(
    directory: &Path,
    mut profile: SafeDropProfile,
    functions: &BTreeMap<String, SafeDropFunction>,
    mut findings: Vec<SafeDropFinding>,
) -> io::Result<()> {
    if !valid_name(&profile.unit) {
        return Err(io::Error::other("Invalid SafeDrop crate/target name"));
    }
    for (function, context) in functions {
        if context.source.is_none() {
            profile
                .limitations
                .push(format!("{function}: source_unavailable"));
        }
    }
    for (index, finding) in findings.iter_mut().enumerate() {
        finding.id = format!("sd-{}-{index}", profile.unit);
        let context = functions.get(&finding.function).ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                "SafeDrop function context is missing",
            )
        })?;
        if finding.location.is_none() {
            profile
                .limitations
                .push(format!("{}: source_location_unavailable", finding.id));
        }
        match &finding.witness {
            Some(witness) => profile.limitations.extend(
                witness
                    .limitations
                    .iter()
                    .map(|event| format!("{}: {event}", finding.id)),
            ),
            None => profile
                .limitations
                .push(format!("{}: witness_unavailable", finding.id)),
        }
        let report = FindingReport {
            function: context,
            finding,
        };
        fs::write(
            directory.join(format!("{}.json", finding.id)),
            serde_json::to_vec_pretty(&report).map_err(io::Error::other)?,
        )?;
    }
    fs::write(
        directory.join("profile.json"),
        serde_json::to_vec_pretty(&profile).map_err(io::Error::other)?,
    )
}

fn valid_name(name: &str) -> bool {
    !name.is_empty()
        && name
            .chars()
            .all(|c| c.is_alphanumeric() || matches!(c, '_' | '-'))
}

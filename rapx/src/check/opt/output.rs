//! Package-local opt reports for review by the current AI session.

use std::{
    env, fs, io,
    path::{Path, PathBuf},
};

use serde::Serialize;

use crate::check::report::Analyzer;

use super::report::{OptFinding, OptProfile};

#[derive(Serialize)]
struct FindingReport<'a> {
    finding: &'a OptFinding,
}

pub fn create_unit_directory(unit: &str) -> io::Result<PathBuf> {
    let package = env::var_os("CARGO_MANIFEST_DIR")
        .map(PathBuf::from)
        .map_or_else(env::current_dir, Ok)?;
    create_directory(&package, unit)
}

fn create_directory(package: &Path, unit: &str) -> io::Result<PathBuf> {
    if !valid_name(unit) {
        return Err(io::Error::other("Invalid opt crate/target name"));
    }
    // Separate analyzers can inspect the same package without report collisions.
    let directory = package.join(format!("opt-{unit}"));
    match fs::create_dir(&directory) {
        Ok(()) => Ok(directory),
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => Err(io::Error::new(
            error.kind(),
            format!(
                "opt report path {} already exists; cannot start a fresh analysis for {unit}. Move the existing path before running again.",
                directory.display()
            ),
        )),
        Err(error) => Err(error),
    }
}

/// The profile is a completion marker, published only after every finding file.
pub fn write_reports(
    directory: &Path,
    mut profile: OptProfile,
    mut findings: Vec<OptFinding>,
) -> io::Result<()> {
    if profile.common.analyzer != Analyzer::Opt
        || !valid_name(&profile.common.unit)
        || profile.common.finding_count != findings.len()
    {
        return Err(io::Error::other("Invalid opt report profile"));
    }
    findings.sort_by(|a, b| {
        (
            &a.function,
            &a.rule_id,
            &a.file,
            a.line_start,
            a.annotations.first().map(|a| a.range.start),
        )
            .cmp(&(
                &b.function,
                &b.rule_id,
                &b.file,
                b.line_start,
                b.annotations.first().map(|a| a.range.start),
            ))
    });
    for (index, finding) in findings.iter_mut().enumerate() {
        finding.id = format!("opt-{}-{index}", profile.common.unit);
        if finding.file == "<unknown>"
            || finding
                .annotations
                .iter()
                .any(|a| a.file == "<unknown>" || a.range.is_empty())
        {
            profile
                .common
                .limitations
                .push(format!("{}: source_location_unavailable", finding.id));
        }
        fs::write(
            directory.join(format!("{}.json", finding.id)),
            serde_json::to_vec_pretty(&FindingReport { finding }).map_err(io::Error::other)?,
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

//! Package-local opt reports for review by the current AI session.

use std::{
    env, fs, io,
    path::{Path, PathBuf},
};

use super::report::{OptFinding, OptProfile};

pub fn create_unit_directory(unit: &str) -> io::Result<Option<PathBuf>> {
    let package = env::var_os("CARGO_MANIFEST_DIR")
        .map(PathBuf::from)
        .map_or_else(env::current_dir, Ok)?;
    create_directory(&package, unit)
}

fn create_directory(package: &Path, unit: &str) -> io::Result<Option<PathBuf>> {
    if !valid_name(unit) {
        return Err(io::Error::other("Invalid opt crate/target name"));
    }
    // Separate analyzers can inspect the same package without report collisions.
    let directory = package.join(format!("opt-{unit}"));
    match fs::create_dir(&directory) {
        Ok(()) => Ok(Some(directory)),
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
            rap_warn!(
                "opt report directory {} already exists; skipping analysis for {unit}. Move the existing directory before running a fresh analysis.",
                directory.display()
            );
            Ok(None)
        }
        Err(error) => Err(error),
    }
}

/// The profile is a completion marker, published only after every finding file.
pub fn write_reports(
    directory: &Path,
    mut profile: OptProfile,
    mut findings: Vec<OptFinding>,
) -> io::Result<()> {
    if !valid_name(&profile.unit) || profile.finding_count != findings.len() {
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
        finding.id = format!("opt-{}-{index}", profile.unit);
        if finding.file == "<unknown>"
            || finding
                .annotations
                .iter()
                .any(|a| a.file == "<unknown>" || a.range.is_empty())
        {
            profile
                .limitations
                .push(format!("{}: source_location_unavailable", finding.id));
        }
        fs::write(
            directory.join(format!("{}.json", finding.id)),
            serde_json::to_vec_pretty(finding).map_err(io::Error::other)?,
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

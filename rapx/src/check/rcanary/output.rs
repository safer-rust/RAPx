//! Package-local rCanary output, isolated from SafeDrop reports.

use std::{
    env, fs, io,
    path::{Path, PathBuf},
};

use serde::Serialize;

use super::report::{AnalysisReport, RCanaryFinding, RCanaryFunction, RCanaryProfile};

#[derive(Serialize)]
struct FindingReport<'a> {
    function: &'a RCanaryFunction,
    finding: &'a RCanaryFinding,
}

pub fn create_unit_directory(unit: &str) -> io::Result<Option<PathBuf>> {
    if !valid_name(unit) {
        return Err(io::Error::other("Invalid rCanary crate/target name"));
    }
    let package = env::var_os("CARGO_MANIFEST_DIR")
        .map(PathBuf::from)
        .map_or_else(env::current_dir, Ok)?;
    let directory = package.join(format!("rcanary-{unit}"));
    match fs::create_dir(&directory) {
        Ok(()) => Ok(Some(directory)),
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
            rap_warn!(
                "rCanary report directory {} already exists; skipping analysis for {unit}. Move the existing directory before running a fresh analysis.",
                directory.display()
            );
            Ok(None)
        }
        Err(error) => Err(error),
    }
}

/// The profile is a completion marker, written only after every finding.
pub(crate) fn write_reports(
    directory: &Path,
    mut profile: RCanaryProfile,
    mut report: AnalysisReport,
) -> io::Result<()> {
    if !valid_name(&profile.unit) || profile.finding_count != report.findings.len() {
        return Err(io::Error::other("Invalid rCanary report profile"));
    }
    for (name, context) in &report.functions {
        if context.source.is_none() {
            profile
                .limitations
                .push(format!("{name}: source_unavailable"));
        }
    }
    for (index, finding) in report.findings.iter_mut().enumerate() {
        finding.id = format!("rc-{}-{index}", profile.unit);
        let context = report.functions.get(&finding.function).ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                "rCanary function context is missing",
            )
        })?;
        if finding.location.is_none()
            || finding.return_site.location.is_none()
            || finding
                .source_sites
                .iter()
                .any(|site| site.location.is_none())
        {
            profile
                .limitations
                .push(format!("{}: source_location_unavailable", finding.id));
        }
        fs::write(
            directory.join(format!("{}.json", finding.id)),
            serde_json::to_vec_pretty(&FindingReport {
                function: context,
                finding,
            })
            .map_err(io::Error::other)?,
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

use crate::args;
use cargo_metadata::camino::Utf8Path;
use rapx::utils::log::rap_error_and_exit;
use std::{env, process::Command, time::Duration};
use wait_timeout::ChildExt;

mod workspace;

pub fn run() {
    match env::var("RAP_RECURSIVE")
        .ok()
        .map(|s| s.trim().to_ascii_lowercase())
        .as_deref()
    {
        Some("none") | None => default_run(),
        Some("deep") => workspace::deep_run(),
        Some("shallow") => workspace::shallow_run(),
        _ => rap_error_and_exit(
            "`recursive` should only accept one the values: none, shallow or deep.",
        ),
    }
}

fn cargo_check(dir: &Utf8Path) {
    // always clean before check due to outdated except `RAP_CLEAN` is false
    rap_trace!("cargo clean in package folder {dir}");
    cargo_clean(dir, args::rap_clean());

    rap_trace!("cargo check in package folder {dir}");
    let [rap_args, cargo_args] = args::rap_and_cargo_args();
    rap_trace!("rap_args={rap_args:?}\tcargo_args={cargo_args:?}");

    /*Here we prepare the cargo command as cargo check, which is similar to build, but much faster*/
    let mut cmd = Command::new("cargo");
    cmd.current_dir(dir);
    cmd.arg("check");

    /* set the target as a filter for phase_rustc_rap */
    cmd.args(cargo_args);

    // Serialize the remaining args into a special environment variable.
    // This will be read by `phase_rustc_rap` when we go to invoke
    // our actual target crate (the binary or the test we are running).

    cmd.env("RAPFLAGS", rap_args.join(" "));

    // Invoke actual cargo for the job, but with different flags.
    let cargo_rap_path = args::current_exe_path();
    cmd.env("RUSTC_WRAPPER", cargo_rap_path);

    rap_trace!("Command is: {:?}.", cmd);

    let mut child = cmd.spawn().expect("Could not run cargo check.");
    if let Some(timeout) = args::timeout() {
        match child
            .wait_timeout(Duration::from_secs(timeout))
            .expect("Failed to wait for subprocess.")
        {
            Some(status) => {
                if !status.success() {
                    rap_error_and_exit("Finished with non-zero exit code.");
                }
            }
            None => {
                child.kill().expect("Failed to kill subprocess.");
                child.wait().expect("Failed to wait for subprocess.");
                rap_error_and_exit("Process killed due to timeout.");
            }
        };
    } else if !child.wait().unwrap().success() {
        rap_error_and_exit("Finished with non-zero exit code.");
    }
}

fn cargo_clean(dir: &Utf8Path, really: bool) {
    if really {
        if let Err(err) = Command::new("cargo").arg("clean").current_dir(dir).output() {
            rap_error_and_exit(format!("`cargo clean` exits unexpectedly:\n{err}"));
        }
    }
}

/// Just like running a cargo check in a folder.
fn default_run() {
    cargo_check(".".into());
}

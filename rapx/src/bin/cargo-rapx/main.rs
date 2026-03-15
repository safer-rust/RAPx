/*
    This is a cargo program to start RAP.
    The file references the cargo file for Miri: https://github.com/rust-lang/miri/blob/master/cargo-miri/src/main.rs
*/
#![feature(rustc_private)]

#[macro_use]
extern crate rapx;

use crate::utils::*;
use clap::Parser;
use rapx::cli;
use rapx::help;
use rapx::utils::log::{init_log, rap_error_and_exit};
use std::env;

mod args;
mod cargo_check;
mod utils;

fn phase_cargo_rap() {
    rap_trace!("Start phase cargo-rapx.");
    cargo_check::run();
}

fn phase_rustc_wrapper() {
    rap_trace!("Launch cargo-rapx again triggered by cargo check.");

    let is_primary = env::var("CARGO_PRIMARY_PACKAGE").is_ok();
    let package_name = env::var("CARGO_PKG_NAME").unwrap_or_default();
    let is_build_script =
        env::var("CARGO_CRATE_NAME").map_or(false, |name| name == "build_script_build");

    // check `CARGO_PRIMARY_PACKAGE` to make sure we only run
    // rapx for the local crate, but not dependencies.
    // rapx only checks local crates
    if is_primary && !is_build_script {
        rap_debug!("run rapx for package {}", package_name);
        run_rap();
        return;
    }

    rap_debug!("run rustc for package {}", package_name);
    // for dependencies and some special crate types, run rustc as usual
    run_rustc();
}

#[derive(Parser, Debug)]
#[command(name = "cargo")]
#[command(bin_name = "cargo")]
#[command(version, about)]
#[command(styles = help::CARGO_RAPX_STYLING)]
enum CargoCli {
    #[command(override_usage = help::styled_cargo_rapx_usage())]
    #[command(version= help::RAPX_VERSION)]
    #[command(after_help = help::RAPX_AFTER_HELP)]
    Rapx(cli::RapxArgs),
}

impl CargoCli {
    fn args(&self) -> &cli::RapxArgs {
        match self {
            CargoCli::Rapx(args) => args,
        }
    }
}

fn main() {
    /* This function will be enteredd twice:
       1. When we run `cargo rapx ...`, cargo dispatches the execution to cargo-rapx.
      In this step, we set RUSTC_WRAPPER to cargo-rapx, and execute `cargo check ...` command;
       2. Cargo check actually triggers `path/cargo-rapx path/rustc` according to RUSTC_WRAPPER.
          Because RUSTC_WRAPPER is defined, Cargo calls the command: `$RUSTC_WRAPPER path/rustc ...`
    */

    // Init the log_system
    init_log().expect("Failed to init log.");

    match args::get_arg(1).unwrap() {
        "rapx" => {
            let _ = args::cargo_cli();
            phase_cargo_rap()
        }
        arg if arg.ends_with("rustc") => phase_rustc_wrapper(),
        _ => rap_error_and_exit(
            "rapx must be called with either `rap` or `rustc` as first argument.",
        ),
    }
}

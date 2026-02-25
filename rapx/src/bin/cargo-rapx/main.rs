/*
    This is a cargo program to start RAP.
    The file references the cargo file for Miri: https://github.com/rust-lang/miri/blob/master/cargo-miri/src/main.rs
*/
#![feature(rustc_private)]

#[macro_use]
extern crate rapx;

use crate::utils::*;
use clap::builder::styling::{AnsiColor, Effects};
use clap::{Arg, ArgAction, Args, Command, CommandFactory, Parser, Subcommand};
use rapx::config;
use rapx::utils::log::{init_log, rap_error_and_exit};
use std::env;

mod args;
mod cargo_check;
mod utils;

fn styled_str(s: &str, bold: bool) -> String {
    let effect = if bold {
        AnsiColor::BrightCyan.on_default().effects(Effects::BOLD)
    } else {
        AnsiColor::BrightCyan.on_default()
    };
    format!("\x1b[{}{}\x1b[0m", effect.render(), s)
}

fn styled_usage() -> String {
    format!(
        "{} {}",
        styled_str("cargo rapx", true),
        styled_str("[OPTIONS] <COMMAND> [-- [CARGO_FLAGS]]", false)
    )
}

fn phase_cargo_rap() {
    rap_trace!("Start phase cargo-rapx.");
    cargo_check::run();
}

fn phase_rustc_wrapper() {
    rap_trace!("Launch cargo-rapx again triggered by cargo check.");

    let is_primary = env::var("CARGO_PRIMARY_PACKAGE").is_ok();

    // check `CARGO_PRIMARY_PACKAGE` to make sure we only run
    // rapx for the local crate, but not dependencies.
    // rapx only checks local crates
    if is_primary && args::filter_crate_type() {
        run_rap();
        return;
    }

    // for dependencies and some special crate types, run rustc as usual
    run_rustc();
}

#[derive(Parser, Debug)]
#[command(name = "cargo")]
#[command(bin_name = "cargo")]
#[command(version, about)]
#[command(styles = config::CLAP_STYLING)]
enum CargoCli {
    #[command(override_usage = styled_usage())]
    Rapx(config::Config),
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
            CargoCli::command().get_matches_from(env::args().take_while(|args| args != "--"));
            phase_cargo_rap()
        }
        arg if arg.ends_with("rustc") => phase_rustc_wrapper(),
        _ => rap_error_and_exit(
            "rapx must be called with either `rap` or `rustc` as first argument.",
        ),
    }
}

#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_session;

use clap::Parser;
use rapx::cli::{self, help};
use rapx::{RAPX_DEFAULT_ARGS, RapCallback, rap_debug, rap_info, rap_trace, util::log::init_log};
use rustc_session::EarlyDiagCtxt;
#[cfg(not(rapx_error_output_in_output))]
use rustc_session::config::ErrorOutputType;
#[cfg(rapx_error_output_in_output)]
use rustc_session::output::ErrorOutputType;
use std::env;

fn run_complier(callback: &mut RapCallback) {
    let mut args = env::args().collect::<Vec<_>>();
    args.extend(RAPX_DEFAULT_ARGS.iter().map(ToString::to_string));
    // Finally, add the default flags of RAPx
    rap_trace!("Final arguments to rustc: {:?}", args);

    let handler = EarlyDiagCtxt::new(ErrorOutputType::default());
    rustc_driver::init_rustc_env_logger(&handler);
    rustc_driver::install_ice_hook("bug_report_url", |_| ());
    rustc_driver::compiler_entrypoint(&args, callback);
    rap_trace!("The arg for compilation is {:?}", args);
}

#[derive(Parser, Debug, Clone)]
#[command(override_usage = help::styled_rapx_usage())]
#[command(version= help::RAPX_VERSION)]
#[command(styles = help::RAPX_STYLING)]
struct RapCli {
    #[command(flatten)]
    args: cli::RapxArgs,
}

fn main() {
    _ = init_log().inspect_err(|err| eprintln!("Failed to init log: {err}"));

    // read RAPXFLAGS
    let mut cli_args =
        shlex::split(env::var("RAPXFLAGS").unwrap_or_default().as_str()).unwrap_or_default();
    rap_debug!("RAPXFLAGS = {:?}", cli_args);

    // parse arguments from RAPXFLAGS
    cli_args.insert(0, "rapx".to_owned());
    let cli = RapCli::parse_from(cli_args);
    let rapx_args = cli.args;
    rapx_args.init_env();

    let mut callback = RapCallback::new(rapx_args);
    rap_trace!("rap received arguments: {:#?}", env::args());
    rap_info!("Start analysis with RAPx.");
    run_complier(&mut callback);
}

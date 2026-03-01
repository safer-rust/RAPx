#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_session;

use clap::Parser;
use rapx::cli;
use rapx::help;
use rapx::{RAP_DEFAULT_ARGS, RapCallback, rap_debug, rap_info, rap_trace, utils::log::init_log};
use rustc_session::EarlyDiagCtxt;
use rustc_session::config::ErrorOutputType;
use std::env;

fn run_complier(callback: &mut RapCallback) {
    let mut args = env::args().collect::<Vec<_>>();
    args.extend(RAP_DEFAULT_ARGS.iter().map(ToString::to_string));
    // Finally, add the default flags of RAP
    rap_trace!("Final arguments to rustc: {:?}", args);

    let handler = EarlyDiagCtxt::new(ErrorOutputType::default());
    rustc_driver::init_rustc_env_logger(&handler);
    rustc_driver::install_ice_hook("bug_report_url", |_| ());
    rustc_driver::run_compiler(&args, callback);
    rap_trace!("The arg for compilation is {:?}", args);
}

#[derive(Parser, Debug, Clone)]
#[command(override_usage = help::styled_rapx_usage())]
#[command(version= help::RAPX_VERSION)]
#[command(styles = help::RAPX_STYLING)]
struct RapCli {
    #[command(flatten)]
    config: cli::RapxArgs,
}

fn main() {
    _ = init_log().inspect_err(|err| eprintln!("Failed to init log: {err}"));

    // read RAPFLAGS
    let mut cli_args =
        shlex::split(env::var("RAPFLAGS").unwrap_or_default().as_str()).unwrap_or_default();
    rap_debug!("RAPFLAGS = {:?}", cli_args);

    // parse arguments from RAPFLAGS
    cli_args.insert(0, "rapx".to_owned());
    let cli = RapCli::parse_from(cli_args);
    let rapx_config = cli.config;
    rapx_config.init_env();

    let mut callback = RapCallback::new(rapx_config);
    rap_trace!("rap received arguments: {:#?}", env::args());
    rap_info!("Start analysis with RAPx.");
    run_complier(&mut callback);
}

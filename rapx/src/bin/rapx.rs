#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_session;

use clap::Parser;
use rapx::config;
use rapx::{RAP_DEFAULT_ARGS, RapCallback, rap_debug, rap_info, rap_trace, utils::log::init_log};
use rustc_session::EarlyDiagCtxt;
use rustc_session::config::ErrorOutputType;
use std::env;

fn run_complier(args: &mut Vec<String>, callback: &mut RapCallback) {
    // Finally, add the default flags all the way in the beginning, but after the binary name.
    args.splice(1..1, RAP_DEFAULT_ARGS.iter().map(ToString::to_string));

    let handler = EarlyDiagCtxt::new(ErrorOutputType::default());
    rustc_driver::init_rustc_env_logger(&handler);
    rustc_driver::install_ice_hook("bug_report_url", |_| ());

    rustc_driver::run_compiler(args, callback);
    rap_trace!("The arg for compilation is {:?}", args);
}

fn main() {
    _ = init_log().inspect_err(|err| eprintln!("Failed to init log: {err}"));

    let mut cli_args =
        shlex::split(env::var("RAPFLAGS").unwrap_or_default().as_str()).unwrap_or_default();
    cli_args.insert(0, "rapx".to_owned());
    rap_debug!("RAPFLAGS = {:?}", cli_args);
    let rapx_config = config::Config::parse_from(cli_args);
    rapx_config.init_env();
    let mut callback = RapCallback::new(rapx_config);

    rap_trace!("rap received arguments: {:#?}", env::args());

    let mut rustc_args = env::args().skip(2).collect::<Vec<_>>();
    rap_trace!("arguments to rustc: {:?}", &rustc_args);

    rap_info!("Start analysis with RAPx.");
    run_complier(&mut rustc_args, &mut callback);

    // for arg in env::args() {
    //     if let Some((_full, [test_crate_name])) =
    //         re_test_crate.captures(&arg).map(|caps| caps.extract())
    //     {
    //         compiler.set_test_crate(test_crate_name.to_owned());
    //         continue;
    //     }
    //     match arg.as_str() {
    //         "-alias" | "-alias0" | "-alias1" | "-alias2" => compiler.enable_alias(arg),
    //         "-alias-mfp" => compiler.enable_alias_mfp(),
    //         "-adg" => compiler.enable_api_dependency(), // api dependency graph
    //         "-callgraph" => compiler.enable_callgraph(),
    //         "-dataflow" => compiler.enable_dataflow(1),
    //         "-dataflow=debug" => compiler.enable_dataflow(2),
    //         "-ownedheap" => compiler.enable_ownedheap(),
    //         "-range" => compiler.enable_range_analysis(1),
    //         "-range=print_mir" => compiler.enable_range_analysis(2),
    //         "-pathcond" => compiler.enable_range_analysis(3),
    //         "-test" => compiler.enable_test(),
    //         "-F" | "-F0" | "-F1" | "-F2" | "-uaf" => compiler.enable_safedrop(arg),
    //         "-I" | "-infer" => compiler.enable_infer(),
    //         "-M" | "-mleak" => compiler.enable_rcanary(),
    //         "-V" | "-verify" => compiler.enable_verify(),
    //         "-O" | "-opt" => compiler.enable_opt(1),
    //         "-opt=all" => compiler.enable_opt(2),
    //         "-opt=report" => compiler.enable_opt(0),
    //         "-scan" => compiler.enable_scan(),
    //         "-ssa" => compiler.enable_ssa_transform(),
    //         "-upg" => compiler.enable_upg(1),
    //         "-upg-std" => compiler.enable_upg(2),
    //         "-verify-std" => compiler.enable_verify_std(),
    //         "-mir" => compiler.enable_show_mir(),
    //         "-dotmir" => compiler.enable_show_mir_dot(),
    //         // -timeout has been handled in cargo-rapx
    //         x if x.starts_with("-timeout=") => (),
    //         _ => args.push(arg),
    //     }
    // }
}

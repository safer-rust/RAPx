use crate::args;
use std::process::{self, Command};

pub fn run_cmd(mut cmd: Command) {
    rap_trace!("Command is: {:?}.", cmd);
    match cmd.status() {
        Ok(status) => {
            if !status.success() {
                if let Some(code) = status.code() {
                    process::exit(code);
                }
                eprintln!("RAPx: child command {cmd:?} terminated: {status}");
                process::exit(255);
            }
        }
        Err(err) => panic!("Error in running {:?} {}.", cmd, err),
    }
}

pub fn run_rustc() {
    let mut cmd = Command::new("rustc");
    cmd.args(args::skip2());
    run_cmd(cmd);
}

pub fn run_rap() {
    let mut cmd = Command::new("rapx");
    cmd.args(args::skip2());
    run_cmd(cmd);
}

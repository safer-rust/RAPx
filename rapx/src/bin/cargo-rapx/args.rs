use std::{
    env,
    path::{Path, PathBuf},
    sync::LazyLock,
};

struct Arguments {
    /// a collection of `std::env::args()`
    args: Vec<String>,
    /// options as first half before -- in args
    args_group1: Vec<String>,
    /// options as second half after -- in args
    args_group2: Vec<String>,
    current_exe_path: PathBuf,
    rap_clean: bool,
}

impl Arguments {
    // Get value from `name=val` or `name val`.
    fn get_arg_flag_value(&self, name: &str) -> Option<&str> {
        let mut args = self.args_group1.iter();

        while let Some(arg) = args.next() {
            if !arg.starts_with(name) {
                continue;
            }
            // Strip leading `name`.
            let suffix = &arg[name.len()..];
            if suffix.is_empty() {
                // This argument is exactly `name`; the next one is the value.
                return args.next().map(|x| x.as_str());
            } else if let Some(arg) = suffix.strip_prefix('=') {
                // This argument is `name=value`; get the value.
                // Strip leading `=`.
                return Some(arg);
            }
        }

        None
    }

    fn new() -> Self {
        fn rap_clean() -> bool {
            match env::var("RAP_CLEAN")
                .ok()
                .map(|s| s.trim().to_ascii_lowercase())
                .as_deref()
            {
                Some("false") => false,
                _ => true, // clean is the preferred behavior
            }
        }

        let args: Vec<_> = env::args().collect();
        let path = env::current_exe().expect("Current executable path invalid.");
        rap_trace!("Current exe: {path:?}\tReceived args: {args:?}");
        let [args_group1, args_group2] = split_args_by_double_dash(&args);

        Arguments {
            args,
            args_group1,
            args_group2,
            current_exe_path: path,
            rap_clean: rap_clean(),
        }
    }
}

pub fn rap_clean() -> bool {
    ARGS.rap_clean
}

fn split_args_by_double_dash(args: &[String]) -> [Vec<String>; 2] {
    let mut args = args.iter().skip(2).map(|arg| arg.to_owned());
    let rap_args = args.by_ref().take_while(|arg| *arg != "--").collect();
    let cargo_args = args.collect();
    [rap_args, cargo_args]
}

static ARGS: LazyLock<Arguments> = LazyLock::new(Arguments::new);

pub fn get_arg_flag_value(name: &str) -> Option<&'static str> {
    ARGS.get_arg_flag_value(name)
}

/// `cargo rapx [rapx options] -- [cargo check options]`
///
/// Options before the first `--` are arguments forwarding to rapx.
/// Stuff all after the first `--` are arguments forwarding to cargo check.
pub fn rap_and_cargo_args() -> [&'static [String]; 2] {
    [&ARGS.args_group1, &ARGS.args_group2]
}

/// Returns true for crate types to be checked;
/// returns false for some special crate types that can't be handled by rapx.
/// For example, checking proc-macro crates or build.rs can cause linking errors in rapx.
pub fn filter_crate_type() -> bool {
    if let Some(s) = get_arg_flag_value("--crate-type") {
        return match s {
            "proc-macro" => false,
            "bin" if get_arg_flag_value("--crate-name") == Some("build_script_build") => false,
            _ => true,
        };
    }
    // NOTE: tests don't have --crate-type, they are handled with --test by rustc.
    true
}

pub fn get_arg(pos: usize) -> Option<&'static str> {
    ARGS.args.get(pos).map(|x| x.as_str())
}

pub fn skip2() -> &'static [String] {
    ARGS.args.get(2..).unwrap_or(&[])
}

pub fn current_exe_path() -> &'static Path {
    &ARGS.current_exe_path
}

/// NOTE: for simplicify in rapx argument forwarding, only `-timeout=` is correctly handled,
/// even though both flavors are accepted here.
pub fn timeout() -> Option<u64> {
    ARGS.get_arg_flag_value("-timeout")?.parse().ok()
}

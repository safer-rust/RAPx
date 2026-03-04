use clap::builder::{
    Styles,
    styling::{Effects, Style},
};

pub const RAPX_AFTER_HELP: &str = color_print::cstr!(
    r#"<bold>NOTE:</bold> multiple detections can be processed in single run by 
appending the options to the arguments. Like `cargo rapx -f -m`
will perform two kinds of detection in a row.

<underline>Examples:</underline>

1. detect use-after-free and memory leak for a riscv target:
   cargo rapx check -f -m -- --target riscv64gc-unknown-none-elf
2. detect use-after-free and memory leak for tests:
   cargo rapx check -f -m -- --tests
3. detect use-after-free and memory leak for all members:
   cargo rapx check -f -m -- --workspace
4. extract all public unsafe APIs in the current crate (outputs JSON to stderr):
   cargo rapx extract unsafe-apis

<underline>Environment Variables (Values are case insensitive):</underline>

    RAP_LOG          verbosity of logging: trace, debug, info, warn
                     trace: print all the detailed RAP execution traces.
                     debug: display intermediate analysis results.
                     warn: show bugs detected only.

    RAP_CLEAN        run cargo clean before check: true, false
                     * true is the default value except that false is set

    RAP_RECURSIVE    scope of packages to check: none, shallow, deep
                     * none or the variable not set: check for current folder
                     * shallow: check for current workpace members
                     * deep: check for all workspaces from current folder
                      
                     NOTE: for shallow or deep, rapx will enter each member
                     folder to do the check.
"#
);

pub const RAPX_VERSION: &str = concat!(
    "version ",
    env!("CARGO_PKG_VERSION"),
    "\n",
    "developed by ",
    env!("CARGO_PKG_AUTHORS"),
);

pub const CARGO_RAPX_STYLING: Styles = clap_cargo::style::CLAP_STYLING;
pub const RAPX_STYLING: Styles = clap_cargo::style::CLAP_STYLING;

pub fn styled_str(s: &str, style: &Style, bold: bool) -> String {
    let style = if bold {
        // clap_cargo::style::LITERAL
        style.effects(Effects::BOLD)
    } else {
        *style
    };
    format!("\x1b[{}{}\x1b[0m", style.render(), s)
}

pub fn styled_cargo_rapx_usage() -> String {
    let style = CARGO_RAPX_STYLING.get_literal();
    format!(
        "{} {}",
        styled_str("cargo rapx", &style, true),
        styled_str("[OPTIONS] <COMMAND> [-- [CARGO_FLAGS]]", &style, false)
    )
}

pub fn styled_rapx_usage() -> String {
    let style = RAPX_STYLING.get_literal();
    format!(
        "{} {} {}",
        styled_str("RAPFLAGS=\"[OPTIONS] <COMMAND>\"", &style, false),
        styled_str("rapx", &style, true),
        styled_str("[RUSTFLAGS]", &style, false)
    )
}

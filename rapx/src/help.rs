pub const RAPX_AFTER_HELP: &str = r#"NOTE: multiple detections can be processed in single run by 
appending the options to the arguments. Like `cargo rapx -F -M`
will perform two kinds of detection in a row.

e.g.
1. detect use-after-free and memory leak for a riscv target:
   cargo rapx check -f -m -- --target riscv64gc-unknown-none-elf
2. detect use-after-free and memory leak for tests:
   cargo rapx check -f -m -- --tests
3. detect use-after-free and memory leak for all members:
   cargo rapx check -f -m -- --workspace

Environment Variables (Values are case insensitive):
    RAP_LOG          verbosity of logging: trace, debug, info, warn
                     trace: print all the detailed RAP execution traces.
                     debug: display intermidiate analysis results.
                     warn: show bugs detected only.

    RAP_CLEAN        run cargo clean before check: true, false
                     * true is the default value except that false is set

    RAP_RECURSIVE    scope of packages to check: none, shallow, deep
                     * none or the variable not set: check for current folder
                     * shallow: check for current workpace members
                     * deep: check for all workspaces from current folder
                      
                     NOTE: for shallow or deep, rapx will enter each member
                     folder to do the check.
"#;

pub const RAPX_VERSION: &str = concat!(
    "rapx version ",
    env!("CARGO_PKG_VERSION"),
    "\n",
    "released at 2025-08-17\n",
    "developped by ",
    env!("CARGO_PKG_AUTHORS"),
);

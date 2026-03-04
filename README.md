# ![logo](https://raw.githubusercontent.com/Artisan-Lab/RAPx/main/logo.png)
RAPx (Rust Analysis Platform with Extensions) [![license](https://img.shields.io/github/license/Artisan-Lab/RAPx)](./LICENSE-MPL)[![docs.rs](https://img.shields.io/docsrs/rapx)](https://docs.rs/rapx) is an advanced static analysis platform for Rust, developed by researchers at [Artisan-Lab](https://hxuhack.github.io), Fudan University. It provides an extensible framework for building and integrating powerful analysis capabilities that go beyond those available in the standard rustc compiler, empowering developers to reason about safety, robustness, and performance at a deeper level.

RAPx is available on crates.io. [![crates.io](https://img.shields.io/crates/v/rapx.svg)](https://crates.io/crates/rapx)

## Features
# ![logo](https://raw.githubusercontent.com/Artisan-Lab/RAPx/main/feature.png)
RAPx is structured into two layers: a core layer offering essential program analysis algorithms (e.g., alias and dataflow analysis), and an application layer implementing specific tasks such as bug detection. This separation of concerns promotes modular development and fosters collaboration between algorithm and application developers.

The project is still under heavy development. For further details, please refer to the [RAPx-Book](https://safer-rust.github.io/RAPx-Book/).

## Quick Start

Install `nightly-2025-12-06` on which rapx is compiled with. This just needs to do once on your machine. If the toolchain exists,
this will do nothing.

```shell
rustup toolchain install nightly-2025-12-06 --profile minimal --component rustc-dev,rust-src,llvm-tools-preview
cargo +nightly-2025-12-06 install rapx --git https://github.com/Artisan-Lab/RAPx.git
```

## Usage

Navigate to your Rust project folder containing a `Cargo.toml` file. Then run `rapx` by manually specifying the toolchain version according to the [toolchain override shorthand syntax](https://rust-lang.github.io/rustup/overrides.html#toolchain-override-shorthand).

```shell
cargo +nightly-2025-12-06 rapx [rapx options] -- [cargo check options]
```

or by setting up default toolchain to the required version.
```shell
rustup default nightly-2025-12-06
```

Check out supported options with `-help`:

```shell
$ cargo rapx --help

Usage: cargo rapx [OPTIONS] <COMMAND> [-- [CARGO_FLAGS]]

Commands:
  analyze  perform various analyses on the crate, e.g., alias analysis, callgraph generation
  check    check potential vulnerabilities in the crate, e.g., use-after-free, memory leak
  extract  audit unsafe APIs and output a JSON document
  help     Print this message or the help of the given subcommand(s)

Options:
      --timeout <TIMEOUT>        specify the timeout seconds in running rapx
      --test-crate <TEST_CRATE>  specify the tested package in the workspace
  -h, --help                     Print help
  -V, --version                  Print version

NOTE: multiple detections can be processed in single run by 
appending the options to the arguments. Like `cargo rapx -f -m`
will perform two kinds of detection in a row.

Examples:

1. detect use-after-free and memory leak for a riscv target:
   cargo rapx check -f -m -- --target riscv64gc-unknown-none-elf
2. detect use-after-free and memory leak for tests:
   cargo rapx check -f -m -- --tests
3. detect use-after-free and memory leak for all members:
   cargo rapx check -f -m -- --workspace
4. extract all public unsafe APIs in the current crate (outputs JSON to stderr):
   cargo rapx extract unsafe-apis

Environment Variables (Values are case insensitive):

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
```

If RAPx gets stuck after executing `cargo clean`, try manually downloading metadata dependencies by running `cargo metadata`. 

RAPx supports the following environment variables (values are case insensitive):

| var             | default when absent | possible values     | description                  |
|-----------------|---------------------|---------------------|------------------------------|
| `RAP_LOG`       | info                | debug, info, warn   | verbosity of logging         |
| `RAP_CLEAN`     | true                | true, false         | run cargo clean before check |
| `RAP_RECURSIVE` | none                | none, shallow, deep | scope of packages to check   |

For `RAP_RECURSIVE`:
* none: check for current folder
* shallow: check for current workpace members
* deep: check for all workspaces from current folder
 
NOTE: rapx will enter each member folder to do the check.



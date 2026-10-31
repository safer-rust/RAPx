---
name: rcanary-ai
description: Check Rust crates for memory leak candidates with RAPx rCanary, review terminal diagnostics or check -M JSON evidence, explain true issues and false positives, and repair and rescan when requested. Use for rCanary leak detection, not SafeDrop lifetime errors or RAPx contract verification.
---

# rCanary AI

Run detection and review in the current agent session. RAPx exports static-analysis evidence; this skill reads it, checks the relevant source and ownership contracts, and performs repairs when the user requests them. No separate model API is needed. When asked to run `check -M`, continue through review of every candidate. A standalone terminal command exports reports without launching an agent.

## Choose the entry point

- For a project check, run rCanary with context export and review the results.
- For existing reports, read each selected unit's `profile.json`, then enumerate its `rc-*.json` files. See the [output protocol](references/output.md).
- For a terminal warning or log, start with the function and annotated source calls. Export fresh context only when needed to resolve a relevant evidence gap. A missing report is not evidence of no leaks.

Determine the target manifest, selected packages, features, target platform, and test scope from the user's request and project. Preserve those choices in compilation checks, detection and rescans.

## Run detection

RAPx uses rustc internals. Its binary and the target crate must use the same compiler build and sysroot, with the required components (`rustc-dev`, `rust-src`, `llvm-tools-preview`) and platform tools available. Inspect the toolchain in both the RAPx and target directories:

```sh
rustup show active-toolchain
rustc -Vv
rustc --print sysroot
rustup toolchain list
```

Compare the compiler commit and host against RAPx build records. An unversioned `nightly` file does not identify the compiler that built an older binary. Rebuild locally if the match cannot be established. Use a confirmed toolchain for each command; the examples use `+nightly` only as a placeholder for that confirmed selection. Preserve existing toolchain files, components and targets; temporary `+toolchain` selection usually avoids project configuration changes.

First verify that the target compiles with the same scope as detection. For example:

```sh
cargo +nightly check --manifest-path Cargo.toml
cargo +nightly rapx check --help
cargo +nightly rapx check -M -- --manifest-path Cargo.toml
```

- `-m / --mleak` runs ordinary leak detection. `-M / --m-ai` runs the same detector and exports review context; there is no need to run `-m` first. `-M` takes no value and conflicts with `-m`, `-f` and `-F`.
- Put RAPx options before the first `--` and Cargo options after it. Match `-p`, `--workspace`, `--features`, `--target`, `--tests` and other selection arguments in the compilation precheck. Preserve argument boundaries, especially paths containing spaces.
- If compilation fails, report that failure rather than a clean scan. Do not arbitrarily upgrade dependencies to fit RAPx.
- Verify that `check --help` includes `-M`. For a local build, use `cargo +nightly build --manifest-path /path/to/RAPx/Cargo.toml -p rapx --bins --locked`. Use `cargo-rapx` and `rapx` from the same build, putting that binary directory first on PATH for this invocation. The wrapper resolves `rapx` and `rustc` from PATH. Do not replace the user's global installation just to review reports.
- Each analyzed Cargo package gets `rcanary-<crate>-<kind>/`, for example `rcanary-demo-lib/`. `CARGO_MANIFEST_DIR` selects the package directory, including when launched from another directory or with `--manifest-path`. Direct rustc/RAPx invocation falls back to its working directory when that variable is absent. The crate name is rustc's name, which may differ from the package name.
- Existing unit directories cause a warning and skip analysis, preserving their contents. Before an authorized new check, archive and move the old directories, confirming the original paths no longer exist. Copying files while leaving the original directories causes rescans to skip. Do not delete existing reports to bypass this protection.
- The wrapper normally runs `cargo clean` before and after analysis, using the launch directory. When using an external `--manifest-path`, cleanup may fail or clean a different workspace; running from the target package avoids that mismatch. If necessary, clean the target with its actual manifest or use a fresh Cargo `--target-dir`. If cleanup is disabled or ineffective, verify that Cargo actually recompiled and RAPx analyzed the selected units; Cargo can replay old diagnostics without running the detector.
- Keep the full command, selected scope, logs and exit status outside unit directories, for example under `.rapx-ai/rcanary/`. Report classification failures and missing units. Explicit crate types other than `lib` or `bin`, including mixed lib/bin, are currently unsupported for export.

## Review the evidence

Read the [output protocol](references/output.md) for field meanings, completion checks and detector limitations. Read the [review rules](references/review.md) when judging findings or preparing repairs.

For every selected compilation unit, read the profile before its findings. Check status, analyzed and skipped function counts, return checks, finding count and limitations, together with this invocation's exit status and logs. Missing or invalid profiles indicate incomplete export. Even a completed zero-finding profile has the detector's fixed coverage boundaries.

Each finding file contains `function` (source and full MIR) and `finding` (one candidate, return site, source calls, symbolic local state and solver constraints). Extract the candidate first; read long MIR and constraints selectively. Reuse matching function context across files. Do not load every report in full at once.

rCanary warns when its accumulated constraints are `unsat` at a return and it has seen an owner-to-pointer/reference source call. This is a heuristic candidate. The constraints do not establish an executable path or identify a unique leaking allocation. Inspect the actual ownership transfer, recovery and eventual deallocation in the source and relevant callees/callers.

Deliver each candidate's report path and ID, relevant code locations, ownership sequence, assessment (`supported`, `refuted`, or `inconclusive`), evidence, remaining assumptions and any repair proposal. For a false positive, identify the concrete premise that fails. If the user asked for analysis only, stop after the assessment and proposals.

## Repair and rescan

When repairs are requested, apply focused ownership or release changes within the existing authorization. Check that source still matches the reviewed snapshot. Group related candidates by resource/function so the same issue is fixed once.

Before editing or rescanning, move each relevant `rcanary-<crate>-<kind>/` directory to a baseline location such as `.rapx-ai/rcanary/before-001/` inside that package. Verify both paths, preserve package hierarchy and logs, and confirm the original output paths are absent. Keep reviews, patches and validation records outside detector directories. Never rewrite original diagnostics to claim a verdict or successful repair.

Compile, run applicable tests, and rerun `check -M` with the same scope and toolchain. Read the new profiles and compare findings by source semantics and resource relationships, rather than IDs, MIR locals, line numbers or counts alone. Check remaining and new candidates. Archive current output again before another rescan.

A disappearing warning is insufficient if analysis was skipped, compilation failed, scope changed, or ownership remains wrong. Mark such validation incomplete. Disabling detection, excluding functions, suppressing diagnostics or deleting tests does not establish a fix. Normally stop after two local repair attempts per group if unresolved, preserving the patch and actual failure evidence; stop earlier if changing an external ownership contract requires user input.

## Distribution

This directory is the complete distributable skill; keep `references/` with it. For discovery in another target project, copy the whole `rcanary-ai` directory into that project's `.agents/skills/`, or install it in the host's user-level skill location. RAPx's ordinary `skills/` directory alone does not make it discoverable in other projects. The repository's `.agents/skills/rcanary-ai/SKILL.md` is only a local discovery entry.

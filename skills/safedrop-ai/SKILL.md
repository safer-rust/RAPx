---
name: safedrop-ai
description: Check Rust projects for use-after-free, double-free, and dangling pointers with RAPx SafeDrop. Run cargo rapx check -f or check -F, interpret terminal or JSON diagnostics, collect context, review potential bugs and false positives, and fix and rescan when requested. Applies to SafeDrop findings, not rCanary leak detection or RAPx contract verification.
---

# SafeDrop AI

Use the current agent to run detection and review. RAPx performs static analysis and exports evidence; this skill interprets that evidence, reads additional source, proposes fixes, and validates them. No separate model API configuration is needed. When the user requests `check -F`, continue after the command to review every candidate and deliver conclusions. In a standalone terminal, the command only runs detection and exports context; it does not launch a model.

## What SafeDrop detects

SafeDrop tracks the release state of values using Rust MIR, path enumeration, MoP alias analysis, and heap ownership information. It reports these candidate issues:

- `use_after_free`: a value may have been released and subsequently used or passed to a function.
- `double_free`: the same resource may be released again.
- `dangling_pointer`: a return value or relevant argument pointer may refer to an invalidated resource at function exit.
- `use_after_free_and_double_free`: UAF and DF findings merged for the same release/trigger pair.

These are candidates from bounded static analysis. SafeDrop does not execute the program and does not prove the absence of other memory issues.

## Choose an entry point

Start with the material available; a new run is not always necessary:

1. **Project check requested, no diagnostics available**: run SafeDrop and enable context export when individual review is needed.
2. **Existing `profile.json` and individual finding files**: read the compilation unit's status and limitations, then enumerate `sd-*.json` in the same directory and review each finding. Read legacy `report.json` according to its actual fields. See the [output protocol](references/output.md).
3. **Existing terminal output, logs, or a single warning**: extract the issue type, function, source location, release site, and trigger site, then analyze the source. If the logs are insufficient, run SafeDrop with context export. If the project is inaccessible or execution is unavailable, describe the evidence gaps.

Explain existing output directly when that is the user's request and the evidence is sufficient. When asked to check a project, perform the check rather than only providing commands.

## Run detection

Determine the target Rust project's working directory, manifest, packages, features, target, and user-specified scope. **The target crate and its dependencies must pass compilation checks on the toolchain used to build the current RAPx binary.** RAPx uses compiler internals and requires the matching toolchain, sysroot, components such as `rustc-dev`, `rust-src`, and `llvm-tools-preview`, and platform linker tools.

### Inspect and select the toolchain

Check the active toolchain and compiler in both the RAPx source directory and the target crate directory:

```sh
rustup show active-toolchain
rustc -Vv
rustc --print sysroot
rustup toolchain list
```

Use RAPx build records and `rust-toolchain.toml` to compare the toolchain name, rustc commit, and host, and confirm the sysroot source. The active-toolchain output can also identify whether selection comes from a directory file, an override, or an environment variable. A repository specifying only `nightly` does not pin a version. Its currently active toolchain does not establish which version built an older RAPx binary. If the match cannot be established, rebuild RAPx with a confirmed toolchain first.

If the target crate's active toolchain differs, choose a temporary or directory-specific configuration as needed. The examples below use an already confirmed `nightly`; replace it with the actual toolchain used to build RAPx, such as a recorded dated nightly. Do not guess the version.

To select a toolchain for individual commands:

```sh
cargo +nightly check --manifest-path Cargo.toml
cargo +nightly rapx check -F
```

To keep using that toolchain in the crate directory, run there:

```sh
rustup override set nightly
rustup show active-toolchain
rustc -Vv
```

Alternatively, create `rust-toolchain.toml` in the target crate directory. Set `channel` to the actual toolchain matching RAPx; use its configuration as a guide for components, for example:

```toml
[toolchain]
channel = "nightly"
components = ["rustc-dev", "rust-src", "llvm-tools-preview", "rustfmt"]
```

Check for an existing `rust-toolchain.toml` or `rust-toolchain` first. Read existing configuration and preserve its targets, profile, and components; choose temporary selection or a focused edit instead of overwriting the file. After applying an override or configuration file, run `rustup show active-toolchain` and `rustc -Vv` again to confirm what takes effect. For temporary `+toolchain` selection, verify it with `rustc +nightly -Vv`. There is no need to change the global default. Rebuild RAPx after updating nightly; source compatibility with several nightlies does not make one binary compatible with all of them.

### Verify that the target crate compiles

Run ordinary `cargo check` with the selected toolchain first. Match the packages, features, target, test targets, manifest, and other choices of the later RAPx invocation. For example:

```sh
cargo +nightly check --manifest-path Cargo.toml
```

Use the Cargo arguments after the first `--` in the RAPx command for this check; omit RAPx's `-F`. If it fails, record the specific toolchain, dependency, or source compatibility issue. Do not interpret compilation failure as no findings or arbitrarily upgrade dependencies to accommodate RAPx. Ordinary `cargo check` establishes compilation compatibility only. Subsequently verify that RAPx actually analyzed the code, especially when build cleanup is disabled and cached results from the precheck might skip analysis.

### Execute SafeDrop

Inspect the available entry point, then select one detection mode: use `-f` for ordinary detection or `-F` for structured context and individual review. There is no need to run `-f` before `-F`:

```sh
cargo +nightly rapx check --help
# Ordinary detection
cargo +nightly rapx check -f
# Choose this command when context and AI review are needed
cargo +nightly rapx check -F -- --manifest-path Cargo.toml
```

- Replace `+nightly` with the confirmed RAPx build toolchain and preserve the scope used for the compilation precheck.
- `-f` / `--uaf` enables ordinary SafeDrop. If supplied without an integer, it parses as 1. `-F` uses the same detector and collects AI review context; do not combine it with `-f` or `-m`. The current source writes the `MOP` environment variable but has no identified reader. Do not interpret the integer as an effective precision or coverage control.
- `-F` takes no value and belongs before the first `--`. Put Cargo arguments such as `--manifest-path`, `-p`, `--workspace`, `--features`, `--target`, and `--tests` after it. Preserve argument boundaries and quote paths containing spaces.
- RAPx creates `<crate>-<kind>/`, such as `demo-lib/` or `demo-bin/`, directly in each analyzed Cargo package directory. Cargo's existing `CARGO_MANIFEST_DIR` determines this location, rather than the command's launch directory. A direct RAPx invocation without that variable uses the current working directory. By default, the wrapper still runs `cargo clean` before and after execution.
- Retain the top-level Cargo command, selection scope, terminal logs, and exit status; JSON does not store `command`. Library and binary outputs go to `<package>/<crate>-lib/` and `<package>/<crate>-bin/`; test targets use their corresponding kinds. Each directory contains `profile.json` and one `sd-<unit>-<index>.json` per finding. Read each unit using the selected packages and the profile paths printed in the terminal. There is no shared output root or aggregate report.
- The directory's crate name comes from rustc's `--crate-name` and may differ from the Cargo package name. Currently, `-F` accepts only `lib` and `bin` in an explicit `--crate-type`; other types or mixed lib/bin fail before directory creation and analysis. Record the incomplete unit and actual classification error. Existing text diagnostics remain reviewable. If trying ordinary `-f` is useful for the task, state that it provides no structured export. Do not infer no issues from missing JSON. See [target classification limitations](references/output.md#target-classification-limitations).
- If the directory already exists, RAPx warns and skips SafeDrop analysis for that unit, preserving its contents. An existing directory, an old `completed` report, or a successful Cargo exit does not prove analysis completed in this run. For an authorized new check or rescan, archive and move the entire old unit directory first. Do not automatically delete an existing directory to bypass the warning.
- Check that `check --help` offers `-F` / `--f-ai`. If not, the current RAPx lacks this feature; do not claim export succeeded. Prefer a local build or installation containing the change. Report actual blockers such as missing tools, compiler mismatches, or missing linker tools, and review available material where possible.

For a local build, use `cargo +nightly build --manifest-path /path/to/RAPx/Cargo.toml -p rapx --bins --locked`. Use `cargo-rapx` and `rapx` from the same build, adding that build's binary directory to PATH for this invocation. The wrapper finds `rapx` and `rustc` through PATH; it does not automatically select sibling executables. Invoke the built `cargo-rapx rapx check ...` from the target project and ensure child processes find the matching toolchain. Do not install or replace the user's global RAPx merely to analyze existing diagnostics.

## Interpret output and review findings

See the [output protocol](references/output.md) for run metadata, terminal warning formats, field precision, and evidence gaps. See the [review rules](references/review.md) for individual assessments and repair decisions.

For the current format, read `profile.json` first, then enumerate every `sd-*.json` in the same directory. Each file contains `function` (the owning function's `source` and complete `mir`) and `finding` (one candidate and its witness). `finding.function` is the full function name. Extract the individual `finding` first, then read function context as needed instead of sending every file's full text to the model at once. Context repeats across files for the same function; after verifying that it matches, reuse already-read content. Separate files support individual review but do not shorten a long function.

`profile.json` is generated only after every finding file has been written successfully. Without a profile or with invalid profile JSON, existing finding files are partial evidence and cannot establish that this run completed a full scan. Zero findings produce only the profile; still check status, actual function count, limitations, and Cargo exit status. `limitations` appears only in the profile; look up entries for the current function or finding ID. Read legacy `functions[finding.function]` mappings or inline `function_source` and `mir` according to their actual fields, without overwriting original reports.

### Fixed capability boundaries

The current implementation has these general boundaries:

- SafeDrop is bounded and approximate. Path enumeration, alias visits, field/dereference depth, and value count have limits; loops and interprocedural summaries involve approximations. Some truncation in path or alias phases is not fully recorded. The absence of an exception marker does not establish complete coverage.
- A witness is a representative path prefix and snapshot at detection. It does not prove branch satisfiability or path executability. May-alias does not prove equal runtime addresses. Full alias derivation history, call-summary provenance, branch constraints, exact statement indices, and all deduplicated occurrences are unavailable. Read additional source as needed or retain `inconclusive`.
- Related-value snapshots contain at most 64 values. Field types are still interpreted as the type of the entire MIR local. Source anchors may identify only a function or basic block. See the output protocol for filtering of constant MIR, internal dummy functions, and some exit dangling-pointer checks.
- JSON `confidence` preserves SafeDrop's original heuristic level. A terminal display of `99%` does not mean a 99% probability that the issue is real.
- `completed` means the compilation unit finished analysis, subject to fixed boundaries and this run's `limitations`. `partial`, `skipped`, missing reports, and invalid reports cannot count as a clean scan. Assess the overall run using Cargo exit status and actual scope. Empty directories or analysis skipped because a directory exists do not establish a passing scan.
- `_N` denotes a MIR local and `BBN` a MIR basic block. Source ranges may cover an entire function or basic block. These are not exact trigger statements or stable identities across versions.
- Interpret path prefixes, release-state propagation chains, and current alias relationships separately. None alone is a proven executable counterexample.
- Use `supported` (evidence supports the finding), `refuted` (evidence contradicts it), or `inconclusive` (insufficient evidence), citing actual source, MIR, or evidence fields. Do not force a binary verdict from heuristic scores or missing context.

For each candidate, deliver its original ID or log anchor, assessment, relevant code locations, resource and event sequence, evidence, unresolved assumptions, and a repair proposal if supported. For a false positive, identify the premise that fails. If there are no findings, state the actual analysis scope and run limitations.

## Repair and rescan

When the user requests repairs, apply relevant changes within existing authorization; when only analysis is requested, provide proposals. **Before an authorized repair or rescan, move the entire relevant unit directories into a baseline location such as `.rapx-ai/before-001/` in each package.** Preserve directory names, reports, the top-level command, and exit status, and confirm that the original unit paths no longer exist. Preserve package hierarchy or original paths when archiving multiple packages to avoid name collisions; verify source and archive destinations first. Copying reports while leaving the original directory causes rescans to skip analysis. Keep AI reviews, `reviews.jsonl`, `review.md`, patches, and repair records outside unit directories, for example under `.rapx-ai/`. Do not rewrite original diagnostics or fabricate detector results.

Group related findings by function or resource to avoid repeatedly fixing the same issue. After editing, run compilation, applicable tests, and SafeDrop with **the same packages, features, target, and analysis configuration**. New profiles and finding files go to each package's `<crate>-<kind>/`; compare them with the archived baseline. Before another rescan, archive and move the current unit directories again. Match findings using functions, source semantics, and resource relationships, checking both remaining and new findings. Do not compare only line numbers, MIR IDs, or finding counts.

If detection did not run, the build failed, scope is incomparable, or results cannot be matched, mark validation incomplete. Disabling detection, lowering limits, excluding functions, or deleting tests does not establish a fix. Normally allow at most two automatic repair attempts per group and stop when validation succeeds. If unresolved or a change to business expectations is needed, report the evidence and remaining work instead of retrying indefinitely.

## Skill placement

This directory is the complete distributable skill; retain `references/` with it. For automatic discovery in another Rust project, copy the entire `safedrop-ai` directory into that project's `.agents/skills/`, or install it in a user-level skill directory supported by the host. Keeping it only in RAPx's ordinary `skills/` directory does not make it discoverable in other target projects. An agent can also be explicitly instructed to read this `SKILL.md`, without a global installation.

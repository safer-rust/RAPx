# SafeDrop output and evidence

## Terminal diagnostics

Ordinary `cargo rapx check -f` retains the existing logs and warnings with source snippets, typically including:

- `Use-after-free detected`, `Double free detected`, or `Dangling pointer detected`. A release/trigger pair may appear as `Double free / Use-after-free`.
- Function name, source file, line number, and source snippet.
- `_N(variable name, file:line)` and `BBN(file:line)`, identifying MIR locals and basic blocks.
- An explanation that two values may alias, followed by the first release and subsequent use, release, or dangling value at exit.
- `confidence 99%` / `50%` / `0%`: the original format uses percentages, but these are heuristic levels. They currently usually correspond to a fully dropped value, a dropped field, or a special pointer classification. Do not use them as probabilities.
- `during unwinding`: the record relates to unwinding; review cleanup paths and the panic strategy.

Intermediate logs such as `Find ...; add to records` can repeat final warnings. Final diagnostics are deduplicated by local and release/trigger pair; UAF and DF can also merge. Do not count log lines as independent issues. No warning is not a safety proof: failed or skipped execution may also produce none.

## JSON reports

`check -F` enables SafeDrop and AI review context without a directory argument. Each analysis process creates `<crate>-<kind>/` directly in its Cargo package directory and writes one `profile.json` plus a separate JSON file for each finding. Cargo's existing `CARGO_MANIFEST_DIR` identifies the package; direct RAPx invocation without it uses the current working directory. With `--manifest-path` or workspace checks, look in the actual selected package directories.

Library and binary outputs go to `<package>/<crate>-lib/` and `<package>/<crate>-bin/`. Library unit tests, binary unit tests, and integration tests use the kinds `lib-test`, `bin-test`, and `integration-test`. There is no shared output root or root summary report. For example:

```text
demo-bin/
  profile.json
  sd-demo-bin-0.json
  sd-demo-bin-1.json
```

Directory creation uses atomic `create_dir`. If a directory or file with that name exists, RAPx warns and returns, skipping SafeDrop analysis for that unit and preserving the contents. Even an empty directory prevents analysis. Other units without conflicts can still generate reports. For an authorized new run, archive and move the entire old unit directory; copying reports while leaving the original directory is insufficient.

Read each unit's newly generated reports and retain the top-level Cargo command, selection scope, terminal logs, and exit status. A directory-exists warning takes precedence over an old JSON `completed` status: the unit was skipped in this run, even if Cargo succeeds. Build failure, an empty directory, or missing or invalid reports cannot establish a completed scan. Missing reports can mean analysis never started, was skipped by caching, or failed.

Verify that the profile and finding JSON files parse. Check their actual fields and `rapx_version` / `rustc_version` against the corresponding implementation. The profile is written after all finding files succeed. A missing or invalid profile indicates incomplete output; existing finding files remain partial evidence. Zero findings produce only the profile; still check status, function count, and actual execution. An empty directory is not a zero-finding result. The profile contains no finding manifest; enumerate all `sd-*.json` in the same directory.

Each `profile.json` contains:

| Field | Meaning |
| --- | --- |
| `unit` | Crate name and target kind, such as `demo-lib` or `demo-bin` |
| `rapx_version`, `rustc_version` | Tool and compiler versions; the compiler version may be null if unknown |
| `working_directory` | Analysis process's working directory, used to interpret relative source paths; it may differ from the command's launch directory |
| `status` | Analysis status of this compilation unit, described below |
| `analyzed_functions` | Number of functions actually analyzed in this unit |
| `limitations` | Optional short list of exceptions observed in this run; fixed capability boundaries are documented in the skill |

Interpret analysis status separately from finding count:

| `status` | Interpretation |
| --- | --- |
| `completed` | The unit finished analysis, subject to known limits; this does not establish that the entire Cargo command succeeded |
| `partial` | Analysis of this unit is known to be incomplete; do not claim the full scope is free of issues |
| `skipped` | No functions were actually analyzed; having no finding files is not a passing scan |

Keep reports for different compilation units separate. Identically named functions can differ across packages, crate types, features, or test builds. Review records must identify both the report path and finding ID; do not merge findings by short function name alone.

Each finding file is named `<finding.id>.json`, for example `sd-demo-bin-0.json`, and contains two fields:

| Field | Meaning |
| --- | --- |
| `function` | Owning function's context: optional `source` and complete function `mir` |
| `finding` | Exactly one `SafeDropFinding`, including its function name, candidate judgment, and witness |

Read context from `function.source` and `function.mir`; `finding.function` gives the full function name. Each file independently supplies one finding's evidence. Multiple findings in the same function repeat its source and MIR for individual reading, which can increase total disk use and does not shorten a long function. Complete MIR still includes all basic blocks, local declarations, and statements; no path slicing is performed. Read run metadata and limitations from the profile in the same directory. JSON no longer stores `command`; callers record the top-level Cargo command and selection scope separately.

Legacy `report.json` may link shared context through `functions[finding.function]` or inline `function_source` and `mir` in each finding. Read its actual structure without overwriting historical reports.

`profile.limitations` records only exceptions that actually occurred, scoped by function name or finding ID:

| Short marker | Observed event |
| --- | --- |
| `related_values_truncated` | The witness had more than 64 related values, so its snapshot was truncated |
| `source_unavailable` | The function's source snippet could not be obtained |
| `source_location_unavailable` | The finding's original source range could not be mapped |
| `witness_unavailable` | The finding has no captured witness |
| `no_enumerated_path` | No enumerated path was available for SafeDrop to traverse in this function |
| `safedrop_visit_limit_reached` | The function reached SafeDrop's visit limit |
| `no_functions_analyzed` | No functions were actually analyzed in this compilation unit |

Temporary witness exceptions are collected into the profile's `limitations` during writing, rather than repeated in each witness. An empty list may be omitted. See the skill's [fixed capability boundaries](../SKILL.md#fixed-capability-boundaries) for fixed limits, approximations, and unavailable analysis capabilities. A missing field does not imply unbounded or complete analysis.

Each `SafeDropFinding` has these base fields:

| Field | Meaning and caveats |
| --- | --- |
| `id` | `sd-<crate>-<target-kind>-<unit-index>`, such as `sd-demo-lib-0` or `sd-demo-bin-0`. Indices start at zero in each unit. The ID is also the filename stem and links reviews and repairs; it does not affect detection or deduplication and need not remain stable after rescanning |
| `function` | Full function name corresponding to the file's `function` context |
| `bug_type` | `use_after_free` / `double_free` / `dangling_pointer` / `use_after_free_and_double_free` |
| `confidence` | Detector's original heuristic level |
| `during_unwind` | Whether the finding relates to unwinding |
| `location` | Mapping of the original `TyBug` span, which may cover the entire function |
| `drop_site` | First release's local, basic block, and optional source range |
| `trigger_site` | Subsequent use, repeated release, or dangling value at exit; exit checks may have no basic block |
| `witness` | One representative snapshot captured at detection before DFS rollback, or `null` if unavailable |

`SafeDropSite.local` and `.basic_block` may be null. Do not replace null with zero: local 0 commonly denotes the return slot and is a valid ID. Source mapping for a site may identify only a basic block; MIR IDs do not replace source locations.

`SourceLocation` contains `path`, `start_line`, `start_column`, `end_line`, `end_column`, and optional `source_digest`. Lines and columns are one-based character coordinates, with an exclusive end, not UTF-8 byte offsets. The current digest is `fnv1a64:<sixteen lowercase hexadecimal digits>` for the compiler's snapshot of the entire source file. It detects version changes but is not a cryptographic integrity guarantee. rustc removes a UTF-8 BOM and normalizes CRLF to LF. Apply the same normalization before comparing digests; hashing raw Windows file bytes alone does not establish that source changed. You can also compare the finding file's `function.source` or collect fresh context. If the digest is absent, state that snapshot consistency was not verified by digest rather than claiming the file is unchanged. If source differs from the snapshot, recollect context or explicitly review only the historical version.

## Use witness evidence correctly

When export is enabled, the collector captures the available `witness` at the analysis site:

| Field | Meaning and limits |
| --- | --- |
| `path_prefix` | Basic-block sequence from function entry to the candidate trigger; it is not a complete execution path and does not prove all branch conditions are satisfiable |
| `drop_propagation` | Value ID chain through which release state propagated, from `DropRecord.prop_chain`; it is not a CFG path and does not explain each derivation |
| `values` | Related abstract values and their state at detection, described below |
| `owner_transfers` | Relevant Move pairs `[destination_value_id, source_value_id]`; these do not imply equality between source-level locals |

Each entry in `values` contains:

| Field | Meaning |
| --- | --- |
| `value_index`, `local` | SafeDrop value ID and corresponding MIR local ID; field projections can make them differ |
| `name`, `local_type`, `fields` | Available source name, type of the entire MIR local, and field path; `local_type` is not the projected field's type |
| `kind`, `may_drop`, `needs_drop` | Analyzer classification and release-related properties; interpret them according to the implementation, not as language-level ownership proofs |
| `is_dropped`, `has_dropped_field` | Static release state at detection, distinguishing a whole value from some fields |
| `may_alias` | May-alias query results for other values, not proof of equal runtime addresses or a complete derivation history |
| `direct_pointees` | Debug strings for abstract locations such as Slot / Null, not concrete addresses or dereferenceable pointers |

Use source and MIR to check event order, branches, calls, ownership transfer, and reinitialization. Read related functions, types, and `Drop` implementations as needed. Snapshots retain at most 64 related values; truncation is recorded in the profile's run limitations. Other referenced value IDs may lack full definitions. A finding retains only one representative witness, not all occurrences merged by deduplication.

Full alias derivation, call-summary provenance, branch constraints, exact statement indices, and all deduplication sources are still unavailable. The skill documents these fixed boundaries; new reports do not repeat them as `missing_context` lists.

## Analysis scope and inherent limits

Through the wrapper, SafeDrop analyzes local primary packages selected by Cargo; dependencies and build scripts usually compile with ordinary rustc. Constant MIR, internal dummy functions, and similar cases are filtered. Neither terminal reporting nor JSON export suppresses findings based on `.cargo` appearing in a source path. A final function-name segment containing `drop`, `dealloc`, `release`, or `destroy` skips exit dangling-pointer checks, not all SafeDrop checks in that function.

Default analysis limits path count, alias visits, field/dereference depth, value count, and SafeDrop visits. Loops and interprocedural summaries also involve approximations. Use the actual report and implementation version to interpret limitations; not reaching a known limit does not imply exhaustive coverage. Check `panic=abort` versus unwind reachability, FFI or unknown calls, special pointers, and custom destructors against the code.

## Target classification limitations

Before alias analysis and SafeDrop detection, `-F` identifies the compilation unit through `driver::unit_name`. The directory's crate name comes from rustc's `--crate-name`, not directly from the Cargo package name. Target names can differ from package names, and package-name hyphens can become underscores in crate names. Use actual report paths and the profile's `unit`.

An explicit `--crate-type` currently accepts only `lib` and `bin`. Other valid Rust types, including `rlib`, `dylib`, `cdylib`, `staticlib`, and `proc-macro`, trigger `Cannot classify SafeDrop crate type`; mixed lib and bin are also rejected. A missing `--crate-name` likewise fails. These classification errors currently fail the RAPx analysis process; they are not completed checks with no issues. Do not change a project's crate type merely to bypass export limitations.

Test classification uses `--test`, explicit crate types, and the presence of Cargo's existing `CARGO_BIN_NAME` and `CARGO_TARGET_TMPDIR`. The environment variables supplement classification only when the type is absent. Binary evidence takes precedence as `bin-test`; otherwise integration-test evidence gives `integration-test`, with remaining cases classified as `lib-test`. A non-test target with no type is classified as `bin`. These are the current implementation's rules, not a guarantee of coverage for every custom target.

Ordinary `-f` does not use export target classification. If `-F` fails for this reason, existing logs remain reviewable. If trying `-f` fits the user's task, verify actual execution and terminal output again and state that structured context was not generated. Repeatedly rerunning `-F` does not resolve the same classification error.

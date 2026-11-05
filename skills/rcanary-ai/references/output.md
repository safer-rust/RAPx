# rCanary output protocol

## Shared reading rules

The current SafeDrop, rCanary, and opt exports share a profile header and a
`finding` object in every candidate file. Read them in this order:

1. Verify this invocation's exit status and scope, then read its fresh
   `profile.json`. Missing or invalid profiles indicate incomplete output.
2. Read `analyzer` and choose the filename prefix below. Check that `unit`,
   versions, working directory, status, and limitations match the intended run.
3. Enumerate the analyzer's candidate files in the same directory. Their number
   must equal `finding_count`. Read each file's `finding`, verify that its ID
   matches the filename stem, and reject duplicate or mismatched IDs.
4. Use any top-level `function` context and the analyzer-specific evidence
   described below. Count agreement is an output-consistency check, not proof
   of fresh execution or complete analysis coverage.

| `analyzer` | Candidate files | Additional evidence |
| --- | --- | --- |
| `safedrop` | `sd-<unit>-<index>.json` | Top-level `function`; release/use sites and witness in `finding` |
| `rcanary` | `rc-<unit>-<index>.json` | Top-level `function`; return sites, locals and solver evidence in `finding` |
| `opt` | `opt-<unit>-<index>.json` | Source, annotations and static advice inside `finding` |

The common profile fields are `analyzer`, `unit`, `rapx_version`,
`rustc_version`, `working_directory`, `status`, `analyzed_functions`,
`finding_count`, and optional `limitations`. Analyzer-specific profile fields
remain at the same JSON level. `rustc_version` is a best-effort query of
`rustc --version` on PATH; use build records to establish binary compatibility.
No schema-version field or top-level Cargo command is exported.

`completed` means analysis completed within that analyzer's model; `partial`
means known coverage loss; `skipped` means no functions were analyzed. All three
statuses use the same vocabulary, but opt currently emits only `completed` or
`skipped`. Function counts reflect each detector's traversal: opt excludes the
two injected helpers, while other analyzers retain their existing filtering.
Do not compare those counts as identical coverage measurements across detectors.
Zero findings are meaningful only with fresh completed output, positive analyzed
function count, matching scope, and successful execution. Read `limitations`
even when status is `completed`.

Older reports may lack `analyzer` or `finding_count`; older opt profiles may
include `schema_version`, and their candidate files may be flat JSON objects.
Read these according to their actual fields and provenance, state any completion
checks that cannot be performed, and preserve the originals. Do not infer a
current-format zero-finding scan from missing fields.

## Locations and completion

`cargo rapx check -M -- [cargo options]` writes to each analyzed package, using Cargo's `CARGO_MANIFEST_DIR`. A direct invocation without that variable uses the working directory:

```text
<package>/rcanary-<crate>-<kind>/
  profile.json
  rc-<crate>-<kind>-0.json
  rc-<crate>-<kind>-1.json
```

Kinds are `lib`, `bin`, `lib-test`, `bin-test`, and `integration-test`. Explicit crate types currently accept only `lib` and `bin`; mixed library/binary types and other types fail classification before analysis. Test harnesses without `--crate-type` use Cargo's `CARGO_BIN_NAME` and `CARGO_TARGET_TMPDIR` to distinguish binary, library and integration tests. These directories are separate from SafeDrop's `<crate>-<kind>/` outputs.

An existing directory, even if empty, or a file occupying the output path causes the command to fail with a nonzero exit status before this unit's rCanary analysis. Existing contents are preserved. An old completed profile cannot establish a fresh scan. Use this invocation's logs and actual output paths. Archive and move existing directories before an authorized fresh run.

The profile is written after all finding files succeed. Without a valid profile, finding files are partial evidence. Zero findings produce only the profile. Check that `finding_count` equals the number of current `rc-*.json` files and that every selected unit was actually analyzed. Interrupted writes, analysis panics, export errors and missing compilation units cannot count as a clean scan.

## Profile

| Field | Meaning |
| --- | --- |
| `analyzer` | `rcanary` |
| `unit` | rustc crate name plus target kind, without the `rcanary-` directory prefix |
| `rapx_version`, `rustc_version` | RAPx package version and best-effort `rustc --version` from PATH; retain build records to establish the actual matching compiler |
| `working_directory` | Analysis process working directory, not necessarily the command's launch directory |
| `status` | `completed`: functions visited without recorded coverage loss; `partial`: some functions/operations/return checks were skipped or unknown; `skipped`: no functions analyzed |
| `analyzed_functions`, `skipped_functions` | Functions actually visited and functions skipped by cyclic-CFG or syscall-dispatch filters |
| `checked_returns` | Number of visited returns with a solver check |
| `finding_count` | Number of exported warning candidates, not number of leaking allocations |
| `solver_timeout_ms` | Per-function solver configuration, currently 1000 ms per check |
| `limitations` | Observed gaps, qualified by function or finding ID; absent when empty |

Coverage markers include `cyclic_cfg_skipped`, `syscall_dispatch_skipped`, `no_return_checked`, `no_functions_analyzed`, `unsupported_local`, `unsupported_merge_local`, `incompatible_merge_local`, and `solver_unknown` with a return block and reason. Missing source text or locations are recorded while writing. Source-mapping gaps do not by themselves change analysis status. Unsupported-local markers are conservative and may involve locals unrelated to the candidate; inspect them before assessing their effect.

The JSON does not store the top-level command, all Cargo selection options, exit status, run ID or an AI verdict. Keep those externally. `completed` is completion within the fixed model, not a proof of full leak coverage.

## Finding files

Each file contains exactly two top-level objects:

- `function.source`: compiler-snapshot source for the function, or null when unavailable.
- `function.mir`: complete function MIR, including local types and cleanup annotations. Context repeats for different candidates in the same function.
- `finding.id`: `rc-<unit>-<index>`, unique within this unit output. Combine it with its package-qualified report path; IDs are not stable across runs.
- `finding.function`: full rustc function path.
- `finding.bug_type`: `memory_leak`.
- `finding.location`: mapped function span, not an exact leaking instruction.
- `finding.return_site`: return basic block, mapped terminator span and MIR terminator.
- `finding.source_sites`: calls matching the source heuristic encountered so far in topological traversal, with block, location and MIR. They are candidate ownership-transfer calls, not necessarily allocations, active sources for each local, or sites on a single execution path.
- `finding.solver.result`: `unsat`, matching the warning condition.
- `finding.solver.constraints`: actual asserted solver constraints at that check, excluding goal-only debug markers. It includes accumulated earlier block and return constraints. No unsat core, satisfying model, per-assertion provenance or executable path is exported.
- `finding.locals`: non-declared or tainted locals after return-value handling. Each contains MIR local index, optional source name, actual local type, state, bit width, symbolic ownership expression, abstract heap layout, taint type descriptions and `checked_at_return`. Taint lists are type-based abstractions rather than allocation identities. `checked_at_return` identifies initialized non-argument locals with nonzero bit width required to have zero ownership bits. The return local is handled separately by the detector; arguments are excluded from these final zero requirements.

Locations use a real local source path and one-based character coordinates, with an exclusive end. `source_digest` is `fnv1a64:<hex>` over the compiler's entire source-file snapshot; it is a freshness hint, not a cryptographic integrity guarantee. Resolve relative paths against the analysis working/package directory. Macros may map outside the function or package; null locations remain unknown. Inspect live source for freshness before repairing.

## Fixed detector boundaries

- Analysis is intraprocedural and based on heap-ownership layouts and call-signature heuristics. It does not prove the actual ownership contract of arbitrary callees, custom destructors or FFI.
- Cyclic CFGs are skipped, including cycles on cleanup edges. Normal traversal excludes unwind/cleanup edges. Panic-only leaks are outside that traversal.
- Branch joins merge ownership with bitwise AND and combine type-based taint. Branch predicates are not modeled as a proven feasible execution path.
- Source calls have one moved argument with an owning layout and a pointer/reference-containing destination. Recovery uses pointer/ownership type matching. Neither heuristic identifies a unique concrete allocation or proves correct recovery/deallocation.
- A warning requires both `unsat` and a seen source call. Unsatisfiability can arise from other modeling constraints. A function-wide solver is reused across topological traversal and multiple returns, without isolating returns; later warnings may depend on earlier checks.
- `sat`, no matching source, no visited return, unsupported operations, ignored MIR or skipped functions cannot prove absence of leaks. Only some unsupported states are recorded; the absence of markers does not establish complete coverage.
- Solver checks can time out or return unknown; these are coverage gaps, not negative findings. Never turn an unknown check into a supported/refuted leak verdict without additional evidence.

Read source and relevant callers/callees to resolve fixed evidence gaps. Repeating export cannot add unimplemented path feasibility, allocation identities or unsat-core provenance.

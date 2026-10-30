# Review and repair rules

## Explain each candidate with verifiable evidence

Read the profile's status and limitations, then read each `sd-*.json`. Each file's `function` contains the owning function's source and MIR, while `finding` contains the current candidate and its witness. Reconstruct the reasoning: who owns the resource, what invalidates it, which value is considered related to it, and whether a subsequent use, repeated release, or dangling pointer at exit occurs. Distinguish analyzer assumptions from facts established by the source.

Prioritize information that can change the conclusion:

1. **Resource identity**: can the two locals or fields actually refer to the same allocation? Could field collapsing, unknown calls, or merged summaries make abstract aliasing too conservative?
2. **Path feasibility and event order**: can the release and trigger occur in one execution? Are branch conditions contradictory? Are additional loop iterations needed? Do cleanup paths and the panic strategy permit this sequence?
3. **Ownership and lifetime**: do Move, return, container ownership, borrowing, reference counting, custom `Drop`, `ManuallyDrop`, `forget`, raw-parts APIs, or FFI change release responsibility and lifetime?
4. **Subsequent events**: is the value reassigned or reinitialized before use? Is the pointer's numeric value used, or the resource it points to? Is a later operation actually a release or merely logic with no release effect?
5. **Evidence provenance**: does the report identify an exact event, a basic-block mapping, or a function span? Is aliasing an approximation or established by the implementation? Are external implementations or contracts unavailable?

First read source, MIR, types, and callers directly relevant to these questions. Export again with the same scope only when fresh collection can improve the material, for example when reports are stale, export was previously disabled, the version is outdated, or snapshot capture failed. For fixed gaps such as unavailable branch constraints or full alias derivations, read more source or add focused tests when useful; retain `inconclusive` if evidence remains insufficient. Do not loop over the same fixed gap or substitute a different scope that makes the warning disappear.

## Three assessments

| Assessment | Required evidence |
| --- | --- |
| `supported` | Source and evidence support the resource relationship, invalidation, subsequent dangerous operation, and feasible order; describe concrete trigger conditions and impact |
| `refuted` | Concrete evidence contradicts at least one essential premise, such as mutually exclusive conditions, distinct resources, correct ownership transfer, or reinitialization before use |
| `inconclusive` | Reachability, resource identity, external implementation, or another essential fact is unavailable, so the candidate cannot yet be supported or refuted |

A single execution without a crash, inability to run a reproducer, low `confidence`, or missing analyzer context does not independently justify `refuted`. Likewise, `confidence` of 99, membership in the same alias set, or the presence of unsafe source does not independently justify `supported`.

For a merged UAF/DF finding, only one dangerous operation may be established. Explain which subclaims are supported or refuted; do not discard one because the other fails. For dangling pointers, check whether the resource becomes invalid before the returned pointer or relevant argument is used and whether the pointer can escape to that context. Seeing `drop` near function exit alone is insufficient.

## Review records

Deliver Markdown as needed. When traceable files are useful, write one entry per candidate to `reviews.jsonl` outside unit report directories, for example `.rapx-ai/reviews.jsonl`. Fields may follow this example:

```json
{
  "report_path": ".rapx-ai/before-001/demo-lib/sd-demo-lib-0.json",
  "finding_id": "sd-demo-lib-0",
  "assessment": "inconclusive",
  "explanation": "The first release and possible alias are recorded, but the called implementation is unavailable, so it is unclear whether the later operation reads freed memory.",
  "evidence": [".rapx-ai/before-001/demo-lib/sd-demo-lib-0.json: finding.drop_site", "src/lib.rs:42"],
  "remaining_questions": ["How the called function uses the pointer and what ownership contract applies"],
  "repair_proposal": null,
  "repair_status": "not_attempted"
}
```

This illustrates the record shape, not a predetermined answer for the current project. Paths are relative to the target package directory. Locate a JSON finding using both its actual report path and finding ID: identically named crates in different packages can produce the same IDs. For cross-package summaries, use package-qualified or absolute paths, and reference actual archive paths after moving reports. For text warnings without report IDs, construct a temporary anchor from the original log's function, issue kind, release site, and trigger site, and state its origin. Evidence references must locate actual files or report fields.

## Repair and validate

When repairs are requested, prioritize restoring correct ownership, resource lifetime, or operation order. Examples include assigning one final release owner to an allocation, extending the actual resource's lifetime, completing access before invalidation, or reestablishing a valid value. Choose based on the code; do not treat `forget`, `ManuallyDrop`, or extra cloning as universal fixes.

Before editing, verify that the target source still matches the reviewed version. Existing repair authorization remains valid; do not ask again for ordinary local changes. If the user requests analysis only, provide proposals without starting repairs.

For an authorized repair or rescan, move each package's relevant `<crate>-<kind>/` directories into a baseline location such as that package's `.rapx-ai/before-001/`. Confirm that reports, the top-level command, and exit status are preserved and that the original unit paths no longer exist. Verify source and archive destinations, preserving package hierarchy to avoid collisions. RAPx does not clear or overwrite existing directories; copying reports while keeping the original directory causes the next run to warn and skip analysis. Preserve original material rather than automatically deleting directories to bypass warnings.

After repairs, retain the actual:

- Changes and associated findings, with a patch or version diff when useful.
- Compilation and relevant test commands and their exit results.
- Newly generated SafeDrop reports and analysis statuses in each package's unit directories. Combine these with the actual Cargo exit status and directory-exists warnings to verify that this run analyzed the target code. Archive and move current unit directories before another rescan.
- Semantic matching of old, remaining, and new findings under the same configuration.

A disappearing warning is only part of validation. Confirm that the original dangerous relationship is eliminated, compilation and applicable tests pass, and a changed detection scope has not hidden the issue. If the rescan did not analyze the code, the configuration changed, results are incomplete, or matching is ambiguous, report validation as incomplete and preserve the issue and failure evidence.

Do not rewrite original reports to claim a false positive or successful repair. Do not clear findings by disabling SafeDrop, reducing path limits, skipping targets, adding suppressions, deleting tests, or leaking resources without justification. If two local attempts do not resolve the issue, describe the failure, current changes, and further information needed.

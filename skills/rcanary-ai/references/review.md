# Reviewing and repairing rCanary candidates

## Follow the ownership obligation

Read the profile and its function-specific limitations before the candidate. The return check and source sites anchor the investigation. Determine:

1. Which allocation/resource exists, where it is created, and which owner is responsible for its release.
2. Whether a source call really relinquishes ownership (`Box::into_raw`, raw-parts conversion, or an equivalent API), or merely borrows, returns a non-owning reference, or transfers responsibility elsewhere.
3. How ownership flows through copies, moves, fields, containers, raw pointers, FFI, returned values and caller contracts. A raw pointer can carry release responsibility by contract; it need not own according to its Rust type.
4. Whether every relevant feasible path recovers or releases the same resource, and whether custom `Drop`, `Box::from_raw`, an allocator-specific free function, a registry, caller or long-lived owner performs the release.
5. Whether the candidate combines mutually exclusive branches, an unrelated source call, stale taint, an unsupported local or constraints from a different return check.

Source-site order is analysis traversal order. Symbolic bits and type taint do not establish equal runtime addresses, a concrete residual allocation or branch feasibility. `unsat` is inconsistency in the whole accumulated constraint set, not a proof that a specific source leaked.

An intentional process-lifetime allocation can still be unreleased memory, but may be permitted behavior. Distinguish mechanism from the user's intended lifetime policy. Avoid inserting a free operation until actual ownership and lifetime are understood.

## Assessments and records

| Assessment | Required basis |
| --- | --- |
| `supported` | Source and contracts establish a feasible resource acquisition/ownership transfer and a path that loses required release responsibility without eventual recovery or deallocation |
| `refuted` | Concrete evidence contradicts an essential premise: valid ownership transfer, correct recovery and release, incompatible path conditions, or an abstraction mismatch that explains the warning |
| `inconclusive` | Allocation identity, reachable path, external release contract, intended lifetime or another necessary fact remains unavailable |

No crash, a single successful run, low resource usage or an unsatisfiable model alone is insufficient to settle the assessment. Explain the specific failing premise for a false positive. Multiple warnings in one function may stem from the same resource or accumulated return constraints; preserve an entry for each original ID while grouping repairs.

Deliver findings in Markdown. When traceable files are useful, save reviews outside unit directories, for example `.rapx-ai/rcanary/reviews.jsonl`:

```json
{
  "report_path": ".rapx-ai/rcanary/before-001/rcanary-demo-bin/rc-demo-bin-0.json",
  "finding_id": "rc-demo-bin-0",
  "assessment": "inconclusive",
  "explanation": "A raw pointer escapes to an external registry whose release contract is unavailable.",
  "evidence": ["src/main.rs:42", "finding.source_sites[0]", "finding.return_site"],
  "remaining_questions": ["Does registry removal release this allocation, and who calls it?"],
  "repair_proposal": null,
  "repair_status": "not_attempted"
}
```

Use actual report paths, IDs and evidence. Keep path references correct after archiving reports; qualify paths by package when summarizing multiple packages. For text-only diagnostics, use an explicitly log-derived anchor containing the function and source/return locations.

## Repair without changing the intended lifetime

For analysis-only requests, provide proposals. For repair requests, apply focused changes within existing authorization after checking source freshness. Choose a repair based on the actual resource contract:

- Keep the resource in a normal RAII owner when the raw conversion is unnecessary.
- Transfer it into an owner with a correct destructor, or recover it exactly once with the matching allocator/type before deallocation.
- If ownership escapes, make the receiver's release responsibility explicit and verify the relevant caller/receiver behavior.
- Preserve borrowing lifetimes, aliases, FFI obligations and observable behavior. Blindly adding `drop(pointer)` does not free its pointee; blindly adding `Box::from_raw` can introduce use-after-free, double free or allocator mismatch.

Before repair/rescan, archive and move relevant unit directories as described in the skill. Keep detector outputs immutable and keep review records separate. After changes, retain the patch and actual compilation, applicable tests and same-scope `check -M` results.

Verify that the resource is correctly released or transferred, each required unit was freshly analyzed, original candidates are semantically resolved, and no related candidates or regressions were introduced. If the rescan is skipped, unknown or incomplete, report that explicitly. Do not claim resolution solely from fewer warnings or changed IDs. After two unsuccessful local attempts per group, preserve the evidence and explain the remaining issue rather than retrying indefinitely.

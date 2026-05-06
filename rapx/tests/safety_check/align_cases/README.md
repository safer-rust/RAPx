# Senryx Align Cases

This crate contains focused examples for the current Senryx `Align` checker.

Run:

```bash
cargo check
cargo rapx check --verify
```

The examples are written around the current checker capabilities in
`rapx/src/analysis/senryx/verification/align.rs`.

| Function | Expected Align Result | Checker Evidence |
| --- | --- | --- |
| `pass_from_align_contract_fact` | Pass | RAPx `Align(ptr, u32)` precondition is stored as a contract fact. |
| `pass_from_reference_source` | Pass | Raw pointer comes from a Rust reference / aligned modeled object. |
| `pass_from_typed_element_add` | Pass | `ptr.add(index)` uses element-sized stride, preserving alignment. |
| `pass_from_runtime_is_aligned_guard` | Pass | `ptr.is_aligned()` true branch refines pointer alignment state. |
| `fail_from_u8_object_cast` | Fail | `u8` object alignment is weaker than required `u32` alignment. |
| `fail_from_unconstrained_byte_add` | Fail | `byte_add(byte_offset)` has byte stride and unconstrained offset. |
| `fail_from_negative_is_aligned_guard` | Fail | The read happens on the branch where alignment is not known to hold. |

Only the `Align` property is described here. Other contracts attached to the
same unsafe APIs, such as `ValidPtr` or `Typed`, may still report separately.

---
name: rapx-verify
description: Use when running RAPx verification (`cargo rapx verify`) on a Rust crate to check that unsafe call sites satisfy their callee's safety preconditions (SOUND/UNSOUND verdicts). Std unsafe APIs are auto-checked from bundled contracts; only user-defined unsafe fns need #[rapx::requires]/#[rapx::invariant]/pred! annotations.
---

# RAPx Contract Verification

`cargo rapx verify` checks every unsafe call site against its callee's safety preconditions and reports `SOUND` / `UNSOUND`. Std unsafe APIs are resolved automatically from bundled contracts; you annotate only your own `unsafe fn`s. Docs: <https://safer-rust.github.io/RAPx-Book/8-verification.html>

## Setup

```rust
#![feature(register_tool)]
#![register_tool(rapx)]
```

```toml
[dependencies]
rapx-macros = "0.7.34"   # only needed for pred!
```

## Annotations

- `#[rapx::requires(P, ...)]` — precondition.
- `#[rapx::invariant(P, ...)]` — struct invariant.
- `#[rapx::verify]` — only for `--mode targeted`; default `scan` auto-detects targets.
- `any(D1, D2)` — disjunction; `any(Null(p), (P1, P2, ...))` = null guard (conjuncts hold when `p` non-null, vacuous when null).
- optional `kind = "hazard" | "option"`.

## Properties

| Tag | Args |
|---|---|
| `NonNull` | `(ptr)` |
| `Align` | `(ptr, Ty)` |
| `Allocated` | `(ptr[, Ty, n[, alloc]])` |
| `InBound` | `(slice, idx)` / `(ptr, Ty, n)` |
| `Init` | `(ptr, Ty, n)` |
| `Typed` | `(ptr, Ty)` |
| `ValidNum` | `(pred)` / `(value, interval)` |
| `ValidCStr` | `(ptr, len)` |
| `NonOverlap` | `(a, b, Ty, count)` |
| `Owning` | `(ptr)` |
| `Alive` | `(ptr, 'a)` |
| `Pinned` | `(ptr, 'a)` |
| `Alias` | `(p1, p2)` — hazard |
| `Size` | `(Ty, c)` |
| `NoPadding` | `(Ty)` |
| `Unwrap` | `(x, Some/Ok/Err)` |
| `Null` | `(ptr)` — only in `any(...)` |

Compounds: `Deref` = `Allocated && InBound`; `ValidPtr` = `Size(T, 0) || Deref`; `Ptr2Ref` = `Init && Align && Alias`; `ZstAwareInBound(ptr, T, end_or_len)` = ZST-safe `InBound`.

## Custom contracts (`pred!`)

```rust
use rapx_macros::pred;

pred!(Readable(p: Ptr, T: Ty, n: Expr) { NonNull(p) && Align(p, T) && Allocated(p, T, n) && Init(p, T, n) });

#[rapx::requires(Readable(ptr, u8, len))]
unsafe fn read_byte(ptr: *const u8, len: usize) -> u8 { unsafe { *ptr } }
```

- Body: `&&` / `||` / `( ... )`. Param roles: `Ptr | Ty | Expr | Ident`.
- Exprs: `size_of(T)` (no turbofish), `align_of(T)`, `len(x)`, `min/max`, `index_access(s, i)`, `if c { a } else { b }`, `T::MAX`/`isize::MIN`.
- `!x.is_empty()` = `len(x) != 0`; projections `.0`/`.field`, `.unwrap_some()`, `.iter()`, `.len`.

## Run

```shell
cargo +nightly install rapx          # from crates.io (needs nightly + rustc-dev)
cargo rapx verify                    # scan (default)
cargo rapx verify --mode targeted    # only #[rapx::verify] fns
cargo rapx verify --prepare-targets | --debug-contracts | --crate C --module m::n
```

Output: `result: SOUND` / `UNSOUND (k unproved, h hazard)` / `UNKNOWN`.

# Rust backend feasibility spike

- Date: 2026-09-21
- Toolchain exercised: Rust/Cargo 1.95.0, `x86_64-unknown-linux-gnu`
- Fixture: `rust/axiom-spike`
- Status: execution design is feasible; Kani and production worker remain gated

## Executed findings

The dependency-free fixture builds and tests with `cargo test --locked --offline`.
It demonstrates:

- reconstruction of two equivalent `Stack<i32>` worlds without requiring `Clone` on
  the stack type;
- legal `&mut self`, `&self`, and owned-`self` operation shapes;
- an owned builder operation that consumes and returns state;
- `Option` and `Result` as ordinary return values;
- ordinary panic recovery through `catch_unwind`;
- one explicit trait implementation selected with static dispatch;
- an interior-mutability example whose state is visible only through an explicit
  snapshot;
- a compile-fail doctest showing that use after move is rejected by Rust rather than
  being delegated to runtime checking.

These results support retaining one language-neutral `Call` node plus input passing
modes. They do not justify erasing ownership: `owned`, `shared_borrow`, and
`mutable_borrow` remain mandatory operation metadata.

## Protocol and harness conclusions

A Rust backend should generate a harness crate because stable Rust has no Java-like
reflection for arbitrary declared operations. One compiled worker should contain a
batch of statically typed wrappers. Recipes can reconstruct each side independently;
legal aliases should use generated lexical borrows, while simultaneous mutable aliases
must be rejected before source generation.

Cargo's locked/offline mode works for the no-dependency spike. A production cache key
must include compiler version, target triple, Cargo.lock, features, target sources,
manifest, adapter, and generated harness digests. The target project must never be
modified.

## Unresolved gates

- Kani is not installed in the execution environment, so pure/mutable proof harnesses,
  unwind completeness, concrete playback, and witness-to-recipe translation are not
  evaluated. No Kani proof claims are made.
- A versioned Rust adapter trait and generated JSON-lines worker are not implemented.
- Abort, memory exhaustion, malicious build scripts, compile-cache isolation, and
  100/1,000/10,000-term compile-cost measurements remain production-spike work.
- Hosted Rust builds remain disabled. `--locked --offline` is reproducible but does
  not make `build.rs` safe.

Decision: the common IR need not be revised, because it already stores concrete type
IDs, post-state projections, and passing modes. Proceed with a separately gated Rust
execution beta only after the generated harness and build sandbox are designed. Defer
Kani without blocking execution support.


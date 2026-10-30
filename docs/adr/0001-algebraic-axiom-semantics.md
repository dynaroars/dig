# ADR 0001: Semantics for algebraic API axioms

- Status: Accepted
- Date: 2026-09-21
- Decision owners: DIG maintainers

## Context

DIG currently reports predicates over program state at source locations. Algebraic
API axioms are different: they relate the results and effects of two typed operation
terms for every admissible initial world. Reusing the numerical-invariant model would
hide important facts about mutation, exceptions, sampling, and proof scope.

The historical `algebraicaxioms` prototype demonstrates useful search techniques,
but its generated source files, process model, runtime type inspection, and Boolean
pass/fail output do not define a safe or reproducible contract. This ADR fixes that
contract before a worker implementation is selected.

## Decision

### Analysis boundary

An axiom run consumes a versioned, declarative manifest and produces a versioned
result document. The language-neutral orchestrator works only with stable string IDs,
serialized recipes, and outcomes. Target imports, reflection, compilation, and API
execution occur in isolated language workers.

API axioms and numerical invariants have distinct internal representations. They may
later share a reporting-level `Finding` and `RunResult` envelope.

### Operations and types

Every type has a manifest-unique stable ID. Compatibility is **exact type matching**
in schema version 1. Subtyping or coercion is allowed only when an operation declares
an explicit compatibility adapter; it is never inferred from a Python or JVM runtime
class hierarchy.

Every operation has a stable ID, language binding, kind, ordered input types, return
type, positive enumeration cost, and explicit effects. Instance receivers are the
first logical input. `mutates` contains logical input indexes, including receiver
index `0`. A `None`/`void` return does not imply mutation. `pure = true` requires an
empty effect set and may be checked dynamically.

Java overloads are selected by the complete declared parameter list in the binding.
Python decorators and wrappers are not unwrapped implicitly: the binding names the
callable that will execute, while the manifest signature remains authoritative.

### Terms and equations

The term IR has three immutable variants:

- `variable`: type ID and non-negative index;
- `constant`: type ID and canonically encoded value;
- `call`: operation ID, a projection, result type ID, and ordered child terms.

A call projection is either `return` or `post_state(input_index)`. This is required
for mutable composition: Java `Stack.push` returns the pushed item, but the nested
receiver in `pop(push(stack, item))` is the post-state of `push` input 0. The explicit
post-state projection has type `stack`; it does not pretend that the Java method's
declared return type changed. Display renderers may omit the projection in familiar
mutator notation when it is unambiguous. A void call has no `return` projection but
may have a post-state projection for each declared mutated input.

Term identity is structural. Stable JSON is UTF-8 with sorted object keys and compact
separators when hashed. Enumeration ordering is `(cost, type_id, canonical_json)` and
must not depend on hash iteration order. Call cost is its operation cost plus child
costs; variables and constants cost zero.

An equation requires equal result types. Equality is symmetric, so its stored form
puts the smaller term under the enumeration ordering on the left. Variable indexes
are renamed to first-occurrence order independently per type. Children of an
operation declared commutative are sorted by term ordering after type checking.

### Aliasing and ownership

Occurrences with compatible type IDs may share a root. Alias cases are canonical set
partitions encoded by restricted-growth strings (`[0, 0]`, `[0, 1]`, ...), not all
integer assignments. A recipe names each constructed root and each variable refers
to a root ID. Workers must preserve this graph within a world.

The schema reserves an input passing mode (`owned`, `shared_borrow`, or
`mutable_borrow`) so Rust can reject illegal terms. Python and Java inputs default to
`owned` for values and use manifest effects for mutable roots. Ownership legality is
part of type checking, not an execution-time guess.

### Evaluation and observable equality

The two sides of an equation execute in independently reconstructed, equivalent
worlds. A worker must not evaluate the right side against state mutated by the left.
Reconstruction from deterministic recipes is preferred to copying.

An outcome records exactly one execution status (`returned`, `threw`, `timed_out`,
`crashed`, `protocol_error`, or `unsupported`), the encoded return value when one was
produced, snapshots of all declared mutated roots, observable public alias relations,
a normalized exception when thrown, and bounded stdout/stderr digests.

For returned outcomes, equality means equal encoded projected values, snapshots, and
declared observable aliases under the configured comparators. Snapshot/observer IDs define
the claim: a result asserts equality only under those observations. Opaque mutable
types without a snapshot or custom comparator are rejected by manifest validation.
Identity is not a default comparator.

### Exceptions and partial operations

The default exception policy is `common_domain`:

- two returns are compared normally;
- one throw and one return refutes the equation;
- two throws are an invalid-domain sample and provide no supporting evidence;
- timeouts, crashes, protocol errors, and unsupported encodings are analysis errors,
  never passing samples.

`same_exception` may be explicitly selected. It treats two exceptions with equal
normalized class and adapter-selected payload as equivalent behavior, and the result
must display that policy. Every candidate requires the configured minimum number of
non-exceptional samples.

### Determinism and evidence

Schema version 1 supports deterministic APIs. Validation replays a deterministic
subset of recipes. A disagreement quarantines affected candidates as `ERROR`; it is
not smoothed over statistically.

Discovery and held-out validation use independently derived random streams. Verdicts
are monotone within a run:

- `REFUTED`: a replayable counterexample was observed;
- `CANDIDATE`: survived discovery only;
- `VALIDATED`: survived the independent validation campaign;
- `PROVED`: a named sound verifier proved the displayed scope;
- `ERROR`: infrastructure prevented a meaningful result.

Random or bounded testing never yields `PROVED`. Proof evidence always states
`finite-domain`, `model`, or a named implementation scope and includes assumptions,
limits, verifier identity/version, and an artifact digest. Truncated exhaustive
enumeration is validation, not proof.

### Bounds and defaults

Version 1 defaults are deliberately conservative and are recorded in every result:

| Limit | Default |
|---|---:|
| maximum call cost | 3 |
| variables per type | 2 |
| terms per type | 1,000 |
| emitted candidates | 10,000 |
| discovery recipes | 100 |
| validation recipes | 1,000 |
| minimum valid samples | 20 |
| case timeout | 1 second |
| worker batch timeout | 30 seconds |
| worker memory | 512 MiB |
| captured stdout/stderr | 64 KiB each |

Caps are deterministic. Reaching one adds a truncation diagnostic and prevents an
exhaustive-proof claim.

### Versioning and forward compatibility

Documents contain integer `schema_version`. Readers accept only versions they
implement and reject unknown versions before importing target code. Unknown fields
are rejected in version 1, except under `extensions`, whose reverse-DNS keys and
values are preserved but ignored by the core. Protocol peers additionally exchange a
protocol version before work begins.

### Threat model

Targets, adapters, recipes, manifests, compiler output, and worker output are
untrusted. They may loop, crash, allocate excessively, print indefinitely, traverse
paths, spawn processes, mutate globals, or attempt network access. The parent must
use argument-vector subprocess calls (never `shell=True`), bounded messages and
output, run-specific directories, deadlines, process-group termination, and resource
limits. Hosted execution additionally requires no network, read-only inputs, path
confinement, and administrator-installed adapters. A manifest is validated before
any target code is loaded or compiled.

## Consequences

The same IR and evidence model can serve Python, Java, and a later Rust backend. Some
apparently useful targets are rejected until they supply complete snapshots or
serializable recipes. Reports are more verbose, but cannot accidentally present
random testing as a universal proof.

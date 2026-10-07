# API axiom analysis

DIG's API axiom mode discovers typed equations over Python and Java API calls. It is
separate from numerical invariant inference and uses an explicit TOML manifest.

## Quick start

Run the checked-in Python stack example:

```console
.venv/bin/python -O src/dig.py \
  --axioms docs/axioms/examples/python-stack.toml \
  --seed 42 \
  --json-output /tmp/python-stack-axioms.json
```

The equivalent Java example needs a full JDK (`java` and `javac`):

```console
.venv/bin/python -O src/dig.py \
  --axioms docs/axioms/examples/java-stack.toml \
  --java java --javac javac \
  --seed 42
```

The checked-in runner supports JDK 17 or newer. The main DIG image uses JDK 21;
the smaller Debian Bookworm web image uses its supported JDK 17 package.

The examples declare a deliberately small finite campaign. Real manifests should
increase discovery and validation cases and provide generators for domains that are
not finite.

## Reading verdicts

- `REFUTED` has a concrete recipe where return value, observable post-state,
  exceptions, or aliases differ.
- `CANDIDATE` survived discovery but lacks sufficient independent validation.
- `VALIDATED` survived a distinct held-out campaign. It is not a proof.
- `PROVED` is reserved for a named verifier and displayed scope, such as an exactly
  enumerated finite domain.
- `ERROR` means execution infrastructure or determinism checks failed; it never
  counts as supporting evidence.

Both-side exceptions are outside the common defined domain by default. A law needs
the manifest's minimum number of non-exceptional cases, preventing exception-only
laws from surviving vacuously.

## Mutable operations

Mutation is declared with logical input indexes; receiver index `0` is used for an
instance method. Calls explicitly select either the language return or a mutated
input's post-state. Thus Java `Stack.push` may return an item while this term remains
type-correct:

```text
pop(post_state[0](push(stack_0, item_0))) == item_0
```

The familiar renderer may describe the same idea as `pop(push(stack, item))`, but the
serialized term always retains its projection.

Opaque mutable types need a deterministic recipe factory and snapshot. The Python
example uses:

```toml
[[types]]
id = "stack"
python_type = "python_stack:Stack"
from_recipe = "python_stack:stack_from_recipe"
snapshot = "python_stack:stack_snapshot"
opaque = true
```

The manifest is validated before the target module is imported. Target imports and
calls occur only in a worker child process.

## Replaying a counterexample

Given a result containing a `REFUTED` finding:

```console
.venv/bin/python -O src/dig.py \
  --axioms path/to/spec.toml \
  --replay-counterexample path/to/result.json \
  --finding axiom-0004
```

Replay reconstructs fresh worlds from the stored minimized recipe and exits
successfully only when the mismatch is reproduced.

## Current boundaries

- Python and Java deterministic finite-recipe campaigns are implemented.
- Python workers enforce bounded output, batch deadlines, restart limits, and pure
  declaration checks. JVM workers enforce heap/stack limits, parent deadlines, and
  bounded output.
- The finite-domain verifier is available as a library plugin; CLI proof promotion is
  not yet exposed.
- Hosted jobs currently accept only administrator-installed Python fixtures through
  the allowlisted `axioms.fixtures` module; arbitrary uploaded adapters and Java
  artifacts remain disabled.
- A restricted pure/scalar SMT model verifier exists with explicit `model` scope.
  Randomized generator APIs, mutable SMT transition models, Rust, and general hosted
  artifacts remain later plan gates.

See the [semantic ADR](../adr/0001-algebraic-axiom-semantics.md),
[worker protocol](protocol-v1.md), and
[integration plan](../../ALGEBRAIC_AXIOMS_INTEGRATION_PLAN.md) for the precise
assurance boundary.

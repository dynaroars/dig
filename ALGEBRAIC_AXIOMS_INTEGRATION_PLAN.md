# Algebraic API Axiom Inference for DIG

## Implementation status

Started 2026-09-21. The specification slice is in progress:

- [x] Record legacy provenance, intended behavior, known defects, and the no-copy
  license constraint in `docs/axioms/legacy-inventory.md`.
- [x] Accept the initial semantic contract and threat model in
  `docs/adr/0001-algebraic-axiom-semantics.md`.
- [x] Add version-1 manifest/result JSON Schemas and a worker protocol draft under
  `docs/axioms/`.
- [x] Add a golden Java stack manifest/result pair, including explicit mutable
  post-state projection in the term IR.
- [x] Add target-free TOML loading and semantic validation in `src/axioms/spec.py`.
- [x] Add golden Python examples and cross-language serialization fixtures.
- [x] Implement the immutable language-neutral model and canonical JSON encoding.
- [x] Implement canonical alias partitions and deterministic, typed, cost-bounded
  term enumeration with explicit truncation reporting.
- [x] Add an isolated Python JSON-lines worker for deterministic recipes, target
  exceptions, bounded output capture, batching, and parent-enforced timeouts.
- [x] Add observational signatures, a pairwise test oracle, finite recipe campaigns,
  independent discovery/validation splits, and structured evidence verdicts.
- [x] Add a checked-in, dependency-free JVM worker and cross-backend stack
  conformance tests for normalized returns, state, and exceptions.
- [x] Add the initial finite-domain exhaustive verifier with explicit common-domain
  proof scope and replayable refutations.
- [x] Add a restricted pure/scalar SMT-model verifier whose proofs are explicitly
  scoped to user-supplied logical models rather than target implementations.
- [x] Add the backwards-compatible `dig.py --axioms` mode with human and stable JSON
  output while retaining the positional numerical invocation.
- [x] Add the first hosted job path for administrator-installed Python fixtures,
  structured JSON consumption, strict binding allowlisting, and existing Docker
  network/memory/process/time limits.
- [x] Run the bounded Rust feasibility spike for ownership modes, reconstruction
  without `Clone`, panic recovery, concrete trait dispatch, interior-mutability
  snapshots, and locked/offline Cargo builds; record Kani as unavailable rather than
  making an untested proof claim.
- [x] Add shrinking, replay commands, nondeterminism checks, worker recycling, and
  mutation-declaration checks to complete the Python/validation gates.
- [x] Exclude the unlicensed archival checkout from distribution while retaining its
  pinned provenance and clean-room behavior inventory; production imports are
  forbidden and tests do not depend on it.

The explicit call projection is a refinement discovered during implementation. It
keeps terms type-correct when a mutator's language return differs from the mutated
receiver (for example, Java `Stack.push`).

## 1. Executive decision

DIG should gain a new **API axiom analysis** alongside its existing program-state
invariant analysis. The new analysis discovers laws over typed API calls, for
example:

```text
pop(push(stack, x)) == x
size(push(stack, x)) == size(stack) + 1
reverse(reverse(xs)) == xs
```

The implementation should preserve the useful ideas in `algebraicaxioms/`—typed
term enumeration, alias-pattern enumeration, mutation awareness, generated tests,
and redundancy pruning—but should not use that code as the new architecture. It is
an unmaintained prototype tied to old Python typing behavior, generated files in the
working directory, and pass/fail random testing.

The target design is:

1. one language-neutral term, operation, effect, and axiom representation;
2. one bounded candidate-generation engine;
3. separate isolated Python and Java execution workers;
4. an evidence and verdict model that never presents random testing as proof;
5. pluggable validators and verifiers;
6. shared DIG CLI, configuration, reporting, serialization, web sandbox, and
   reproducibility infrastructure.

API axioms should not be forced into DIG's current `DInvs` representation. A state
invariant is a predicate at a source location; an API axiom is a quantified relation
between executions of operation terms. Both can implement a common reporting-level
`Finding` protocol without sharing their internal semantics.

## 2. Goals and initial scope

### Required goals

- Support Python and Java APIs through the same inference core.
- Support pure functions, instance methods, static methods, constructors, observers,
  and mutators.
- Discover typed unconditional equalities first.
- Handle aliasing between arguments of the same type.
- Define meaningful equality for return values and mutated state.
- Treat partial operations and exceptions explicitly.
- Separate discovery examples from independent validation examples.
- Produce deterministic, replayable counterexamples.
- Support finite exhaustive validation and pluggable sound proof backends.
- Integrate with DIG's CLI, result output, Docker/web execution, logging, seeds,
  timeouts, and tests.
- Run on Python 3.14, matching DIG's declared runtime.

### Deferred goals

These should be supported by the architecture, but not block the first useful
release:

- conditional axioms such as `not empty(s) => top(pop(s)) == ...`;
- inequalities or arithmetic relationships between observations;
- concurrent, asynchronous, nondeterministic, or I/O-heavy APIs;
- inference over APIs whose state cannot be constructed or observed;
- fully automatic universal proof of arbitrary Python or Java implementations;
- cross-language equivalence between a Python implementation and a Java
  implementation.

## 3. Semantic contract to define before coding

The largest risk is not implementation—it is reporting an ambiguous or unsound law.
Write an architecture decision record (ADR) that fixes the following semantics.

### 3.1 Operations

Each operation declaration records:

- a stable operation ID;
- display name;
- language binding;
- kind: constructor, instance method, static method, or free function;
- ordered input types and return type;
- receiver position, if any;
- effect set: which arguments may be mutated;
- whether the operation is declared pure;
- whether argument order is commutative;
- exception policy;
- optional precondition;
- cost used by bounded enumeration.

Do not infer mutation from a `None` return value. Mutation is an explicit part of the
specification and can later be checked by a mutation detector.

### 3.2 Terms and variables

A term is an immutable, typed tree:

```text
Variable(type, index)
Call(operation_id, children)
Constant(type, encoded_value)       # optional in the first release
```

Term identity must be structural and independent of Python object identity. Store
types and operations by stable IDs, not imported class objects. This makes terms
serializable and usable by both the Python and JVM workers.

Use a cost bound rather than only “number of functions.” The default call cost can
be one, while expensive constructors or observers can be assigned larger costs.

### 3.3 Aliasing

Variables of a compatible type may denote the same input object. Enumerate canonical
set partitions rather than all raw integer assignments. For two stack occurrences,
test both:

```text
(stack_0, stack_0)
(stack_0, stack_1)
```

Canonicalize variable renamings so equivalent laws are not emitted multiple times.
The value recipe sent to a worker must preserve the chosen alias graph.

### 3.4 Evaluation of mutable terms

An equation `lhs == rhs` is evaluated from two independently constructed but
equivalent initial worlds. Never evaluate the right side on state mutated by the
left side.

Each evaluation produces an `Outcome`:

```text
Outcome(
    return_value,
    observations_by_root,
    exception,
    stdout_digest,
    timed_out,
)
```

The comparison normally includes:

- return values;
- configured observations of every mutated root object;
- alias relationships that are part of the public behavior;
- normalized exceptions, according to the declared policy.

For a void mutator, the observed post-state is its effective result. For an opaque
type, the spec must provide observers, a snapshot adapter, or a custom comparator;
ordinary object identity is not adequate.

### 3.5 Exceptions and partial functions

Use these default rules:

- both sides return: compare values and observable post-state;
- one side throws and one returns: counterexample;
- both sides throw: treat the sample as outside the common defined domain, not as
  evidence that the law holds;
- timeout, crash, protocol error, or unsupported serialization: infrastructure
  failure, never a passing sample.

Record exception class and a normalized payload for diagnostics. Allow a spec to
opt into “same exception is equivalent behavior,” but make that non-default and
visible in the result.

Require a configurable minimum number of valid, non-exceptional samples. This
prevents vacuous candidates for operations such as `pop(empty_stack)`.

### 3.6 Determinism

The first release supports deterministic APIs. During validation, replay a subset of
identical recipes and reject or quarantine nondeterministic operations. Later, a
custom distributional comparator can be added as a separate feature; it must not be
silently treated as ordinary equality.

## 4. Target architecture

```text
                           DIG CLI / web API
                                  |
                         Analysis dispatcher
                         /                  \
             numeric invariant run      axiom run
                                              |
                                      Spec validation
                                              |
                                  Typed term enumeration
                                              |
                                    Candidate selection
                                              |
             +--------------------------------+-------------------------------+
             |                                                                |
       Python worker                                                     JVM worker
             |                                                                |
       target package                                                    target classes
             +---------------------- outcome protocol -------------------------+
                                              |
                              discovery + held-out validation
                                              |
                                simplify / canonicalize
                                              |
                              optional verifier plugins
                                              |
                               findings + evidence report
```

Recommended package layout:

```text
src/
  axioms/
    __init__.py
    model.py              # IDs, types, operations, terms, equations
    spec.py               # manifest schema and validation
    enumerate.py          # typed, bounded term generation
    aliases.py            # canonical alias partitions
    signatures.py         # observational signatures / equivalence classes
    simplify.py           # normalization and redundancy removal
    outcomes.py           # result and exception comparison
    evidence.py           # verdicts, samples, counterexamples, provenance
    engine.py             # language-neutral orchestration
    protocol.py           # versioned JSON-lines worker protocol
    workers/
      base.py
      python_worker.py
      jvm_worker.py
    verify/
      base.py
      finite.py
      smt_model.py
  analysis_result.py      # common reporting-level RunResult/Finding protocol
```

The JVM worker may include a small checked-in Java helper project, for example:

```text
jvm/
  axiom-runner/
    src/main/java/...
    src/test/java/...
```

## 5. API specification format

Use a versioned TOML manifest for portable declarations, plus optional language code
for generators, snapshots, and comparisons. Do not make arbitrary executable Python
files the only configuration format because Java projects need the same schema.

Illustrative manifest—not the final schema:

```toml
schema_version = 1
language = "java"

[target]
classpath = ["target/classes"]

[[types]]
id = "stack"
java_class = "java.util.Stack"
generator = "example.StackRecipes#generate"
snapshot = "example.StackRecipes#snapshot"

[[types]]
id = "item"
java_class = "java.lang.Integer"
finite_values = [-2, -1, 0, 1, 2]

[[operations]]
id = "push"
binding = "java.util.Stack#push(java.lang.Object)"
kind = "instance_method"
receiver_type = "stack"
parameter_types = ["item"]
return_type = "item"
mutates = ["receiver"]

[[operations]]
id = "pop"
binding = "java.util.Stack#pop()"
kind = "instance_method"
receiver_type = "stack"
return_type = "item"
mutates = ["receiver"]
```

For Python, `binding` identifies `module:qualified_name`, and an optional adapter
module provides generators and observers. Resolve annotations with supported public
inspection APIs, but treat manifest declarations as authoritative when annotations
are missing or ambiguous.

Validate the manifest before importing or compiling target code. Diagnostics must
identify the manifest path and field.

## 6. Evidence and verdict model

Keep a simple top-level verdict while retaining detailed assurance evidence:

```text
REFUTED       a concrete counterexample was observed
CANDIDATE     survived discovery only
VALIDATED     survived an independent validation campaign
PROVED        a named sound verifier proved the stated scope
ERROR         analysis infrastructure failed
```

`CANDIDATE` and `VALIDATED` can map to DIG's existing `UNKNOWN` status when a common
three-valued view is needed. Do not overload `PROVED` for “passed many tests.”

Every surviving axiom should include:

- normalized axiom text and serialized term IR;
- verdict;
- language and target fingerprint;
- discovery seed and validation seed;
- valid, invalid-domain, exception, and failed sample counts;
- generator and observer IDs;
- limits: maximum term cost, timeout, and candidate caps;
- minimized counterexample for a refuted candidate;
- verifier name, version, scope, assumptions, and proof artifact digest for a proof;
- explicit `implementation`, `model`, or `finite-domain` proof scope.

This distinction matters: an SMT proof of a user-written model is not automatically a
proof of the Python or Java implementation.

## 7. Implementation phases

Each phase ends with a usable artifact and a gate. Do not begin broad UI work until
the Python and Java command-line paths pass the same conformance suite.

### Phase 0 — Preserve and classify the legacy repository

Tasks:

1. Decide whether `algebraicaxioms/` will be an archive, a Git submodule, or removed
   after the port. Do not leave it as an accidental embedded repository.
2. Establish its license and provenance before copying implementation code.
3. Tag or record the imported commit (`a22e1a0`) in an ADR.
4. Convert its intended examples into behavior tables:
   - stack;
   - Python list;
   - string/string-buffer;
   - exception and empty-container cases;
   - aliasing and side-effect cases.
5. Record known defects rather than repairing them in place.
6. Identify reusable algorithms, not reusable modules:
   typed tree construction, alias partitions, side-effect propagation, and structural
   pruning.

Deliverables:

- provenance/license decision;
- legacy behavior inventory;
- accepted and rejected legacy design decisions;
- no dependency from production DIG code to `algebraicaxioms/python/src`.

Gate: the team can remove the legacy directory without losing undocumented intended
behavior.

### Phase 1 — Write the semantic ADR and versioned schema

Tasks:

1. Finalize the semantics in section 3.
2. Specify type compatibility, including exact types versus subtyping.
3. Specify overload resolution for Java and decorated/wrapped functions in Python.
4. Specify observer completeness and what “state equality” claims.
5. Define the exception-domain policy.
6. Define bounds and defaults for term cost, variables per type, candidates, samples,
   worker time, and memory.
7. Define schema versioning and forward-compatibility behavior.
8. Define stable JSON encodings for terms, recipes, outcomes, evidence, and results.
9. Include an explicit threat model for executing analyzed APIs.

Deliverables:

- ADR;
- JSON Schema or equivalent validation model for manifest and result documents;
- golden serialized examples for stack laws.

Gate: Python and Java implementers can independently produce the same term and
outcome JSON from the specification.

### Phase 2 — Build the language-neutral core on Python 3.14

Tasks:

1. Add immutable `dataclass(frozen=True, slots=True)` models for types, operations,
   variables, calls, equations, effects, and outcomes.
2. Use explicit validation exceptions, never `assert`, for user input or runtime
   correctness.
3. Use package-relative imports; do not copy `vu_common.py` or the flat legacy import
   structure.
4. Implement canonical hashing and ordering independent of hash randomization.
5. Implement typed bottom-up term enumeration by cost.
6. Implement alias partitions and canonical variable renaming.
7. Reject ill-typed compositions before evaluation.
8. Canonicalize declared commutative calls.
9. Add deterministic caps and explain in results when a cap truncates search.
10. Unit-test enumeration counts, types, alias patterns, canonicalization, and stable
    serialization.

Modernization rules:

- use `typing.get_type_hints`, `inspect.signature`, `get_origin`, and `get_args`, not
  private `typing` attributes such as `__parameters__`;
- use `collections.abc` for runtime protocols;
- use `pathlib`, `tempfile`, and argument-list subprocess calls;
- never use `shell=True` for generated commands;
- keep generated artifacts inside a run-specific temporary directory;
- use structured logging through DIG's logger;
- make random-number generators explicit objects rather than shared global state;
- add complete type checking and lint coverage for the new package.

Deliverable: the core can enumerate language-neutral stack terms and equations
without importing a Python or Java target.

Gate: unit tests prove deterministic output across repeated processes with different
hash seeds.

### Phase 3 — Replace pairwise equation explosion with observational signatures

The legacy algorithm enumerates many equation pairs and tests them one by one. Use a
more scalable approach:

1. Generate a fixed discovery recipe set.
2. Evaluate every well-typed term independently on those recipes.
3. Build an observational signature from its sequence of outcomes.
4. Group terms with identical signatures.
5. Choose the smallest canonical representative in each group.
6. Emit equations from other group members to the representative.
7. Validate emitted equations on held-out recipes.

Retain direct candidate generation as a test oracle for very small grammars. Compare
both algorithms to ensure signature grouping does not lose expected laws.

Add controls for:

- maximum terms per type and cost;
- minimum valid samples;
- exception-heavy terms;
- duplicate semantic signatures;
- per-operation and per-term coverage;
- incremental search so cost `n + 1` reuses cost `n` results.

Gate: the stack benchmark finds the expected push/pop laws while evaluating
substantially fewer equation pairs than the legacy strategy.

### Phase 4 — Build the isolated Python backend

Tasks:

1. Start a worker using a configured Python interpreter; do not import the analyzed
   package into DIG's orchestrator process.
2. Communicate using a length-bounded, versioned JSON-lines protocol.
3. Resolve functions/classes only from manifest bindings.
4. Support constructors, functions, static/class methods, and instance methods.
5. Create initial worlds from deterministic recipes. Prefer rebuilding twice from a
   recipe over `deepcopy`; allow a tested custom clone adapter when rebuilding is not
   possible.
6. Preserve aliases within each world and isolate the left and right worlds.
7. Add built-in codecs for `None`, booleans, integers, finite floats, strings, bytes,
   lists, tuples, dictionaries with supported keys, and sets with canonical order.
8. Require adapters for arbitrary objects.
9. Capture return value, snapshots, normalized exceptions, worker crash, timeout, and
   bounded stdout/stderr.
10. Batch evaluations to avoid one process startup per term while enforcing a batch
    deadline.
11. Restart workers after crashes or configured batch counts to contain leaked state.
12. Detect target mutation that contradicts a `pure` declaration.

Tests:

- built-in list and string APIs;
- a custom stack class;
- static and class methods;
- inheritance and annotation overrides;
- alias-sensitive operations;
- exceptions, crashes, infinite loops, excessive output, and nondeterminism;
- objects that cannot be deep-copied;
- global-state contamination between cases.

Gate: Python stack/list examples produce replayable results on Python 3.14 without
writing outside the run directory.

### Phase 5 — Add discovery, validation, shrinking, and robustness checks

Tasks:

1. Split the root seed into independent deterministic streams for:
   - discovery;
   - held-out validation;
   - shrinking;
   - mutation testing.
2. Require held-out validation before `VALIDATED`.
3. Add boundary-biased built-in generators: empty, singleton, duplicates, negative,
   zero, minimum/maximum configured magnitude, and nested values.
4. Permit user generators to return a serializable construction recipe, not only a
   live object.
5. Implement type-aware counterexample shrinking:
   - integers toward zero and boundaries;
   - sequences by deletion and element shrinking;
   - object recipes through adapter-provided shrink moves;
   - alias graphs toward simpler partitions.
6. Store the smallest reproducible counterexample and a command to replay it.
7. Replay surviving laws under multiple seeds and report stability.
8. Seed known-invalid equations and mutations to measure the campaign's ability to
   reject them.
9. Report coverage metrics: operations exercised, term costs, valid-domain rate,
   exception rate, and generator cases used.
10. Add optional property-based generator integration behind the recipe interface;
    keep the core independent of a particular fuzzing library.

Gate: every intentionally false benchmark law is refuted with a stable minimized
counterexample, and no exception-only law survives vacuously.

### Phase 6 — Build the JVM/Java backend

The inference engine remains Python; Java execution happens in a long-lived JVM
worker.

Tasks:

1. Define supported target forms for the first release:
   - compiled classes plus explicit classpath;
   - JAR plus classpath;
   - optionally a source directory compiled with `javac` into the run directory.
2. Do not run Maven or Gradle automatically in the first release. Accept a build
   command only in trusted local mode later; web mode must use prebuilt or explicitly
   compiled, dependency-complete inputs with networking disabled.
3. Implement the same versioned protocol and conformance fixtures as the Python
   worker.
4. Resolve overloaded methods by full JVM-compatible parameter declaration, not only
   method name.
5. Support constructors, instance methods, and static methods.
6. Use deterministic recipe classes/factories to construct two equivalent worlds.
7. Preserve aliases in object graphs.
8. Add built-in support for primitives, boxed primitives, strings, arrays, lists,
   sets, maps, and enums.
9. Use deep array/collection comparison where appropriate; require snapshots or
   comparators for opaque domain classes.
10. Normalize Java exceptions by declared class and adapter-selected payload.
11. Enforce per-batch timeout from the parent and per-case cooperative deadlines in
    the worker where possible. Kill and replace a stuck JVM.
12. Bound heap, stack, output, and process count.
13. Fingerprint class files/JARs and include the digest in results.
14. Test on the project's selected minimum and primary JDK versions in CI.

Java conformance corpus:

- `java.util.Stack` push/pop/peek;
- `ArrayList` add/get/size and alias cases;
- strings and string builders;
- overloaded methods;
- primitive versus boxed values;
- arrays and deep equality;
- a custom mutable class with snapshots;
- throwing and nonterminating methods.

Gate: the same abstract stack specification produces semantically equivalent
normalized laws and counterexamples through Python and Java test targets.

### Phase 7 — Add verification as a plugin ladder

Create a verifier protocol:

```text
supports(spec, axiom) -> SupportReport
verify(spec, axiom, limits) -> VerificationResult
```

Implement in this order:

#### 7.1 Finite-domain exhaustive verifier

- If every root value, argument value, and construction depth is explicitly finite,
  enumerate the complete declared domain.
- Report `PROVED` only with scope `finite-domain` and include exact domain bounds.
- Detect state-space truncation; truncated enumeration is bounded validation, not
  proof.

#### 7.2 User-supplied SMT model verifier

- Allow operations and snapshots to have language-neutral logical models.
- Translate terms into Z3 expressions/state transitions.
- Prove the negation unsatisfiable or return a model as a counterexample recipe.
- Clearly report scope `model` unless implementation/model conformance is separately
  established.
- Support mutable state by explicit pre-state/post-state transitions, not by treating
  mutators as pure functions.

#### 7.3 Direct implementation-verifier research spikes

Run bounded, time-boxed evaluations before choosing dependencies:

- Python: assess symbolic execution for a restricted pure/scalar subset and document
  unsupported syntax and library calls.
- Java: assess bytecode-level bounded verification for a restricted subset and the
  feasibility of extracting replayable counterexamples.
- Compare installation cost, licensing, active maintenance, proof scope, loop and
  heap support, and deterministic automation.

Do not couple the core to a specific external verifier during the spike. Add a plugin
only if it can state a defensible proof scope and produce machine-readable results.

#### 7.4 Optional model-conformance checks

- Differentially test each logical operation model against its implementation.
- Where a direct verifier supports the operation, prove conformance separately.
- A model axiom plus sampled conformance remains a model proof with validation—not an
  implementation proof.

Gate: reports make it impossible to confuse randomized validation, bounded exhaustive
checking, model proof, and implementation proof.

### Phase 8 — Integrate the analysis into DIG

CLI plan:

1. First add an explicit, backwards-compatible mode:

   ```console
   python -O src/dig.py --axioms path/to/spec.toml
   ```

2. Retain the existing positional C/trace behavior unchanged.
3. Once stable, consider real subcommands while preserving old invocation:

   ```console
   dig invariants program.c
   dig axioms spec.toml
   dig replay result.json --counterexample ID
   ```

Add axiom options in a distinct argument group:

```text
--max-call-cost
--max-terms-per-type
--max-candidates
--discovery-tests
--validation-tests
--python-executable
--java
--classpath
--verifier
--worker-timeout
--replay-counterexample
--json-output
```

Integration tasks:

1. Add an analysis dispatcher instead of extending the existing `.c`/trace suffix
   branch repeatedly.
2. Introduce a common `RunResult` envelope with analysis kind, target, findings,
   evidence, timings, diagnostics, and artifacts.
3. Preserve `DInvs` internally for numerical analysis.
4. Add `AxiomFindings` for axiom analysis.
5. Generalize top-level verdict/report concepts without weakening current invariant
   checks.
6. Add stable JSON output; keep human-readable output as a renderer of structured
   results.
7. Make `--writeresults` use the common result renderer while retaining compatible
   numerical text output.
8. Integrate seed handling, temporary directories, multiprocessing policy, logging,
   timeout accounting, and cleanup.
9. Add `axiom` to documentation as an analysis kind, not as a numerical `--types`
   member. `--types` continues to select invariant families inside numerical
   analysis.
10. Include axiom timings and counts in the existing analysis summaries without
    pretending axioms belong to source locations.

Gate: all existing DIG regression tests pass unchanged, and axiom runs produce both
human and stable JSON reports through `dig.py`.

### Phase 9 — Docker, security, and web integration

Tasks:

1. Add the selected JDK runtime/compiler to the DIG image and pin/document its major
   version.
2. Run Python and Java targets as untrusted child processes with:
   - no network;
   - read-only target inputs;
   - a dedicated writable temporary directory;
   - CPU, wall-clock, memory, output, file-size, and process limits;
   - process-group termination on timeout/cancellation.
3. Never interpolate manifest values into a shell command.
4. Reject path traversal and classpaths outside allowed roots in web mode.
5. Decide whether custom generator/adapter code is permitted in hosted mode. The
   recommended first policy is “examples and administrator-installed adapters only.”
6. Extend the web runner with `tool = "axioms"` or a first-class analysis-kind field.
7. Accept a manifest plus a bounded set of source/class artifacts; do not overload the
   existing single C/CSV text field.
8. Render verdict, evidence counts, assumptions, and expandable counterexamples.
9. Consume JSON output rather than parsing console text.
10. Add cancellation and timeout integration tests for both worker types.

Gate: malicious timeout/output/path fixtures are contained, and a Python and Java
example can run through the same web job lifecycle.

### Phase 10 — Hardening, documentation, and release

Tasks:

1. Add an axiom benchmark/golden harness analogous to DIG's numerical golden tests.
2. Record expected must-find laws, must-refute laws, maximum term counts, and runtime
   ceilings.
3. Run determinism tests across processes and repeated seeds.
4. Add performance baselines for enumeration, worker throughput, and memory.
5. Add protocol compatibility tests between current and previous worker versions.
6. Add schema migration tests.
7. Document how to write generators, observers, snapshots, and comparators.
8. Document interpretation of every verdict and proof scope.
9. Document unsafe API categories and hosted-mode restrictions.
10. Publish Python and Java tutorials using equivalent stack examples.
11. Add troubleshooting for classpaths, virtual environments, serialization, and
    insufficient valid-domain samples.
12. Remove or archive the legacy directory only after feature-parity examples pass.

Release gate:

- Python and Java conformance suites pass;
- existing DIG tests do not regress;
- no surviving candidate is labeled proved without a proof artifact and scope;
- all counterexamples replay from the result document;
- deterministic runs have identical normalized outputs;
- security limit tests pass in Docker and direct execution modes.

## 8. Test strategy

### Unit tests

- schema and binding validation;
- type compatibility and overload resolution;
- term enumeration and cost bounds;
- alias partition generation;
- structural hashing and canonical variable renaming;
- outcome comparison;
- exception-domain handling;
- signature grouping;
- simplification and implication rules;
- evidence/verdict transitions;
- JSON round trips and schema versions.

### Cross-backend conformance tests

Create semantically matching Python and Java fixtures and feed both the same abstract
recipe sequences. Compare normalized outcomes rather than language-specific object
representations.

Required cases:

- pure identity and composition;
- mutable push/pop;
- void mutator plus observer;
- shared versus distinct arguments;
- both-sides exception;
- one-side exception;
- custom snapshot;
- nested containers;
- overloaded Java method;
- Python annotation override;
- nondeterministic operation detection.

### Metamorphic and mutation tests

- Randomly generate small operation grammars and compare optimized signature grouping
  with exhaustive pair testing.
- Mutate valid implementations or expected laws and require counterexamples.
- Shuffle declaration order and require identical normalized results.
- Vary `PYTHONHASHSEED` and JVM hash-sensitive collection insertion order.

### End-to-end golden tests

Each benchmark records:

- must-find normalized laws;
- must-not-report laws;
- expected verdict floor;
- minimum valid samples;
- maximum terms/candidates;
- runtime and memory envelope;
- expected counterexample for seeded false laws.

Avoid asserting only total counts: they do not establish semantic quality.

## 9. Legacy-to-new mapping

| Legacy concept | New disposition |
|---|---|
| `Term`, `Arg`, `Fun` tuple subclasses | Replace with typed immutable dataclasses |
| Python type objects embedded in terms | Replace with stable `TypeId` |
| `side_effect_idxs` | Replace with explicit effect declarations and observed roots |
| `gen_trees` | Port algorithmically as typed, cost-bounded bottom-up enumeration |
| `gen_args` integer patterns | Replace with canonical alias partitions |
| Python/Java source-string generation | Replace with versioned worker protocol and adapters |
| fixed `Test.py` / `Test.java` | Remove; use isolated run directories and workers |
| random input pass/fail | Replace with discovery/validation evidence and verdicts |
| structural `implies` pruning | Retain only after normalization tests establish soundness |
| `vu_common.py` | Do not port; use DIG helpers or standard library |
| Java prototype in `java/` | Treat as historical reference only |
| Python stub specification files | Migrate to versioned manifest plus optional adapters |

## 10. Main risks and mitigations

### Search explosion

Mitigate with type-directed construction, cost bounds, semantic signature grouping,
canonical aliasing, per-type caps, incremental enumeration, and clear truncation
diagnostics.

### Unsound equality for mutable objects

Require explicit observable state, fresh equivalent worlds, and post-state comparison.
Report which observers define equality.

### Vacuous laws caused by exceptions

Exclude both-exception samples by default, require minimum valid-domain coverage, and
report exception rates.

### Misleading “verification” claims

Use explicit verdicts and proof scopes. Preserve proof artifacts and assumptions.

### Generator bias

Use independent held-out streams, boundary cases, stability runs, mutation tests, and
coverage reporting.

### Python/Java semantic drift

Use one serialized IR, one outcome contract, and a shared cross-backend conformance
suite.

### Running untrusted APIs

Use process isolation and resource controls from the first backend milestone; do not
treat sandboxing as a web-only finishing task.

### Toolchain burden

Keep the Python core independent of Java build systems and optional theorem provers.
Use explicit classpaths first and verifier plugins later.

## 11. Recommended delivery slices

The following slices provide reviewable, useful increments:

1. **Specification slice:** ADR, schemas, stack fixtures, and legacy inventory.
2. **Core slice:** IR, typed enumeration, aliasing, serialization, exhaustive oracle.
3. **Python candidate slice:** isolated worker and empirical stack/list discovery.
4. **Validation slice:** held-out tests, shrinking, counterexample replay, verdicts.
5. **Scalability slice:** observational signatures, incremental search, benchmarks.
6. **Java slice:** JVM worker and conformance suite.
7. **DIG slice:** dispatcher, CLI, structured result, unchanged numerical regressions.
8. **Verification slice:** finite proof and SMT model proof.
9. **Security/web slice:** hardened Docker execution and UI.
10. **Proof research slice:** go/no-go decisions for direct Python and Java verifiers.

Do not combine the initial Python port, Java backend, DIG CLI refactor, and proof-tool
selection into one change. Each slice should leave the repository runnable and have a
clear semantic test gate.

## 12. Definition of success

The project is successful when a user can point DIG at a documented Python or Java
API specification and receive a deterministic report like:

```text
VALIDATED pop(push(stack_0, item_0)) == item_0
  discovery: 100/100 valid samples
  validation: 1000/1000 held-out valid samples
  mutated roots compared with: stack_snapshot
  proof: none

REFUTED peek(stack_0) == pop(stack_0)
  counterexample: stack_0 = [0, 1]
  return values: 1 == 1
  post-state mismatch: [0, 1] != [0]
```

and, where supported:

```text
PROVED pop(push(stack_0, item_0)) == item_0
  scope: finite-domain
  domain: stack length <= 4, items in {-1, 0, 1}
  cases checked: ...
  artifact digest: ...
```

The report must state exactly what was compared, what evidence was collected, and
what “proved” means. That assurance boundary is the central requirement for
broadening DIG from numerical state invariants to algebraic API specifications.

## 13. Planned Rust backend extension

Rust is a worthwhile third backend, but it is not part of the initial Python/Java
release gate. Design the common IR and worker protocol for Rust from the beginning,
run a feasibility spike after the Python backend, complete the required Java backend,
and then deliver Rust as a separately gated beta.

Recommended order:

1. language-neutral model and semantic ADR;
2. Python backend and validation pipeline;
3. bounded Rust feasibility spike before freezing the worker protocol;
4. Java backend and Python/Java conformance gate;
5. Rust execution backend beta;
6. Kani verification plugin;
7. Rust web support only after local sandboxing passes.

This sequencing avoids delaying the required languages while preventing early model
decisions that would make Rust ownership or generics impossible to represent.

### 13.1 Rust-specific semantic additions

Add an input passing mode to every operation parameter:

```text
OWNED
SHARED_BORROW       # &T
MUTABLE_BORROW      # &mut T
```

The term checker must enforce:

- a moved value cannot be used later in the same evaluation;
- simultaneous mutable aliases are never generated;
- a mutable borrow cannot coexist with a live shared borrow where Rust forbids it;
- shared aliases are generated only where legal;
- interior-mutability wrappers such as `RefCell<T>` are explicit semantic types, not
  loopholes in the alias checker;
- ownership-consuming operations rebuild each comparison world from the same recipe;
- `Clone` is never assumed unless declared and tested by the adapter.

The common outcome model must distinguish:

- `Result<T, E>` as an ordinary return value;
- `Option<T>` as an ordinary return value;
- a caught panic as exceptional behavior;
- process abort, timeout, compile error, sanitizer/verifier failure, and protocol
  failure as infrastructure or safety outcomes;
- an unsafe-code violation as a refutation/safety finding, never as an equivalent
  outcome.

Extend stable type IDs so a Rust type includes its concrete instantiation. Analyze
`Stack<i32>` and `Stack<String>` as separate types initially; do not claim a law for
all `T` from tests of one monomorphization.

### 13.2 Rust target and manifest model

Support Cargo library projects through explicit declarations:

```toml
schema_version = 1
language = "rust"

[target]
manifest_path = "./Cargo.toml"
package = "my_collections"
features = []

[[types]]
id = "stack_i32"
rust_type = "my_collections::Stack<i32>"
adapter = "dig_adapter::StackI32Adapter"

[[operations]]
id = "push"
binding = "my_collections::Stack::<i32>::push"
kind = "instance_method"
receiver_type = "stack_i32"
receiver_mode = "mutable_borrow"
parameter_types = ["i32"]
parameter_modes = ["owned"]
return_type = "unit"
mutates = ["receiver"]
```

Require explicit concrete bindings in the first release. Do not make Rust API
discovery depend on rustdoc JSON because that output is experimental. Use
`cargo metadata --format-version` for stable workspace/package discovery and keep
operation signatures authoritative in the DIG manifest.

Record in every run:

- Rust compiler and Cargo versions;
- target triple and compilation profile;
- package, crate, enabled features, and `Cargo.lock` digest;
- target source digest;
- generated harness digest;
- adapter digest;
- whether dependencies were resolved in locked/offline mode.

Primary tooling references:

- Cargo metadata and reproducible flags:
  <https://doc.rust-lang.org/cargo/commands/cargo-metadata.html>
- Rustdoc JSON stability:
  <https://doc.rust-lang.org/rustdoc/unstable-features.html?highlight=doc>
- Kani overview:
  <https://model-checking.github.io/kani/>
- Kani usage and concrete playback:
  <https://model-checking.github.io/kani/usage.html>
- Kani proof-harness attributes:
  <https://model-checking.github.io/kani/reference/attributes.html>
- Kani contracts:
  <https://model-checking.github.io/kani/crates/doc/kani/contracts/index.html>

### 13.3 Rust execution architecture

Rust cannot use the Java reflection approach. Generate and compile a harness crate:

```text
DIG orchestrator
      |
candidate terms + recipes
      |
generated harness crate
      |
cargo build --locked --offline
      |
compiled worker executable
      |
versioned outcome protocol
```

Implementation steps:

1. Add `RUST` to the language enum without enabling it in the CLI.
2. Add owned/shared/mutable parameter modes to the common operation IR.
3. Add Rust identifiers and concrete generic arguments to schema validation.
4. Use `cargo metadata --format-version 1` to locate the selected package and target.
5. Generate a temporary harness crate that depends on the target by local path.
6. Generate direct, statically typed wrapper functions for declared operations.
7. Compile one worker containing a batch of terms rather than compiling per equation.
8. Invoke Cargo with argument arrays and `--locked --offline`; never construct a shell
   command from manifest values.
9. Cache compiled harnesses by compiler, target, lockfile, feature, adapter, manifest,
   and generated-source digests.
10. Run the compiled worker under the same JSON-lines protocol and resource limits as
    other languages.
11. Reconstruct independent left and right worlds from deterministic recipes.
12. Preserve legal aliases within a world.
13. Capture panics at the case boundary when the panic strategy permits unwinding.
14. Detect an abort or worker disappearance at the parent process.
15. Restart workers after crashes and reject incomplete batches.

Do not automatically modify the user's Cargo project. Generated harnesses, target
artifacts, proof harnesses, and counterexample tests belong in DIG's temporary or
explicit artifact directory.

### 13.4 Rust adapters and supported values

Define a small adapter contract implemented in the generated harness or a user helper
crate. Conceptually it must provide:

```text
from_recipe(recipe) -> T
snapshot(&T) -> EncodedValue
compare_return(&R, &R) -> Comparison
shrink_recipe(recipe) -> recipes
```

The actual Rust traits may need associated types so implementations remain statically
typed and do not require unsafe type erasure.

First-release built-ins:

- booleans and integer primitives;
- finite floating-point values with an explicit NaN/signed-zero policy;
- `String` and `&str` where lifetime construction is controlled by the harness;
- tuples up to a documented arity;
- arrays and `Vec<T>`;
- `Option<T>` and `Result<T, E>`;
- `HashSet`, `BTreeSet`, `HashMap`, and `BTreeMap` with canonical snapshots;
- user enums with explicit recipe codecs.

Require custom adapters for opaque domain types, reference-counted graphs, interior
mutability, external resources, raw pointers, and unsafe invariants.

### 13.5 Rust feasibility spike

Time-box the spike and answer these questions with executable fixtures:

1. Can the common IR express owned, shared-borrowed, and mutably borrowed operations
   without language-specific term nodes?
2. Can generated wrappers compile representative generic and overloaded-via-trait
   APIs using explicit concrete bindings?
3. Can recipes reconstruct alias-sensitive object graphs without relying on `Clone`?
4. Can the worker recover structured results after ordinary panics?
5. Can compiled artifacts be cached safely and deterministically?
6. Can Cargo run fully offline against an already-resolved target?
7. Can Kani verify a generated pure law and a mutable stack law?
8. Can a Kani counterexample be converted into, or accompanied by, a replayable DIG
   recipe?
9. Which loops, heap structures, traits, unsafe code, and dependencies are not
   supported by the proposed verification path?
10. What is the compile-time and disk-cost envelope for 100, 1,000, and 10,000 terms?

Spike fixtures:

- pure arithmetic functions;
- `Vec<i32>` push/pop/last;
- a custom stack without `Clone`;
- owned builder-style methods;
- shared queries followed by mutation;
- `Option` and `Result` returns;
- a trait method with one explicit implementation;
- a panic and an aborting worker;
- an interior-mutability example that must require a custom adapter.

Go/no-go gate:

- proceed if the common IR remains language-neutral, worker failures are contained,
  and batched compile/run performance is usable;
- revise the protocol before Java stabilization if Rust exposes missing ownership or
  outcome concepts;
- defer Kani without deferring execution support if proof-counterexample translation
  is the only failed criterion.

### 13.6 Rust backend implementation phase

After the spike succeeds:

1. Promote the harness generator and adapter API from experimental to versioned.
2. Add `rust_worker.py` orchestration and the checked-in Rust support crate.
3. Add manifest validation and clear compiler diagnostics.
4. Add compile caching with bounded size and safe invalidation.
5. Add built-in recipes, snapshots, comparisons, and shrinkers.
6. Add operation and type coverage metrics.
7. Add target-feature and workspace-package selection.
8. Add deterministic result normalization for hash-based collections.
9. Add CLI routing for local Rust axiom runs.
10. Add JSON result and counterexample replay support.
11. Add Docker toolchain and resource-limit integration.
12. Document unsupported Rust constructs explicitly.

Rust execution beta gate:

- all Rust conformance fixtures pass on the pinned primary toolchain;
- repeated runs produce identical normalized results;
- false laws produce minimized, replayable recipes;
- legal borrow/ownership terms compile;
- illegal reuse and aliasing are rejected before compilation where possible;
- compiler errors are reported as diagnostics, not candidate failures;
- existing Python, Java, and numerical DIG tests remain unchanged.

### 13.7 Kani verification plugin

Generate a proof harness for one normalized candidate at a time, or a deliberately
small compatible group, so proof results and resource limits remain attributable.

Implementation steps:

1. Map supported recipes to `kani::any()` values or adapter-provided symbolic
   constructors.
2. Encode declared type invariants and operation preconditions as explicit
   assumptions.
3. Generate two equivalent initial worlds without assuming `Clone` unless justified.
4. Evaluate both sides and assert return plus observable post-state equivalence.
5. Set and record unwind bounds and solver/resource limits.
6. Require successful unwinding/completeness checks before an implementation proof.
7. Parse machine-readable proof results where available; otherwise use a strict,
   version-pinned adapter rather than loose console matching.
8. Request concrete playback for failures and translate the witness into a DIG recipe
   when possible.
9. Replay every reported verifier counterexample against the ordinary compiled worker.
10. Store proof output and generated harness digests as artifacts.

Verdict rules:

- `PROVED`, scope `rust-implementation/Kani`: property succeeds and all required
  completeness checks succeed under the recorded assumptions;
- `REFUTED`: Kani produces a counterexample that the ordinary worker replays;
- `UNKNOWN`: resource exhaustion, unsupported feature, incomplete unwinding, solver
  unknown, or non-replayable witness;
- `ERROR`: toolchain/protocol failure unrelated to the property.

Never turn a bounded or incomplete Kani run into `PROVED`. Treat assumptions as part
of the displayed theorem statement.

### 13.8 Rust tests

Unit tests:

- Rust type/binding parsing;
- concrete generic instantiation;
- ownership-aware term legality;
- Cargo metadata parsing;
- harness source generation;
- cache keys and invalidation;
- panic/abort classification;
- canonical snapshots for unordered collections.

End-to-end fixtures:

- `Vec<i32>`;
- `String`;
- stack and queue types;
- sets and maps;
- builder APIs that consume `self`;
- `Option` and `Result` APIs;
- trait-bound concrete implementations;
- custom snapshots and generators;
- panicking, hanging, memory-heavy, and unsafe targets.

Cross-language tests should compare normalized laws for semantically equivalent
Python, Java, and Rust stack implementations. They should not require identical
language-specific exception/panic behavior.

Security tests:

- malicious `build.rs`;
- attempted network dependency access;
- path dependencies outside permitted roots;
- excessive compiler output;
- fork/process spawning by build scripts or target code;
- disk and target-cache exhaustion;
- worker timeout and abort.

Hosted mode should initially reject custom build scripts and unresolved dependencies,
or run them only inside a stricter build sandbox. `--locked --offline` improves
reproducibility but does not make a Cargo build script safe.

### 13.9 Rust beta release gate

Rust support can leave beta when:

- the supported ownership and generic subset is documented and enforced;
- the pinned Rust/Cargo toolchain is reproducible in Docker and CI;
- Cargo builds have no network access;
- counterexamples replay from result JSON;
- compile caches cannot cross-contaminate targets;
- mutation and alias semantics match the language-neutral contract;
- Kani proof scope and assumptions are visible in human and JSON reports;
- no incomplete verification is labeled `PROVED`;
- Python, Java, Rust, and numerical regression suites pass together.

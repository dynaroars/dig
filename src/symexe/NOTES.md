# MiniSym research notes

## Current design

MiniSym deliberately separates source syntax, executable concrete semantics,
symbolic formula construction, and semantic proofs. Stores are total functions,
which makes extensional correctness proofs small; examples expose finite snapshots
for readable output. Path conditions are explicit syntax and are interpreted only
when stating correctness. The executor never asks an external solver for trust.

Assertions split into a normal path guarded by the asserted formula and a failure
path guarded by its negation. Concrete and symbolic failures both short-circuit a
sequence. The main theorem preserves both the result tag and failure-point store.

Loops use a recursive per-loop unrolling budget (eight by default). Nested loops
receive the current enclosing budget, so this is not a global bound on the sum of
all loop iterations. A path that needs another
iteration at zero fuel is tagged `fuelExhausted`; it is not misreported as normal
termination or assertion failure. `execFuel` and `symExecFuel` accept an explicit
budget, and the strong soundness theorem quantifies over every budget.
The CLI accepts `--fuel N` before the source path.

## Limitations

- Loops are bounded by explicit execution fuel and may return `fuelExhausted`;
  there are no procedures, heap, pointers, arrays, or bounded-machine arithmetic.
- The parser accepts a deliberately small C-like language, not ISO C. There is
  no symbolic simplifier, feasibility filter, or SMT-LIB printer.
- Symbolic execution explores infeasible paths, so its result can grow
  exponentially with conditionals.
- Variable stores are functions; callers provide a finite list of names to print.
- Soundness is proved, but no claim is made that a solver will find every feasible
  path or that generated paths are mutually exclusive after future optimizations.

The source frontend requires `else`, treats initialized `int` declarations as
assignment syntax, and has no C types, lexical scopes, overflow, side effects in
expressions, or undefined behavior. All variables denote total symbolic inputs and
all integers are mathematical integers. Parser correctness is not part of the
symbolic-execution theorem: that theorem applies to the AST produced by the parser.

## Promising extensions

- Define a proof-producing pruning interface: a path may be removed only with a
  Lean proof that its interpreted condition is false. `omega` already handles
  useful linear-integer contradictions.
- Add normalization or SSA and prove it once as a semantics-preserving pass; SSA
  should also make SMT output and store reasoning simpler.
- Translate `SymBool` to SMT-LIB while keeping solver answers outside the trusted
  core, ideally checking unsatisfiability certificates in Lean.
- Generalize the expression and state interpretation lemmas so later front ends
  (or an LLVM subset) can reuse the symbolic-execution proof skeleton.
- Study bounded integers, memory regions, aliasing, and pointer provenance before
  approaching C or LLVM memory semantics.
- Evaluate whether `omega` and `grind` can automate branch obligations and compare
  proof-producing Lean workflows with KLEE- and Rosette-style exploration.
- Factor reusable verified execution infrastructure into CSLib once interfaces
  stabilize.

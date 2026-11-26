# MiniSym walkthrough for Lean newcomers

MiniSym is both an executable symbolic executor and a machine-checked argument
that the executor covers every behavior of its concrete semantics. This guide
explains how the pieces fit together and suggests an order in which to read them.

## Where should I start?

Start with [`MiniSym/Syntax.lean`](MiniSym/Syntax.lean). It is short and defines
the three syntax trees—arithmetic expressions, Boolean expressions, and
statements—that every other module consumes.

Recommended reading order:

1. [`MiniSym/Syntax.lean`](MiniSym/Syntax.lean) — the MiniC vocabulary.
2. [`MiniSym/Concrete.lean`](MiniSym/Concrete.lean) — what MiniC programs mean on
   ordinary integer inputs.
3. [`MiniSym/Symbolic.lean`](MiniSym/Symbolic.lean) — symbolic terms, formulas,
   valuations, and symbolic states.
4. [`MiniSym/SymExec.lean`](MiniSym/SymExec.lean) — the actual symbolic executor.
5. [`MiniSym/Examples.lean`](MiniSym/Examples.lean) — runnable AST examples.
6. [`MiniSym/Soundness.lean`](MiniSym/Soundness.lean) — the correctness relation
   and formal proof.
7. [`MiniSym/Parser.lean`](MiniSym/Parser.lean) — the optional C-like frontend.
8. [`Main.lean`](Main.lean) — command-line I/O and result printing.

The parser is intentionally late in this order. It is convenient engineering,
but the central research content begins with the AST and does not trust parsing.

## A tiny amount of Lean syntax

You only need a few ideas to begin reading:

- `def name (x : T) : U := ...` defines a function from `T` to `U`.
- `inductive` defines a datatype by listing its constructors.
- `.var "x"` is shorthand for a constructor such as `Expr.var "x"` when Lean
  can infer the datatype.
- `structure` defines a record with named fields.
- `fun x => ...` is an anonymous function.
- `f : A → B` means that `f` maps values of type `A` to values of type `B`.
- `List α` is a list whose elements have type `α`.
- `Option`, `Except`, and result constructors make exceptional cases explicit.
- `Prop` is the type of propositions. `Bool` is executable data with values
  `true` and `false`. MiniSym evaluates formulas to `Bool` and proves properties
  about those computations in `Prop`.
- A theorem is a definition whose type is a proposition. The code after `:= by`
  constructs its proof.
- `{x : T}` is an implicit argument that Lean normally infers; `(x : T)` is an
  explicit argument supplied by callers.
- `@[simp]` marks a theorem for Lean's simplifier.

## Overall pipeline

```text
C-like .c text
      |
      | Parser.parseProgram       (convenience layer, not verified)
      v
MiniC Stmt AST
      |                                  |
      | execFuel                         | symExecFuel
      v                                  v
concrete ExecResult                List SymResult
normal / assertionFailure /        each with a symbolic store
fuelExhausted                      and path condition
      |                                  |
      +------------ soundness -----------+
                    under valuation ν
```

The verified theorem starts at `Stmt`. It does not claim that the C-like parser
implements ISO C.

## 1. Source syntax

`Expr`, `BoolExpr`, and `Stmt` are explicit trees. For example,

```lean
.assign "x" (.add (.var "input") (.int 1))
```

represents `x = input + 1`. A loop is represented by

```lean
.while (.lt (.var "x") (.int 3)) body
```

The language uses mathematical integers. It has no machine overflow, pointers,
heap, functions, or C undefined behavior.

## 2. Concrete execution

A concrete state is a total function:

```lean
State := String → Int
```

Calling `state "x"` retrieves `x`. Assignment creates a new function that
returns the new value for the assigned name and delegates every other name to
the old state.

`evalExpr` and `evalBool` recursively interpret syntax. `execFuel` executes a
statement and returns one of three explicit outcomes:

- `normal state` — execution completed normally;
- `assertionFailure state` — an assertion was false at this state;
- `fuelExhausted state` — a true loop guard required another iteration after the
  loop-unrolling budget reached zero.

Failures and exhaustion are terminal: a following statement is not executed.
The default wrapper `exec` uses fuel 8.

Fuel is a recursive per-loop unrolling budget, not a global counter of every
statement step. On a true loop guard with positive fuel, the body runs and the
next iteration receives one less fuel. Nested loops receive the current budget.

## 3. Symbolic data

A symbolic expression describes an integer in terms of named inputs. For
example, `input + 1` is data, not a Lean arithmetic proposition:

```lean
SymExpr.add (SymExpr.input "input") (SymExpr.int 1)
```

Similarly, `SymBool` is an explicit formula tree. Keeping formulas explicit is
what makes future pretty printing, simplification, SMT-LIB translation, or
certificate checking possible.

A valuation gives concrete meanings to input names:

```lean
Valuation := String → Int
```

`interpretExpr` and `interpretBool` evaluate symbolic syntax under a valuation.
A `SymState` contains:

- `store : String → SymExpr`, describing every program variable; and
- `pc : SymBool`, the path condition that must hold on this path.

Initially every variable `x` maps to the symbolic input named `x`, and the path
condition is true.

## 4. Symbolic execution

`symExecFuel fuel statement state` returns a list because one input state may
fork into many paths.

- Assignment updates the symbolic store.
- Sequence uses `flatMap`: run the second statement from every normal result of
  the first, while preserving terminal failures and exhaustion.
- An `if b` explores both `PC ∧ b` and `PC ∧ ¬b`.
- `assert(b)` emits a normal result under `PC ∧ b` and a potential failure under
  `PC ∧ ¬b`.
- A loop emits an exit path for the false guard. Its true path either executes
  another bounded iteration or becomes `fuelExhausted` at zero fuel.

The executor deliberately retains infeasible paths. A symbolic assertion failure
is therefore a *potential* violation until its path condition is proved
satisfiable.

## 5. What the proof says

The relation

```lean
Matches valuation concreteState symbolicState
```

requires two facts:

1. the valuation satisfies the symbolic path condition; and
2. every concrete variable equals the interpretation of its symbolic expression.

`ResultMatches` also requires result tags to agree. A concrete assertion failure
cannot be matched by a symbolic normal result, and fuel exhaustion cannot be
confused with either one.

The strongest theorem is:

```lean
theorem symExecFuel_sound (fuel : Nat) (statement : Stmt)
    {valuation : Valuation} {state : State} {symbolic : SymState}
    (h : Matches valuation state symbolic) :
    ∃ result,
      result ∈ symExecFuel fuel statement symbolic ∧
      ResultMatches valuation (execFuel fuel statement state) result
```

In plain English: choose any fuel, program, valuation, and pair of matching input
states. Run the concrete program. Among the symbolic results there is one with
the same outcome tag, a path condition satisfied by the same valuation, and a
store interpreting to the concrete result state.

This direction is essential: symbolic execution cannot lose a real concrete
behavior. The theorem does not say every generated path is feasible or that
every potential assertion failure is a real counterexample.

The proof first establishes expression correctness, assignment preservation,
and true/false branch lemmas. It then uses induction on fuel and statement
syntax. The sequence and loop cases compose induction hypotheses; the result-tag
relation rules out mismatched terminal outcomes.

## 6. Running the tool

Build everything:

```bash
lake build
```

Run a branch/assertion example with the default loop fuel:

```bash
lake exe minisym examples/demo.c
```

Run the loop example with bound 3 and display only `x`:

```bash
lake exe minisym --fuel 3 examples/loop.c x
```

Use the Lean API directly:

```lean
import MiniSym

open MiniSym

#eval snapshotResults ["x"]
  (symExecFuel 3 MiniSym.Examples.loopProgram initialSymState)
```

## 7. How to experiment safely

Good first exercises are:

1. Change constants in `Examples.lean` and inspect the printed path conditions.
2. Lower loop fuel and observe `fuelExhausted` paths.
3. Add a statement constructor only after identifying the corresponding concrete
   result, symbolic rule, and soundness proof case.
4. Add formula simplification as a separate pass and prove interpretation is
   preserved.
5. Add pruning only when an infeasibility proof justifies removing a path.

After every change, run `lake build`. Lean will report missing pattern-match and
proof cases, which is one of the main benefits of keeping the design explicit.

## Trust boundary and limitations

The Lean kernel checks the AST-level semantic proofs. The handwritten parser,
CLI formatting, and chosen input files are not verified. The current engine also
lacks automatic feasibility pruning, SMT integration, loops without a bound,
machine integers, memory, pointers, and procedures. See [`NOTES.md`](NOTES.md)
for the longer research roadmap and [`docs/minisym-tool-paper.pdf`](docs/minisym-tool-paper.pdf)
for a paper-style description.

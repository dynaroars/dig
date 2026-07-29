# DIG — Algorithms, Invariant Types, and Usage

This document describes what DIG infers (the **invariant types**), how it infers
them (the **algorithms**), the **modes** it runs in, and the **flags** that
select or tune each algorithm, invariant type, and optimization.

DIG is a hybrid invariant generator. It combines three engines:

- **Dynamic analysis** — mine candidate invariants from concrete execution
  traces (numeric variable values at observation points).
- **Symbolic execution** — build z3 path conditions ("symbolic states") for a
  small subset of C, used both to *check* candidates soundly and to *optimize*
  bounds.
- **Static / algebraic analysis** — solve a loop's transition relation directly
  (recurrences → closed forms → invariants), with no traces at all.

Observation points are marked in the source with `vtrace<N>(...)` calls (e.g.
`vtrace1(q, r, a, b, x, y)`); `mainQ(...)` is the entry function and
`vassume(...)` states preconditions. An invariant is reported *per location*.

---

## 1. Invariant types

| Type | Example | Module | Engine |
|---|---|---|---|
| **Equalities** (linear & nonlinear) | `q*y + r == x`, `x*y == z`, `a*y - b == 0` | `infer/eqt.py` | dynamic CEGIR (+ symbolic check) |
| **Recurrence equalities** (solvable loops) | `2*x == y**2 + y`, `x*z - x - y + 1 == 0` | `infer/recurrence.py` | **static** (closed form + k-induction) |
| **Invariant-ideal equalities** (bounded degree, opt-in) | same class as above | `infer/kapur.py` | **static** (Rodríguez-Carbonell & Kapur) |
| **Inequalities** (interval / octagonal / polynomial) | `-4 <= x`, `-x - y <= 10`, `x*y <= 50` | `infer/oct.py` | symbolic optimization |
| **Min/max-plus** (a form of disjunction) | `max(x, y) <= z + 2`, `min(q, r) - b <= 0` | `infer/mp.py` | symbolic optimization |
| **Congruences** | `x === 0 (mod 4)`, `x + y === 1 (mod 5)` | `infer/congruence.py` | dynamic (GCD / arithmetic progression) |
| **Nested array relations** | `A[i] == B[C[3*i + 2]]` | `infer/nested_array.py` | dynamic (trace-only) |
| **User terms** | infer relations over `2^x`, `log(n)`, `y^2` | `-uterms` | feeds eqt / ieq generation |
| **Disjunctions** | `(x - y = 0) ∨ (x - z = 0)` via `x² − xy − xz + yz = 0` | eqt + mp | nonlinear factoring / min-max |

Every reported invariant carries a status: **proved** (`p`, sound), **disproved**
(`d`, a counterexample was found — dropped), or **unknown** (`u`, the solver
timed out). In symbolic-states mode most equalities and all recurrence
equalities are proved; in pure-dynamic mode results are candidates supported by
traces but not proved.

---

## 2. Algorithms

### 2.1 Symbolic execution → symbolic states (`data/symex_c.py`)

A self-contained symbolic-execution engine for a subset of C (integer and real
arithmetic, `if`/`switch`, `while`/`for`/`do-while` with `break`/`continue`,
1-D arrays, by-value structs, function inlining, globals, `#define`/`#if`).
It explores paths up to a bounded unroll **depth** and returns, per `vtrace`
location, a set of z3 path conditions (`pc ∧ slocal`). These *symbolic states*
are DIG's sound oracle:

- **`check`** — decide `pc ⇒ candidate`; if not, the model is a concrete
  counterexample input that becomes a new trace (used by CEGIR below).
- **`maximize`** — compute the exact upper bound of a term over the states
  (an SMT-`Optimize` convex-hull computation), used for inequalities/min-max.

The engine also exposes **sound, unbounded** reasoning used by the recurrence
engine and available standalone (§5): `prove_inductive` (k-induction),
`houdini` (largest mutually inductive subset of candidates),
`prove_termination` (ranking function), and `check_inv` (bounded per-path).

Determinism: path feasibility uses a z3 **rlimit** (a work-unit budget,
`SOLVER_RLIMIT`), not a wall-clock timeout, so symbolic states are reproducible
regardless of machine load.

### 2.2 Equalities — dynamic CEGIR (`infer/eqt.py`)

Counterexample-guided (CEGIR) fitting of a polynomial template:

1. Build a degree-`d` template `Σ cᵢ·tᵢ` over the location's variables.
2. Instantiate it on concrete traces → a linear system in the unknown
   coefficients `cᵢ`; solve for its **null space** (`Miscs.solve_eqts`) to get
   candidate equalities.
3. **Refine**: check each candidate against the symbolic states. A
   counterexample becomes a new trace row; loop until no candidate is
   disproved (or no new rows are linearly independent).

Optimizations:
- **Auto-degree via finite differences** (`_estimate_degrees` in `alg.py`):
  a few sample executions estimate each location's polynomial degree, used as a
  *floor* so high-degree power sums (e.g. `ps6`) can stop below the budget
  ceiling while low-degree ones aren't over-searched.
- **Rank short-circuit**: skip a solve when no new linearly independent rows
  were added since the last iteration.
- **Gröbner reduction** of the final equalities (bounded by `GROEBNER_TIMEOUT`).

### 2.3 Recurrence equalities — static (`infer/recurrence.py`)

The **static counterpart to `eqt.py`**: instead of guessing a template and
fitting traces, it reads the loop's transition relation and *solves* for the
invariants. No program is run and no traces are collected; generation is
algebraic and verification is unbounded.

Pipeline, per loop:

1. **Extract the update map** — symbolically execute the loop body once from a
   fresh symbolic state and keep the *continue* path, giving each variable's
   per-iteration update (e.g. `x = y + x`, `y = y + 1`).
2. **Solve the recurrences** — translate z3 → sympy and use `rsolve` in
   dependency (topological) order to get closed forms in an iteration counter
   `n` (e.g. `x(n) = n(n+1)/2`).
3. **Eliminate the counter** — a lexicographic **Gröbner basis** of
   `{v − closed_form_v(n)}` projects out `n`, leaving polynomial equalities
   among the program variables.
   - **P-solvable extension** (geometric/exponential loops, e.g. `x = x*z`,
     `a = 2*a`): a closed form containing `base**(a·n+b)` is handled by
     introducing an auxiliary `T = base**n`, rewriting the exponential, adding
     the multiplicative relations among numeric bases, and eliminating both `n`
     and the `T`'s. The base may be a *program variable* (e.g. `geo1`'s `z`),
     so the resulting invariant is still polynomial (`x*z − x − y + 1 = 0`).
4. **Prove** — verify the whole candidate set **jointly** with `houdini`
   (k-induction). Joint proof is essential: invariants like `2x = c²+c` are
   *mutually* (not individually) inductive — proving them one at a time by
   1-induction spuriously rejects the interdependent ones. Survivors are marked
   PROVED and need no trace checking.

**Scope.** The *single-path* engine handles *solvable single-path loops* (the
classic P-solvable class): ps1–ps6, cohencu, sqrt1, hard, geo1–3, and the
geometric inner loop of cohendiv (`a*y − b = 0`). Loops with **branching**
bodies (piecewise recurrences, e.g. egcd/fermat/prodbin) or non-closed-form
updates (integer division/mod) are declined here and picked up either by the
multi-path extension below (§2.3.1) or by DIG's dynamic engine. This is the
intended hybrid: static-complete where the algebra permits, data-driven
otherwise. Runs only in symbolic-states mode, on C input.

#### 2.3.1 Multi-path (branching) loops — CRA-style extension (`-norecurrencemp` to disable)

The single-path engine needs the loop body to reduce to *one* straight-line
update map; a branching body (an `if` inside the loop) produces several and is
declined. The multi-path extension, in the spirit of **compositional recurrence
analysis** (Kincaid et al.), lifts that restriction:

1. **Enumerate the continue paths.** Symbolically execute one havoc'd iteration
   and keep every loop-back path, giving one update map per branch (paths with
   div/mod/`ite` that don't render to a polynomial are dropped).
2. **Generate per path.** Solve each branch's update as if that branch ran on
   every iteration (§2.3 solve + counter-elimination), yielding candidate
   equalities. Pool and de-duplicate them across branches.
3. **Filter jointly.** Keep the subset that is *actually* inductive over the
   **real** multi-path loop (all branches, real guards) with `houdini`
   (k-induction). Generation is a heuristic — it pretends each branch runs in
   isolation — but soundness comes entirely from this joint proof, so every
   reported equality is genuinely PROVED.

**When it works / when it doesn't.** It recovers the equalities that each branch
*independently preserves* — e.g. cohendiv's `q*y + r − x = 0` and fermat1's
`4·A + 4·r − u² + 2u + v² − 2v = 0` (both branching loops the single-path engine
declined). It does **not** recover invariants that only hold through the
*interplay* of branches (e.g. egcd's Bézout relations `p·s − q·r = 1`,
`a·q − b·p = y`): none of the per-branch candidates are jointly inductive, so
houdini rejects them all and the loop is left to the dynamic engine (which does
find them from traces). The extension is therefore *purely additive* — it only
runs on loops the single-path engine declines, and never removes coverage.
On by default; disable with `-norecurrencemp`.

#### 2.3.2 Invariant-ideal equalities — Rodríguez-Carbonell & Kapur (`infer/kapur.py`)

> *In memory of Deepak Kapur (1950–2026), whose work on ideals, Gröbner bases,
> and quantifier elimination for program reasoning underlies this engine.*

A second **static** equality engine, algorithmically distinct from the
recurrence method: instead of solving closed forms, it computes the loop's
**ideal of polynomial invariants up to a degree bound `d`** directly, following
E. Rodríguez-Carbonell and D. Kapur, *"Automatic generation of polynomial
invariants of bounded degree using abstract interpretation"* (Sci. Comput.
Program. 2007) and *"Generating all polynomial invariants in simple loops"*
(J. Symbolic Computation 2007).

A polynomial `p` of degree ≤ `d` is an invariant iff it vanishes on every
reachable state, i.e. on the orbit `s₀, τ(s₀), τ²(s₀), …` of the loop's
transition `τ`. Over the finite-dimensional space of monomials of degree ≤ `d`,
writing `p = Σ cₐ·mₐ`, the condition `p(sᵢ) = 0` is a polynomial identity in the
program's **parameters** (loop-invariant inputs), so each parameter-monomial
coefficient must vanish — a homogeneous linear system in the unknowns `cₐ`. Its
**null space** is the degree-≤`d` invariant vector space (a Macaulay/evaluation
view of the bounded-degree invariant ideal). Because the space is finite and the
orbit is kept symbolic in the parameters, finitely many orbit points pin it down
exactly, so the computation **terminates on all solvable loops — affine and
geometric alike** (unlike the naïve ideal fixpoint, which never stabilises on a
free-running counter). The result is returned as a **Gröbner basis** (the
canonical presentation of the invariant ideal) and every generator is then
confirmed by k-induction/houdini before being reported PROVED.

The degree bound is the price of unconditional termination: to capture a
degree-`k` invariant, use `--deg k` (the engine tries degrees 2..3 by default
when wired into DIG). This complements the recurrence engine, which gets the
exact degree for free but only on loops with polynomial closed forms.

Standalone:

```bash
python3 -m infer.kapur ../benchmark/c/nla/geo1.c --deg 2
python3 -m infer.kapur ../benchmark/c/nla/cohencu.c --deg 3
```

Opt-in inside DIG with `-dokapur` (off by default, since it overlaps the
recurrence engine on the solvable class).

### 2.4 Inequalities and min/max-plus — symbolic optimization (`infer/oct.py`, `infer/mp.py`, `infer/infer.py::_Opt`)

For a fixed family of candidate terms:

1. Enumerate terms — octagonal `±x ± y` (`IDEG=1`, `ITERMS=2`, `ICOEFS=1`),
   higher-degree polynomial terms (`IDEG>1`), or min/max-plus terms
   `max(y₁,…,yₖ)`/`min(...)` (capped at `MP_MAX_SUBSET` operands).
2. Discard terms whose bound is trivial/uninteresting via a first `check`.
3. **Maximize** each surviving term over the symbolic states (`iupper` cap) to
   get its exact upper bound → `term <= bound`. This is a convex-hull
   computation done with an SMT optimizer, so the bounds are proved.

Term **filtering** (`DO_FILTER`) removes terms over inputs only (their bounds
aren't program invariants) and other unlikely-interesting terms.

#### 2.4.1 SYMBA — simultaneous optimization (`-dosymba`; `SymStates.maximize_many`)

Step 3 above, by default, runs **one z3-`Optimize` solve per term**; with many
variables the term count grows quadratically (octagons) or exponentially
(min/max-plus), so this dominates symbolic-states-mode runtime. `-dosymba`
replaces it with **SYMBA** (Li, Albarghouthi, Gurfinkel & Chechik, POPL'14):
all terms at a location are maximized **together** against a single shared SMT
solver. Each satisfying model of the symbolic states supplies a value for
*every* objective at once, so one model typically raises many terms' lower
bounds; the search stops when no model can beat any current bound (an `unsat`
certificate that proves they are the exact maxima). Fewer, cheaper solver calls
for the **same** proved bounds.

It respects incremental depth exactly like the per-term path: the exact max is
computed at each unroll depth and a term whose bound keeps growing with depth
(an artifact of bounded unrolling, not a real invariant, e.g. cohendiv's `q`) is
dropped, so results are byte-identical to the default. Same accept/reject policy
too (non-integer optima and bounds beyond `iupper` are rejected). Off by default
(it overlaps the default optimizer, like `-dokapur`); intended for programs with
many variables where the per-term solves are the bottleneck. Integer-valued
terms only — on real/rational optima it defers to the reject path.

### 2.5 Congruences — dynamic (`infer/congruence.py`)

For each linear term over a location's variables, detect an arithmetic
progression in its trace values (`a === b (mod n)`) via GCD of successive
differences. Guarded by `CONGRUENCE_MIN_NVALS` distinct values to avoid a large
modulus overfit from too few points. Trace-based; runs in both modes.

### 2.6 Nested array relations — dynamic (`infer/nested_array.py`)

Infer relations like `A[i] = B[C[k·i + c]]` among array-valued traces by
searching for consistent index maps. Trace-only (enabled per location when the
location is array-typed).

### 2.7 LLM-assisted inference — propose-and-verify (`infer/llm_infer.py`, `-llm`)

An LLM proposes candidate invariants (the forms DIG's algebra is weakest at:
disjunctions, conditionals, nonlinear inequalities, closed forms) and DIG
**verifies** them soundly — the LLM is never trusted. Each round:

1. **Verify (bounded).** Every candidate is checked with `symstates.check`
   (`pc ⇒ inv` over the symbolic states). Passing candidates are recorded;
   failing ones yield a concrete counterexample state.
2. **Houdini pass** (`DO_LLM_HOUDINI`, on by default; `-nollmhoudini` to skip).
   The *union* of a loop's candidates is additionally run through `houdini`
   (k-induction) at that loop head. This is stronger than step 1 in two ways:
   the proof is **unbounded** (not just true on the bounded reachable states),
   and it proves **mutually inductive** sets — candidates that fail alone but
   hold given the others (the classic reason per-candidate 1-induction rejects
   interdependent invariants). Because houdini's bounded entry states can
   over-approve on *nested* loops, its survivors are **intersected** with step
   1: a candidate step 1 disproved (a real, reachable counterexample) is never
   resurrected. So the pass only ever *adds* soundly-proved invariants.
3. **Refine (CEGIR).** The counterexamples from step 1 are formatted as
   `candidate  # false when <state>` lines and fed back into the next prompt, so
   the model sees *why* each guess failed rather than just that it did.

**When the houdini pass helps / doesn't.** It matters when the true invariants
are *mutually* inductive (each needs the others) or only provable unboundedly —
step 1 alone would miss or under-report them. It adds nothing when candidates
are already independently checkable, and it is skipped for non-loop-head
locations. Requires `ANTHROPIC_API_KEY`; the verifier half (steps 1–2) is
LLM-free and reusable on its own.

### 2.8 Result post-processing

- **Sanitize / simplify** (`DO_SIMPLIFY`): test invariants against all collected
  traces, then remove weaker/implied invariants using the symbolic states
  (deduplicates, e.g., a recurrence equality and the identical dynamic one).
- **Multiprocessing** (`DO_MP`): inference tasks across locations/degrees run in
  parallel forked workers.
- **Incremental depth** (`DO_INCR_DEPTH`): symbolic-state `check`/`maximize`
  start at a shallow unroll depth and deepen only while results keep changing
  (`SE_DEPTH_NOCHANGES_MAX`), avoiding the cost of the full depth when a shallow
  one already settles.

---

## 3. Modes of operation

| Mode | How to trigger | What happens |
|---|---|---|
| **Symbolic states** (default) | `dig.py prog.c` | Build z3 symbolic states; eqts via CEGIR, ieqs/min-max via SMT optimization, recurrences statically. Results are largely **proved**. |
| **Pure dynamic** | `dig.py prog.c -noss` | Compile + run the instrumented program on `N_RAND_INPS` random inputs; mine traces only. No proofs; recurrence/symbolic checks are skipped. |
| **Trace file** | `dig.py traces.csv` | Read a semicolon-separated CSV of concrete values; run the trace-only miners (eqt null-space, oct/min-max bounds from data, congruences, arrays). No source, no proofs. |
| **LLM-assisted** | `dig.py prog.c -llm` | An LLM proposes invariants; DIG **verifies** them soundly with symbolic states + z3 (plus a k-induction houdini pass, §2.7) in a CEGIR loop (`-llm_rounds`, `-llm_no_traces`, `-nollmhoudini`). Requires `ANTHROPIC_API_KEY`. |

Safety: before compiling/running a C file (dynamic or `-noss` mode), a static
scan rejects programs calling dangerous functions (`system`, `fork`, `open`,
…); each run is killed after `C.RUN_TIMEOUT` seconds.

---

## 4. Usage and flags

Run from `src/`:

```bash
python3 -O dig.py <input> [flags]      # input: prog.c | traces.csv | results_dir
```

### 4.1 Selecting invariant types

Every type is **on by default**. Pick a subset with the single **`-types`**
selector (a comma-separated allowlist); everything not listed is turned off.

| Type name (for `-types`) | Invariant type |
|---|---|
| `eqt` | equalities (dynamic CEGIR **and** static recurrence) |
| `ieq` | inequalities (octagonal / polynomial) |
| `minmax` | min/max-plus |
| `congruence` | congruences |
| `array` | nested array relations |
| `recurrence` | static recurrence equalities (subset of `eqt`'s output) |

```bash
# only equalities and inequalities:
python3 -O dig.py ../benchmark/c/nla/cohendiv.c -types eqt,ieq -log 3

# only the static recurrence engine (proved equalities), nothing else:
python3 -O dig.py ../benchmark/c/nla/ps6.c -types recurrence

# everything (the default — no -types needed):
python3 -O dig.py ../benchmark/c/nla/cohendiv.c -log 3
```

The old per-type `-no…` flags (`-noeqts`, `-noieqs`, `-nominmaxplus`,
`-nocongruences`, `-noarrays`, `-norecurrence`) have been **removed** — `-types`
is the single way to select invariant types.

Two modifiers and the opt-in engines are separate from `-types`:

| Flag | Effect | Default |
|---|---|---|
| `-norecurrencemp` | disable the multi-path (branching-loop) recurrence extension (§2.3.1) | multi-path on |
| `-dokapur` | **enable** the RC-Kapur bounded-degree ideal engine | kapur **off** |
| `-dosymba` | **enable** SYMBA simultaneous optimization for ieqs/min-max (§2.4.1) | symba **off** |
| `-nollmhoudini` | (`-llm` only) disable the k-induction pass over LLM candidates (§2.7) | houdini on |

`-dokapur` and `-dosymba` are the opt-in engines. `-dokapur` overlaps the
recurrence engine on the solvable-loop class; `-dosymba` overlaps the default
per-term optimizer — both compute the same results a different way, so they are
enabled only when requested.

### 4.2 Selecting the mode

| Flag | Effect |
|---|---|
| `-noss` | pure dynamic analysis (no symbolic states, no proofs) |
| `-nrandinps N` | number of random inputs (dynamic mode only; default 100) |
| `-inpMaxV N` | max magnitude of random inputs (default 300) |
| `-llm` / `-llm_rounds N` / `-llm_no_traces` | LLM-propose + DIG-verify mode |
| `-test_tracefile F` | extra trace file to test candidates against |

### 4.3 Tuning the algorithms

**Equalities / recurrences**

| Flag | Effect | Default |
|---|---|---|
| `-maxdeg D` | max polynomial degree for equalities | auto (finite-difference estimate, capped by `MAX_TERM=200`) |
| `-maxterm N` | cap terms used for auto-degree | 200 |

The recurrence engine derives its own exact degree from the closed form, so it
is unaffected by `-maxdeg`; it produces the true-degree invariant even when
`-maxdeg` would cap the dynamic engine below it.

**Inequalities / min-max**

| Flag | Effect | Default |
|---|---|---|
| `-ideg D` | term degree (1 = linear/octagonal, 2 = quadratic, …) | 1 |
| `-iterms K` | operands per term (2 = octagonal `±x ± y`) | 2 |
| `-icoefs C` | coefficient range `[-C..C]` (1 = octagonal) | 1 |
| `-iupper V` | max upper-bound value searched | 50 |

**Symbolic execution**

| Flag | Effect | Default |
|---|---|---|
| `-se_maxdepth N` | loop-unroll depth for symbolic states | 8 |

(Incremental-depth checking/maximizing is always on; the old `-noincrdepth`
flag and its non-incremental code path have been removed.)

**User terms**

| Flag | Effect |
|---|---|
| `-uterms "y^2 ; xy+4"` | add user terms; DIG infers equalities/inequalities over them |

### 4.4 Optimizations and output control

Invariant simplification (weaker-invariant removal) and inequality-term
filtering are always on (`DO_SIMPLIFY`/`DO_FILTER` are constants in
`settings.py`; the old `-nosimplify`/`-nofilter` debug flags were removed).

| Flag | Effect | Default |
|---|---|---|
| `-nomp` | disable multiprocessing | MP on |
| `-dosolverstats` | collect z3 sat/unsat/timeout statistics | off |
| `-writevtraces F` | write collected traces to CSV `F` | — |
| `-writesstates F` | write symbolic states to JSON `F` and stop | — |
| `-readsstates F` | load symbolic states from JSON `F` (skip re-running symex) | — |
| `-writeresults F` | write the inferred invariants to file `F` | — |
| `-log N` | verbosity: 0 error, 1 warn, 2 info, 3 debug, 4 trace | 3 |
| `-seed S` | RNG seed (runs are pinned with `PYTHONHASHSEED=0` for reproducibility) | — |
| `-benchmark_times N` / `-benchmark_dir D` | run N times / over a directory of programs | — |

### 4.5 Advanced algorithms — examples and when to use them

Three optional engines/optimizations, each independently toggled. All are sound
(every reported invariant is still proved); they change *what gets covered* or
*how fast*, never correctness.

**Multi-path recurrence** (`-norecurrencemp` to disable; on by default, §2.3.1)

```bash
# branching loops the single-path engine declines now get PROVED equalities:
python3 -O dig.py ../benchmark/c/nla/cohendiv.c            # proves q*y + r - x == 0
python3 -O dig.py ../benchmark/c/nla/fermat1.c -types eqt  # 4A+4r-u^2+2u+v^2-2v == 0
# inspect just the recurrence engine on one loop:
python3 -m infer.recurrence ../benchmark/c/nla/fermat1.c --multipath
```
- **Useful for**: loops with an `if` in the body whose invariant each branch
  *independently* preserves (cohendiv, fermat1). Purely additive — it only runs
  where the single-path engine gives up, so leaving it on is free coverage.
- **Not useful for**: invariants that only hold through branch *interplay*
  (egcd's `p*s - q*r == 1`): no per-branch candidate is jointly inductive, so
  nothing survives and the dynamic engine handles it. Disable with
  `-norecurrencemp` only to reproduce single-path-only behavior.

**SYMBA simultaneous optimization** (`-dosymba`; off by default, §2.4.1)

```bash
# same octagonal/min-max bounds, computed with one shared solver per location:
python3 -O dig.py ../benchmark/c/nla/dijkstra.c -types ieq,minmax -dosymba
```
- **Useful for**: programs with **many variables**, where the default one-solve-
  per-term optimizer dominates runtime (term counts grow quadratically for
  octagons, exponentially for min/max-plus). Same proved bounds, fewer solver
  calls (≈20% faster wall-clock on dijkstra's ieqs+min-max).
- **Not useful for**: small programs (few terms — the shared-solver overhead
  isn't repaid) or **real/rational-valued** programs (SYMBA is integer-model
  based and defers non-integer optima to the reject path, matching the default
  but gaining nothing). Leave off unless the optimizer is your bottleneck.

**LLM houdini pass** (`-nollmhoudini` to disable; on by default in `-llm`, §2.7)

```bash
export ANTHROPIC_API_KEY=...
python3 -O dig.py ../benchmark/c/nla/cohendiv.c -llm            # verify + houdini
python3 -O dig.py ../benchmark/c/nla/cohendiv.c -llm -nollmhoudini   # bounded check only
```
- **Useful for**: proposals that are **mutually inductive** (each candidate needs
  the others, so the per-candidate bounded check under-reports) or that need an
  *unbounded* proof. It only ever adds soundly-proved invariants (survivors are
  intersected with the bounded check, so a disproved candidate is never
  resurrected — important on nested loops).
- **Not useful for**: candidates that are already independently checkable, and it
  does nothing at non-loop-head locations. No reason to disable except to
  measure its contribution.

---

## 5. Standalone verification & reasoning CLI (`data/symex_c.py`)

The symbolic-execution engine is usable on its own for sound checking and
reasoning — the same primitives the recurrence engine builds on:

```bash
python3 -m data.symex_c prog.c [--depth N] [options]
```

| Option | What it does |
|---|---|
| (none) | print the symbolic states (path conditions) per `vtrace` location |
| `--prove "q*y + r == x" [--k K --loop L]` | prove an invariant at a loop head by **k-induction** (unbounded) |
| `--houdini "E1" --houdini "E2" …` | keep the largest **mutually inductive** subset of candidate invariants |
| `--check-inv LOC "E"` | bounded per-path check of `E` at location `LOC` |
| `--terminates "R" [--assume "INV"]` | prove termination via ranking function `R` (supporting invariants verified first) |
| `--gen-tests` / `--gen-harness F` | one concrete input per explored path / a compilable C replay driver |
| `--check-overflow`, `--no-safety`, `--merge` | opt-in 32-bit overflow check / disable auto div-by-zero+bounds checks / merge if-else diamonds |

Example (prove the recurrence engine's output the same way DIG does internally):

```bash
python3 -m data.symex_c ../benchmark/c/nla/ps2.c --prove "2*x == y*y + y" --k 2
python3 -m data.symex_c ../benchmark/c/nla/geo1.c --prove "x*z - x - y + 1 == 0"
```

---

## 6. Quick reference — which flag for which algorithm

| I want… | Use |
|---|---|
| nonlinear equalities, degree ≤ 2, fast | `-maxdeg 2 -types eqt` |
| only **proved** equalities from solvable loops | `-types recurrence` |
| octagonal inequalities only | `-types ieq -ideg 1 -iterms 2 -icoefs 1` |
| quadratic inequalities | `-ideg 2` |
| interval bounds only | `-iterms 1` |
| dynamic analysis (no proofs, no source needed beyond running) | `-noss` |
| infer over custom terms (e.g. `2^x`) | `-uterms "..."` |
| reproducible timing/debugging | `-nomp -log 4 -seed 42` |
| everything except the recurrence engine | `-types eqt,ieq,minmax,congruence,array` |
| prove equalities for **branching** loops (on by default) | (nothing — `-norecurrencemp` disables it) |
| use the RC-Kapur ideal engine instead/also | `-dokapur` |
| faster ieq/min-max bounds on many-variable programs | `-dosymba` |
| LLM-assisted, with the k-induction pass (on by default) | `-llm` (add `-nollmhoudini` to skip the pass) |
| deeper loops in symbolic execution | `-se_maxdepth N` |
| verify a specific invariant soundly | `python3 -m data.symex_c prog.c --prove "..." [--k N]` |
| run the RC-Kapur engine standalone | `python3 -m infer.kapur prog.c --deg d` |
| run the multi-path recurrence engine standalone | `python3 -m infer.recurrence prog.c --multipath` |

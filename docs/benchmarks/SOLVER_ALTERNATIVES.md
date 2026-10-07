# Solver alternatives for DIG — research, 2026-10-07

## Recommendation

Add **cvc5 as an optional exact checking backend first**, retaining Z3 as the
default and symbolic expression implementation. Evaluate a full replacement
only after query replay and end-to-end results establish a benefit. Consider
Yices as a second arithmetic comparison. Use dReal for a separately designed
approximate real/transcendental extension, rather than the current exact
counterexample loop.

This recommendation is an inference from DIG's code and the primary sources
below. It is not a measured speed ranking. No alternate solver was installed,
no DIG benchmark was run, and no production backend or paper claim was changed.
The existing stopping policies are outside this proposal. Knuth remains deferred.

## What DIG actually needs

The current code uses Z3 for much more than satisfiability:

| Role | Code | Requirements |
| --- | --- | --- |
| Symbolic execution | `src/data/symex_c.py` | Typed expression DAGs; integers/reals, booleans, arrays, ITE; substitution, rewriting, model evaluation, feasibility checks |
| Equality CEGIR | `src/infer/eqt.py`, `src/data/symstates.py` | Exact SAT/UNSAT/unknown; counterexample values for both observed variables and X_* entry inputs |
| Bounds | `src/data/symstates.py:_solve_max` | Incremental SAT checks and exact integer model values |
| Redundancy removal | `src/infer/inv.py`, `src/helpers/z3utils.py` | Implication checks; retain results when inconclusive |
| Recurrence/Kapur and symbolic proof | `src/infer/recurrence.py`, `src/infer/kapur.py`, `CSymEx.prove_inductive` | Base/step obligations; jointly inductive candidates; exact result handling |
| Serialization | `src/helpers/z3utils.py`, `SymStates.vwrite/vread` | SMT-LIB expression export/import and sort preservation |
| Other modes | `src/llm_infer.py`, `src/axioms/verify/smt_model.py` | Additional direct Z3 expression and solver usage |

An AST scan counted 487 `z3.<attribute>` references across 13 source files.
These include 133 ExprRef type annotations: this is a coupling measure, not
487 independent solver calls. `pyproject.toml` pins z3-solver 4.16.0.0.

The dominant numerical requirements include nonlinear mathematical integer
arithmetic, quotient/remainder, and mixed integer/real arithmetic. Switching
to machine bit-vectors or treating every integer as a real would change the
analysis. Symbolic loop unrolling does not bound the input integers.

Importantly, numerical bound inference now uses certified SAT search rather
than requiring a solver-native Optimize interface. SYMBA also uses shared SAT
queries. Optimization API compatibility is therefore not the primary obstacle
to a cvc5 numerical backend. Some legacy helpers still expose Optimize.

SymPy handles equality fitting and Groebner reduction separately. Replacing
Z3 would not repair floating-point matrix pruning, overflow-prone traces,
sampling gaps, template selection, or expensive SymPy operations.

## cvc5: best first alternative

cvc5 provides exact integer/real SMT solving, models, arrays, and incremental
solving. Its published nonlinear strategy combines incremental linearization
with algebraic methods; integer reasoning also uses incomplete reductions to
bit-vectors. Different algorithms make complementary results plausible, but
do not establish superiority on DIG. [cvc5 system paper](https://cvc5.github.io/papers/2022/BarbosaBBKLMMMN-TACAS22.pdf),
[current Python quickstart](https://cvc5.github.io/docs/latest/api/python/base/quickstart.html),
[current options](https://cvc5.github.io/docs/latest/options.html).

Its Pythonic API resembles Z3Py but is not fully compatible. The documented
gaps include SMT2 parsing in that wrapper. DIG also uses low-level Z3 AST
serialization, Z3 operation identifiers, and `simplify(..., som=True)`; cvc5's
documented Pythonic simplify takes a single expression argument. An import
alias is therefore not a credible migration plan. The base API has an input
parser, so the wrapper's parsing gap does not prevent SMT-LIB replay.
[Pythonic compatibility](https://cvc5.github.io/docs/latest/api/python/pythonic/pythonic.html),
[Pythonic utilities](https://cvc5.github.io/docs/latest/api/python/pythonic/solver.html),
[base input parser](https://cvc5.github.io/docs/latest/api/python/base/inputparser.html).

Use its own resource policies. cvc5 distinguishes per-query `rlimit-per` and
`tlimit-per` from lifetime resource limits. API `tlimit` does not enforce a
whole-process timeout, and per-query limits can overshoot before a safe return.
Its resource units are not interchangeable with Z3's; copying 15,000,000 into
both would not provide a fair budget comparison. Preserve process supervision.
[Resource limits](https://cvc5.github.io/docs/latest/resource-limits.html).

Nonlinear integer arithmetic remains incomplete. cvc5 can return unknown, and
switching solvers cannot guarantee termination or remove the need for budgets.
The published Yices NIA work also identifies undecidability of the general
problem. [NIA/MCSAT research](https://yices.csl.sri.com/papers/vmcai2017.pdf).

**Expected practical value:** independent verification, alternative
counterexamples, and recovery of some currently inconclusive queries. Whether
it improves latency, result coverage, or repeatability needs measurement.

## dReal: different evidence contract

dReal targets nonlinear real constraints, including transcendental functions.
Its standard answers are exact `unsat` and `delta-sat` for a numerically
relaxed formula. Thus delta-sat is not an exact SAT certificate. The Python
examples return interval boxes rather than exact counterexample assignments.
[dReal semantics](https://dreal.github.io/),
[dReal4 project and Python binding](https://github.com/dreal/dreal4).

It would be incorrect to say dReal has no integer support: its documented
variable types include INTEGER and its implementation includes integer
interval contraction. This does not make its evidence contract equivalent to
Z3/cvc5 or demonstrate compatibility with DIG's div/mod and array workloads.
[Variable types](https://dreal.github.io/dreal4/classdreal_1_1drake_1_1symbolic_1_1_variable.html),
[integer contractor](https://dreal.github.io/dreal4/namespacedreal.html).

DIG currently refines polynomial fits using exact violating states. A point
chosen from a delta-sat box might not satisfy the original path or violate
the exact candidate. It must not be fed into fitting as a certified row.
Concrete replay can validate entry-input proposals; an exact checker is needed
for exact symbolic witnesses when replay cannot establish them.

An unsat answer to a faithfully translated counterexample query can establish
the corresponding claim. But delta-sat should remain approximate/inconclusive
unless independently validated. Arbitrary bounds introduced to make interval
search practical restrict the claim, and constant rounding/translation must
not strengthen the original query accidentally. These are adapter obligations.

For exact equalities, near-violations and numerical weakening can make
delta-sat unhelpful even when the equality is valid. Decreasing delta adds
another tuning parameter and does not itself convert a relaxed witness into
an exact one. Do not assume finite numerical precision settles every exact
polynomial obligation.

**Useful future role:** real-valued models involving sin, cos, exp, or physical
tolerances, with explicitly approximate invariant/evidence semantics. That
would be a product extension requiring a different result contract.

## Other candidates

| Candidate | Research finding | DIG assessment |
| --- | --- | --- |
| Yices 2 | Nonlinear arithmetic uses MCSAT; integer MCSAT is documented in published work. Its contexts support multiple modes, and the project reports push/pop support for MCSAT. | Worth including in arithmetic query replay; verify mixed theories and div/mod capabilities on actual queries. |
| SMT-RAT | Focuses on nonlinear real arithmetic; lists NIA/NIRA methods too. Some methods are not adapted to incremental SMT-LIB. | Useful specialist comparison for polynomial obligations; less attractive as the first full backend. |
| Bitwuzla | Focuses on fixed-size bit-vectors, floating-point, arrays and uninterpreted functions. | Suitable for a future machine-arithmetic backend; does not directly replace mathematical Int/Real reasoning. |
| pySMT | Supports multiple solver APIs including Z3, cvc5 and Yices. | An abstraction library, not a competing solver. Evaluate operator coverage before making it DIG's universal expression representation. |

Sources: [Yices contexts](https://yices.csl.sri.com/doc/context-operations.html),
[Yices MCSAT](https://yices.csl.sri.com/doc/mcsat-support.html),
[Yices release notes](https://yices.csl.sri.com/release-notes.html),
[SMT-RAT project](https://github.com/ths-rwth/smtrat),
[Bitwuzla](https://bitwuzla.github.io/),
[pySMT integration](https://pysmt.readthedocs.io/en/latest/getting_started.html).

MathSAT supports incremental solving, models, linear arithmetic, bit-vectors,
and arrays, but the overview alone does not establish that it is a better
fit for DIG's nonlinear integer workload. It is not on the first experimental
shortlist. [MathSAT overview](https://mathsat.fbk.eu/).

## Migration choices

**A. Change the checking engine while retaining Z3 expressions.** Export
normalized obligations in SMT-LIB and solve with cvc5. Start with standalone
query replay; later add an incremental session or cached direct AST translator
for hot paths. This preserves Z3 expression simplification and minimizes
invasive changes. It remains a Z3 dependency, so it is an alternative checking
backend, not a complete removal of Z3.

**B. Add a solver-neutral typed expression layer.** Move symbolic execution,
rewriting, serialization, and model conversion behind it. Adapt Z3 and cvc5
to the same interface. This is the route to complete replacement, but the
surface includes the entire symbolic executor and several inference modes.
Only do this once the benefit or independence requirement justifies the work.

**C. Use an exact solver fallback.** Query cvc5 after Z3 unknown within a
shared total budget. Start deterministic and sequential so reproduction and
budget accounting remain clear. A future solver race would need explicit
resource allocation and cleanup; it is unnecessary for the first evaluation.
Separate DIG benchmark invocations must always remain serialized.

For all approaches, normalize result semantics: exact SAT plus model, exact
UNSAT, unknown plus reason, and separate approximate evidence. Maintain X_*
input namespace/model completion, never silently round rational or algebraic
values into integer counterexamples, and preserve bounded versus inductive
proof provenance. Neither engine makes a bounded check an unbounded proof.

Preserve C quotient/remainder modeling. SMT-LIB Int div/mod use Euclidean
division; DIG explicitly adjusts these for C truncation toward zero. Retain
those adjustments, negative-operand behavior, and division-by-zero handling.
Constant integer powers should be translated portably rather than assuming
identical pretty-printed power operators across solvers.
[SMT-LIB integer semantics](https://smt-lib.org/theories-Ints.shtml).

## How to decide empirically

1. Build a query corpus from path feasibility, equality counterexamples,
   optional bounds, redundancy checks, and induction obligations. Label
   program/location/seed, sorts/operators, phase, preprocessing, solver version,
   limits, outcome and model requirements. Start with existing outputs where
   sufficient; instrument a serialized representative run when actual
   obligations are needed. Saved final invariants alone are not a query corpus.
2. Replay identical formulas through Z3 and cvc5, then Yices if useful. Compare
   fresh and incremental sessions separately. Use matched elapsed-time limits
   for comparisons and retain each solver's independently calibrated work
   policy. Count solved outcomes, tail latency, parse/translation overhead,
   model validity, and unknown reasons.
3. Include EGCD2/3, Prod4br/Prodbin, quotient/remainder programs, Freire real
   arithmetic, high-degree power sums, and congruence simplification. Keep
   ordinary easy cases to measure overhead. Keep Knuth out of the first pass.
4. Test semantics before performance: negative div/mod, mixed casts, exact
   large coefficients, constant powers, arrays/ITE, unused inputs and model
   completion, scope push/pop, interruption and unknown. Check disagreements
   explicitly rather than voting between solvers.
5. Run end-to-end CEGIR comparisons. Different valid models can produce
   different fitting trajectories and polynomial bases; faster isolated
   queries do not guarantee faster complete inference. Compare semantic
   target recovery and retain interesting high-degree equations.
6. Validate any proposed default over the 91 required recovery entries at
   seeds 0..6, keeping outer benchmark concurrency one and internal
   multiprocessing enabled. Preserve the original golden/recovery artifacts.

Adopt cvc5 as default only if end-to-end evidence supports it. Retain a
fallback if it improves hard-query coverage within the same total budget.
Do not expose the solver's long expert-option list as new ordinary DIG knobs:
solver replacement should not undo the parameter-reduction objective.

# DIG parameter analysis — 2026-10-07

Scope: the current numerical C/trace inference pipeline, its CLI, web runner,
and TSE recovery fixture. This is a code review with small direct-function
probes, not a benchmark ablation. No inference behavior or paper claims were
changed. The user considers the current stopping rules acceptable: degree
early stopping and depth stabilization are therefore **outside the proposed
reductions**. API axiom analysis has a separate manifest and search space;
its limits should not be folded into numerical DIG settings.

## Assessment

Yes, the settings can be reduced, but fewer flags alone will not make DIG
more robust. Distinguish intent (invariant families, degree ceiling, analysis
mode), search heuristics (input range, template shapes, sample sizing), and
resource safeguards (solver work, process time, simplification time).
Automate the second category, centralize the third, and preserve the first.

The recovery fixture is less heterogeneous than it initially looks. Of the
91 required entries, excluding deferred Knuth:

| Setting | Recorded configuration |
| --- | --- |
| Symbolic depth | 89 use 4; EGCD3 uses 6; H34 uses 12 |
| Equality degree | 37 use 1, 39 use 2, 11 use 3, two use 4, one uses 5, one uses 6 |
| Input maximum | H24 and H34 use 30; the other 89 use the default 300 |
| Inequality term count | Sqrt1 uses 3; the other 90 use the default 2 |
| Inequality degree/coefficient range | No fixture overrides |
| Invariant families | Recovery excludes congruences globally |

All 91 entries specify degree explicitly. This establishes recovery with the
recorded configuration, not recovery with automatic defaults. The code does
not establish that each override is necessary; that requires controlled
comparisons. The existing seven-seed results and golden baseline should be
preserved during such comparisons.

## Settings worth reducing

### Input sampling: strongest first candidate

`src/data/prog.py:Prog._get_inp_ranges` combines `INP_MAX_V=300`,
`INP_RANGE_V=4`, four fixed percentage ranges for small input signatures, and
two ranges for larger signatures. `_get_valid_inp_ranges` tries one random
point in each Cartesian range combination. A combination is cached as valid
only if that point yields traces. `gen_rand_inps` then samples the cached
combinations.

Consequences:

- A failed sample can discard a range containing many valid inputs. The
  decision mixes precondition failure, overflow rejection, timeout, and
  observation reachability into one empty-trace result.
- Random sampling has no negative-value support. Symbolic counterexample
  replay can still supply negative inputs, so this is a sampling limitation,
  not a universal restriction on the analysis.
- Input magnitude influences termination, native overflow, number of trace
  rows, and numerical conditioning in polynomial fitting simultaneously.
- Range enumeration grows as 4^n for n<=4 and 2^n above that. More inputs
  change both sampling coverage and sampling cost discontinuously.
- Small legal CLI values can create empty ranges. Direct probes found
  `(0,0)` ranges at input maxima 1 and 10; `random.randrange` cannot sample
  them. The CLI accepts these positive values.

Recommendation: replace the public magnitude knob with a default sampling
policy that starts from zero, signed small values, source constants, and
symbolic reachability inputs; then broadens scales within a resource budget.
Do not permanently reject a whole range after one failed point. Keep an
explicit input-domain override for users who actually want to restrict the
domain, and an expert magnitude override for reproducing old runs. A sampler
is not a proof-domain restriction; make that distinction explicit.

Minimum prerequisite: eliminate empty ranges and record why executions
contribute no samples. Keep overflow rejection rather than fitting wrapped
values. The current `C.RUN_TIMEOUT=2` remains a process safeguard; it should
not silently become evidence that a range is infeasible.

### Inequality templates: consolidate the controls

`src/infer/oct.py:Infer.my_get_terms` uses `IDEG`, `ITERMS`, and `ICOEFS` to
construct a combinatorial candidate set. Nonlinear monomials are generated
first when IDEG>1, then combined using the same term/coefficient controls.
`UTERMS` adds positive/negative user expressions and combinations with each
observed variable. It is not simply a list of exact expressions to check.

Direct generation for eight variables produced:

| ITERMS | ICOEFS | Candidate count |
| --- | --- | --- |
| 2 | 1 | 128 |
| 3 | 1 | 576 |
| 2 | 2 | 480 |

These are counts before domain filtering, checking, and simplification, not
runtime measurements. Increasing IDEG compounds this growth.

Recommendation: keep the default octagonal family, then schedule more costly
templates from program expressions, assertions, and promising trace relations.
Sqrt1's three-term override is useful evidence that restricting all programs
to octagons loses useful relations. Do not remove it without replacement.
Prefer a named extended template family or a candidate-work budget to three
independent public integer controls. Preserve explicit expert overrides.

`ICOEFS` and `ITERMS` also control congruence generation in
`src/infer/congruence.py`, while `IDEG` does not: congruences independently
add quadratic monomials. Consequently, changing an inequality control also
changes another invariant family's workload. Separate domain policies
internally, even if the public interface becomes smaller.

`MP_MAX_SUBSET=2` separately caps the operands in min/max terms. Keep a
bounded default because unrestricted subsets grow exponentially. Generate
larger subsets preferentially from source min/max expressions rather than
exposing another ordinary tuning integer.

### Constant-bound caps: replace arbitrary magnitude with bounded work

Octagonal bounds use `IUPPER=50`; min/max bounds use `IUPPER_MMP=1`.
`src/infer/infer.py:_Opt._gen` first checks candidate inequalities against
these caps. `src/data/symstates.py:SymStates._solve_max` then certifies an
integer maximum by SAT search within the cap. Dynamic inference and later
bound weakening also apply caps.

A direct solver probe with `x==100` returned no maximum under cap 50 and
returned 100 under cap 100. The solver handled both queries easily. This is
a deliberate coverage restriction, not necessarily a difficult solver case.

Recommendation: seed search from observed bounds/source constants and expand
the interval geometrically under a work budget, certifying every accepted
bound. This removes the need for users to guess a numeric constant ceiling.
Do not interpret exhaustion or unknown as a bound. This changes magnitude
search, not the existing depth stabilization rules.

Bounds over real-valued expressions are currently accepted only when an
integer bound is certified. Removing caps would not fix that separate
expressiveness limitation.

### Trace fitting and numerical thresholds: fix before automating

`EQT_RATE=1.5` requests a multiple of the number of monomials;
`TRACE_MULTIPLIER=5` controls an oversampled subset from which relatively
sparse rows are selected (`src/data/traces.py:Traces.instantiate`). There are
also hard-coded diversity sizes in equality refinement. These quantities
address matrix conditioning and fit quality, but row count does not establish
linear independence.

More significant issues occur in `src/helpers/miscs.py`:

- `coef_matrix_rank` casts coefficients through `int` before floating-point
  rank. For rows `[1,1/2]` and `[1,1/3]`, the probe returned rank 1 while exact
  rational rank is 2.
- `_null_space_fast` prunes columns whose numerical null-space support is
  <=1e-7. For rows `[1,10^9]` and `[2,2*10^9]`, it returned no null vectors,
  while the exact matrix has a one-dimensional null space. The exact relation
  needs a coefficient that becomes small after numerical normalization.
- The subsequent exact solve certifies returned vectors, but does not certify
  that numerically discarded columns cannot participate in a relation. The
  code comment describing those columns as provably uninvolved is stronger
  than the implementation justifies.

This is a concrete mechanism by which input magnitude and polynomial degree
can affect discovery beyond runtime. The probes demonstrate local failures;
they do not establish that a particular saved benchmark lost a target this way.

Recommendation: use numerical results as hints, require exact evidence before
discarding columns or declaring no relation, and select independent fitting
rows using exact or modular arithmetic with certification. Then sample sizing
can be an internal policy rather than another multiplier users must tune.
Keep the user's accepted outer stopping policies; correct the rank information
fed to them.

`TRACE_MAX_VAL=10^9` is another removable heuristic.
`src/infer/inv.py:Inv.test_single_trace` returns True without evaluating a
trace if any observed value exceeds it. A direct probe incorrectly accepted
`x==0` on `x=1000000001`. This concerns base-class trace validation; it does
not establish that the final emitted benchmark results are false. Equality
refinement separately evaluates collected traces, and some invariant classes
override trace evaluation.

Recommendation: remove silent magnitude-based acceptance and use exact
evaluation of valid traces. If arithmetic semantics are uncertain, record
that explicitly rather than counting the trace as supporting the candidate.
Keep signed-overflow trapping and rejection as a distinct safeguard.

`UGLY_FACTOR=20` still filters coefficients/term counts through
`Miscs.refine` by default, including the trace-only equality path. The symbolic
CEGIR path now explicitly disables this filter. This inconsistency can discard
interesting high-degree/large-coefficient candidates in one mode but preserve
them in another. Replace deletion with ranking/presentation, preserving the
candidate catalog as the user requested.

### Resource limits: centralize, but retain distinct task policies

The numerical pipeline has separate work/time policies:

| Task | Current work/time controls |
| --- | --- |
| General checking | 15,000,000 Z3 work units; 5 s fallback |
| Optional bound inference | 500,000 units; 1 s fallback |
| Redundancy simplification | 100,000 units; 1 s fallback |
| Path feasibility | 100,000 units; 100 ms fallback |
| Groebner reduction | 5 s, original basis retained on timeout |
| Concrete execution | 2 s per input execution |
| Symbolic path/recursion safety | 5,000 active states; 50,000 concrete steps; inline depth 8 |
| Outer runner | legacy benchmark 900 s; recovery 600 s; web defaults to 60 s and caps at 300 s |

A plain numerical CLI invocation does not enforce
`BENCHMARK_TIMEOUT` on the whole analysis; that constant belongs to the
legacy benchmark runner. The web and recovery limits are different contracts.
EGCD3's validated median is about 148 s, so it exceeds the web default even
with the successful recovery settings.

Recommendation: one user-facing analysis resource budget, with internally
separate policies for feasibility, discovery, optional bounds, and cosmetic
simplification. Record effective policies and exhaustion reasons. Keep
per-execution and wall-clock safeguards: Z3 work units cannot bound native
execution or SymPy reduction. A deadline also cannot preempt every operation
unless enforced through cancellable workers/process supervision.

Do not simply assign the same limit to every phase. That would let optional
min/max or simplification consume the time needed to retain equality results.
Centralize policy and ownership rather than pretending all costs are equal.

`SymStatesMakerC.get_symstates` currently returns only the engine's records;
it does not propagate `CSymEx._incomplete` to the numerical result. Recording
truncation is useful even while retaining the existing limits and stopping
rules. Bounded checks and unbounded recurrence induction currently share the
`PROVED` status; retaining evidence provenance would clarify what settings
affected each result.

### Configuration plumbing: smaller interface needs consistent semantics

`settings.setup` mutates module globals. Some consumers read globals live;
others snapshot them at import time (`Oct.Infer.IUPPER`, `MMP.Infer.IUPPER`,
`Z3.RLIMIT`, `Z3.TIMEOUT_MS`). Normal single-run CLI setup happens before
`alg` is imported, so the ordinary CLI avoids the most obvious stale-default
case. Embedded/repeated use or tests can behave differently: after importing
Oct, changing settings.IUPPER to 100 left the inference class at 50 in a probe.

Optional optimization and simplification temporarily mutate the shared Z3
class limits. Sequential domains and forked workers make this workable in the
current CLI, but explicit per-run policy objects would make ownership clearer
and avoid import-order dependence.

The legacy benchmark reconstruction also has confirmed fidelity gaps:

- `settings.setup(None,args)` omits `maxdeg`; `analysis.Benchmark.start` does
  not add it back when constructing subprocess arguments. A requested degree
  can therefore disappear in this mode. The TSE recovery runner constructs
  argv explicitly and includes degree, so this finding does not invalidate
  that campaign.
- String output/read options emit the bare flag without their values.
- It constructs a string and then uses `.split()`, so quoted user terms and
  paths containing spaces are not reliably preserved.
- Positive tuning integers <1 are silently ignored by setup rather than
  consistently rejected. Other controls have separate validation behavior.

Recommendation: immutable per-run configuration plus a single validated
argv serializer used by CLI, web, and runners. This is an implementation fix
that makes existing parameters reliable before reducing their public surface.

## Controls to preserve

- Invariant family selection (`--types`) expresses user intent. Keep it.
- Symbolic versus trace-only mode changes the kind of evidence. Keep it.
- Degree ceilings express a useful explicit search restriction. Keep expert
  access; `MAX_TERM` can become an internal per-location allocation. Currently
  auto degree uses the location with the most variables for every location,
  and explicit degree bypasses the term cap. Recurrence generation is separate
  and does not receive the CLI equality ceiling; document its scope.
- Seed is useful for reproduction. Keep it. Task-keyed RNG streams would
  reduce coupling to invariant ordering and batch layout. Current
  `MP.N_BATCHES=12` fixes batches for reproducibility, and `-nomp` can change
  result streams; keep the latter a diagnostic control.
- Kapur/SYMBA and recurrence-multipath toggles remain research/diagnostic
  controls until comparative evidence supports automatic routing. Do not
  change their defaults solely to reduce flag count.
- Congruence minimum-value count is a trace-overfitting guard, not a proof
  threshold. Keep it internal and add independent validation where useful.
  Fix the known congruence simplification bottleneck before claiming full
  default-domain performance; global exclusion remains a recovery workaround.

## Recommended sequence

1. Fix empty sampling ranges, trace magnitude acceptance, numerical pruning,
   and option reconstruction. These address demonstrated defects without
   changing the accepted outer stopping rules.
2. Introduce explicit per-run configuration and resource-policy ownership;
   record effective settings and evidence provenance.
3. Automate bound magnitudes and input sampling; consolidate inequality
   template controls. Keep old overrides for exact reproduction.
4. Assess per-location degree allocation and shared trace collection as
   further simplifications. Preserve complicated candidate equations and
   separate discovery from confirmed semantic target recovery.
5. Validate each change independently on affected cases, then the 91-entry
   recovery suite across seeds 0..6, with strictly one DIG invocation at a
   time and internal multiprocessing enabled. Include a full-domain check
   for congruences. Compare semantic implications and retained interesting
   equations; do not require identical polynomial bases or overwrite golden
   results automatically. Knuth remains deferred.

The recommended ordinary interface retains family selection, mode, seed,
and an analysis budget, with a degree override available. Numeric input,
bound, sample-sizing, and template-policy details become automatic or expert
configuration. This is a proposed direction, not a claim that those parameters
have already been safely eliminated.

Follow-up: [limited parameter trials and implementation decisions](PARAMETER_TRIALS.md).

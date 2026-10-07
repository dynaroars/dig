# NLA-mosaic

Fourteen C benchmarks from eleven mathematical algorithm families. "Mosaic"
reflects the mix of number theory, polynomial dynamics, combinatorics,
statistics, and numerical integration.

Each file follows the existing NLA `mainQ`, `vassume`, and `vtrace` conventions.
Its header explains the computation, cites mathematical sources, identifies
our C adaptation, states expected relations at observation points, and gives
input and arithmetic assumptions. [manifest.json](manifest.json) records the
target expressions and degree budgets for the runner.

Input bounds keep integer updates within signed 32-bit range. Tuple updates use
temporaries. Invariant expressions in comments are mathematical specifications;
evaluating their expanded powers directly as C `int` expressions can overflow
even when the program's own updates remain within range.

## Measured DIG results

Tests ran on 2026-10-06 with seed 42, one run per program and configuration,
two concurrent jobs, and DIG's internal multiprocessing disabled. Equality
degree caps match the expected relation's degree; the expected polynomial is
used only to assess output and is never supplied to DIG as a hint.

| Program | Degree | Baseline C | Tuned C | Collected C traces |
|---|---:|---|---|---|
| pell | 2 | recovered | — | recovered |
| fibonacci | 4 | recovered | — | recovered |
| fibonacci_sign | 2 | recovered | — | recovered |
| markov | 3 | no result | no result | recovered |
| fibonacci_trace | 3 | no result | timeout | recovered |
| berggren | 2 | timeout | timeout | recovered |
| continued_fraction | 4 | no result | no result | recovered |
| continued_fraction_sign | 2 | recovered | — | recovered |
| chebyshev | 3 | no result | recovered | recovered |
| chebyshev_pair | 4 | no result | no result | recovered |
| nagata | 2 | no result | recovered | recovered |
| binomial | 2 | recovered | — | recovered |
| welford | 2 | no result | no result | no result |
| symplectic_euler | 3 | no result | no result | recovered |

"Recovered" means DIG printed the target polynomial equality, up to a nonzero
scalar multiple. Both target equalities are required for Welford. "No result"
means the process exited without reporting the target; raw logs distinguish
trace shortages from empty inference output. A dash means that configuration
was not run. Baseline uses `eqt,recurrence` with a 120-second limit. Tuned runs
add `-dokapur -inpMaxV 30` with a 90-second limit on baseline failures.

Direct C runs recovered targets for **7/14** programs across the two settings.
DIG inference from collected C traces recovered targets for **13/14**. These
are inference results, not a claim of unbounded verification. The ordinary
equality engine checks bounded symbolic states; the trace mode checks concrete
traces. The opt-in static engine has its own inductive verification path.

Evidence:

- [Baseline report](results/baseline/RESULTS.md), full commands and logs,
  and [JSON data](results/baseline/results.json).
- [Tuned report](results/tuned/RESULTS.md), full commands and logs,
  and [JSON data](results/tuned/results.json).
- [Trace report](results/traces/RESULTS.md), C-generated CSV inputs, full
  commands and logs, and [JSON data](results/traces/results.json).
- [Existing NLA annotation checks](results/legacy_annotations.json).

## Reproduce

From the repository root:

```sh
.venv/bin/python benchmark/c/NLA-mosaic/run_suite.py
.venv/bin/python benchmark/c/NLA-mosaic/run_suite.py --only markov fibonacci_trace berggren continued_fraction chebyshev chebyshev_pair nagata welford symplectic_euler --kapur --input-max 30 --timeout 90 --skip-validation --output benchmark/c/NLA-mosaic/results/tuned
.venv/bin/python benchmark/c/NLA-mosaic/run_suite.py --traces --types eqt --output benchmark/c/NLA-mosaic/results/traces
```

The runner retains complete logs and exports JSON and Markdown summaries. It
first instruments and compiles the C programs with warnings as errors and
UBSan, exercises boundary inputs and diverse cases, and evaluates the expected
polynomials exactly on the captured values. The trace configuration then gives
those same C-generated CSVs to DIG. These finite checks validate the examples
and catch translation mistakes; they do not establish completeness or proofs.

Welford illustrates the difference between an exact-real specification and C
floating point. Its validation traces had nonzero residuals for `n*mean-sum`
and `n*M2-n*sumsq+sum^2`, with maxima approximately `7.1e-15` and `3.4e-13`.
DIG did not recover either exact relation in the tested configurations. The
oscillator uses bounded dyadic steps, and its captured traces satisfy its
expected polynomial exactly.

## Existing NLA annotations

All C files in `../nla` and `../nla_full`, including archived subdirectories,
have purpose, source, and invariant headers. Sources distinguish the existing
DIG collection, related published algorithms, and exact implementation
provenance. Unverified original attribution is stated explicitly.

Expected relations follow each file's actual initialization, assignments,
and observation locations. `ps1` increments both variables by one, so its
basic equality is linear. `nla_full/geo1.c` scales its sum before its exit
trace, changing the exit equality. Archived files without active trace calls
are labeled accordingly. Existing executable code was preserved; corrections
to misleading old comments are documentation changes.

# Limited parameter trials — 2026-10-07

These trials test the recommendations in [PARAMETER_ANALYSIS.md](PARAMETER_ANALYSIS.md).
The accepted degree and depth stopping rules remain unchanged. Knuth stays deferred;
the golden baseline and the paper's full campaign results are not replaced.

## Scope and method

We ran 170 serialized DIG invocations across 22 small baseline/variant groups,
using 17 distinct programs. Each invocation kept internal multiprocessing enabled.
There was no full-suite campaign. Eleven difficult programs were selected explicitly:
Cohencu, EGCD2, EGCD3, Prod4br, Prodbin, Geo3, Ps6, Freire2, Sqrt1, H24 and H34.
Six spot checks were sampled deterministically from the existing recovery pool
(selection seed 20261007): Freire1, Hard, CAV09 Fig2d, PLDI09 Fig4_3, H41 and H43.
Most comparisons used seed 0; selected programs also used seed 3. Two checks enabled
congruences, which the ordinary recovery configurations exclude.

The comparison baseline was the working numerical implementation before these
parameter edits, frozen under local commit `b84f002`. It includes the existing TSE
recovery fixes, rather than the older remote numerical implementation. The focused
change also includes those numerical dependencies and the selected benchmark
annotations, so its code can run independently on the remote branch. The broader
paper/API-axiom baseline commit is not part of this change.

Each group changed one recommendation first; the accepted combination was then
checked on all 17 programs at seed 0. Follow-up coefficient extraction, template
policy and arithmetic edge fixes received targeted reruns and unit tests.
All 169 completed runs recovered their configured semantic targets. The remaining
run was an EGCD3 timeout in the rejected automatic-bound variant. Discovery counts
are not the criterion: different polynomial bases are acceptable when they imply
the target. High-degree equations, locations, status, settings and source hashes
are preserved in [results.json](../../benchmark/parameter_trials/results.json).

## Decisions

| Recommendation | Decision and evidence |
| --- | --- |
| Exact arithmetic for rank, fitting and trace validation | Adopt. Modular independence and exact residual/dimension checks certify the kernel; numerical support is only a hint. Rational, huge-coefficient and unlucky-prime tests pass. Preserve large-coefficient equations instead of filtering them by default. |
| Reuse fitting data and avoid repeated coefficient scans | Adopt with exact fitting. Reuse valid degree-estimation traces; extract each linear row once and cache it. This removed the Ps6 slowdown found during seed-3 checks. |
| Per-location automatic degree ceilings | Adopt. Five focused automatic-degree checks passed; explicit degree limits retain their meaning and stopping rules are unchanged. |
| Source-driven inequality templates | Adopt within the existing candidate budget and degree. Guards and additive updates supply candidate objectives that go through the ordinary SMT checks. Explicit IDEG/ITERMS/ICOEFS switches retain expert control. Sqrt1 recovered without its manual three-term override at seeds 0 and 3. |
| Solver resource policy | Adopt structural cleanup: scoped phase policies replace shared mutable limits, with existing budgets unchanged. No lower solver budget is proposed. |
| Configuration correctness and evidence | Adopt positive-integer validation, safe option serialization, live cap lookup, small input-range repair, exact large-trace validation, execution outcomes and per-result settings/exploration metadata. |
| Signed small/source-constant sampling | Reject as a default. All 17 targets passed, and H24/H34 could drop the magnitude override, but Ps6 and complexity spots slowed; total seed-0 time was 376.8s versus 352.9s baseline. Keep the legacy sampler, with the empty-range bug repaired. |
| Automatically expand constant-bound caps | Reject. Cohencu slowed from 14.3s to 34.4s; EGCD3 timed out at 240s. Retain the existing caps, while fixing their stale import-time lookup. |
| Reduce EQT_RATE to 1 and TRACE_MULTIPLIER to 1 | Reject. Geo3 took about 124s versus 18.1s and Ps6 about 21s versus 9.4s. Keep 1.5 and 5. |

Exact fitting initially made Geo3 slower when tested alone. Its acceptance depends
on the accompanying trace reuse and coefficient extraction, rather than treating
that isolated result as a performance win.

## Representative final comparisons

Elapsed wall time includes DIG startup and inference. These are individual runs,
not statistical estimates; small differences should not be read as reliable gains.

| Program / configuration | Baseline (s) | Latest accepted check (s) |
| --- | ---: | ---: |
| EGCD2, seed 0 | 88.360 | 79.695 |
| EGCD3, seed 0 | 151.889 | 143.020 |
| Geo3, seed 0 | 18.119 | 10.508 |
| Cohencu, seed 0 | 14.257 | 10.999 |
| Ps6, seed 0 | 9.386 | 7.589 |
| Ps6, seed 3 | 8.936 | 9.183 |
| Sqrt1, seed 3, final uses default term count | 4.741 | 4.278 |
| CAV09 Fig2d, seed 0 | 4.824 | 4.227 |
| PLDI09 Fig4_3, seed 0 | 4.876 | 4.125 |
| H41, seed 0 | 4.427 | 4.330 |
| H43, seed 3 | 3.574 | 3.676 |
| Cohencu, seed 0, congruences enabled | 24.470 | 19.562 |

The combined 17-program seed-0 group took 327.9s versus 352.9s baseline before
the last fitting optimization. Later focused checks retained every target and
removed the material Ps6 regression. Final focused numerical verification passed
239 tests. This limited sample gives no evidence of a material regression in the
accepted combination; it does not establish performance across all programs,
seeds, platforms or user-defined template settings.

## Evidence and reproduction

[benchmark/parameter_trials](../../benchmark/parameter_trials) contains compact
manifests and variant patches. Local raw logs and result pickles remain under
`benchmark/results/parameter_checks`; their recorded absolute paths identify the
original runs and are not portable download links. The runner
[run_parameter_checks.py](../../benchmark/run_parameter_checks.py) uses a shared
campaign lock and executes one benchmark at a time. Its limited fixture includes
only these 17 programs and their semantic targets. Use a fresh output directory:

```sh
/usr/bin/python3 benchmark/run_parameter_checks.py \
  --programs nla/cohencu nla/ps6 nla/sqrt1 \
  --seeds 0 --out benchmark/results/parameter_recheck
```

For baseline comparisons use `--source-root` with a frozen source checkout.
The fixture's recorded expert settings are applied unless explicitly omitted
with `--omit-setting`; Sqrt1's default-template trial omitted `iterms`.
Do not run this runner concurrently with any other DIG benchmark invocation.

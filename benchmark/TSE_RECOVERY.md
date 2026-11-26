# TSE target recovery work

The goal is to recover the targets of the TSE successes in the current
benchmark suites, including the previously failing cases and isolated seed
errors. A successful process exit alone does not count as recovery.

## Completed validation — 2026-10-07

All **91 required entries pass all seven seeds (0..6): 637/637 successful
runs**. This covers 90 TSE successes (27 NLA, 18 Complexity, 45 HOLA) and the
Freire integer control. Knuth remains deferred and unresolved, as requested;
the historical Java disjunction suite is outside this C campaign.

The final serialized runner in `results/tse_recovery/final_v2` exited with
status 0. A fresh audit checked every saved output, command/settings, source
hash, benchmark hash, and required program/seed pair, and reconfirmed all
**1,092 target implications**. Its evidence is in
[`final_audit.json`](results/tse_recovery/final_audit.json).
The [status report](TSE_RECOVERY_STATUS.md) and
[equality catalog](TSE_RECOVERY_INVARIANTS.md) record final per-program results.
`paper/paper.tex` now reports complete coverage and seven-seed medians/ranges.

Selected median times: Cohencu 14.760 s, Prod4br 14.009 s, Prodbin 6.989 s,
EGCD2 84.112 s, EGCD3 148.420 s. All seven runs are retained; these configured
recovery timings are not a controlled speedup comparison with TSE'21.
The focused implementation suite passed 218 tests; the subsequently improved
target checker passed four tests, including the quartic cancellation case.

## Execution and acceptance

- Historical equations need not reappear in the same form. Different bases
  can imply the same targets. Preserve complicated/high-degree alternative
  equalities for review even when target implication is missing or unknown.
  The user explicitly requested this distinction on 2026-10-07.
- The target checker also certifies constant-coefficient combinations by exact
  rational row reduction. On `pldi09_fig2` seed 3, division by the raw output
  basis missed a quartic target and SMT returned unknown; subtracting two
  generators and combining with the third certifies that same target. The
  saved output passes all three targets with this check, without changing DIG.
  Evidence: `results/tse_recovery/quartic_checker_audit.json`; the checker suite
  passes four tests, including generator-order independence and a false target.
- [The inferred equality catalog](TSE_RECOVERY_INVARIANTS.md) records actual
  equations, locations, degrees, monomial counts, and observed seeds. Its JSON
  companion also preserves per-run commands, hashes, timing, target checks,
  and DIG statuses. Refresh with `benchmark/catalog_tse_invariants.py`, which
  only reads saved output. `tests/golden.json` is an older regression baseline
  whose tests require matching sign-normalized equation strings; do not
  confuse it with semantic TSE recovery or automatically replace it.
- Run one `dig.py` invocation at a time, including seeds. Keep internal
  multiprocessing enabled. `run_tse_recovery.py` also holds a shared runner
  lock and kills/reaps the entire child process group on interruption/timeout.
- Exclude congruences with `-types eqt,ieq,minmax,array,recurrence`.
- `tse_recovery_targets.json` records source files, target locations/formulas,
  degree settings, and exploration/input settings. The first 19 entries cover
  the 16 original TSE regressions, Bresenham/Freire's isolated failures, and
  the integer Freire control. H04 has also been added: its source is executable
  despite its earlier relocation into `bad-programs`.
  The fixture now also covers all 28 NLA, 18 complexity, and 45 HOLA successes
  in the TSE tables, plus the additional Freire integer control (92 entries).
  This expanded coverage has now completed execution and target validation.
- Check each recovered output for consistency using a collected trace, then
  check implication of every listed target. Preserve missing/unknown outcomes.
  These checks establish target recovery; they do not turn bounded numerical
  inference into an unbounded inductive proof of every emitted invariant.
- Validate every required program over seeds 0..6 with the final source
  version. Preliminary runs during implementation are not final campaign
  evidence. Each run records source hashes, settings, times, target checks,
  and invariant status counts.

## Validated changes

1. Refine equality fitting against all collected concrete traces before
   accepting early-state candidates. Keep the basis through symbolic
   counterexample refinement instead of discarding it for large coefficients.
   Add diverse existing states when a whole fitting basis is underdetermined.
2. When the input space is exhausted, verify candidates fitted from available
   states instead of requiring an arbitrary minimum number of distinct rows.
   This recovers exact constants for parameterless H11/H30.
3. Honor explicit degree ceilings through the whole schedule and retain lower
   degree results. Finding an unrelated quadratic must not hide a cubic target.
4. Count symbolic forks inside concrete-guard loops, and allow deterministic
   tails with concrete counters to reach postconditions. This fixes the CAV09
   postconditions without changing their benchmark programs.
5. Run inference domains sequentially so their internal candidate pools can
   use the worker budget. Flatten trace validation and cache min/max evaluators.
6. Use certified bounded SAT search instead of nonlinear Optimize. Bound
   optional searches and redundancy checks separately; unknown optimization
   supplies no bound, unknown redundancy retains the original invariant.
7. Normalize quotient/remainder identities and substitute symbolic snapshots
   before SMT polynomial checking. Keep inconclusive feasibility paths.
8. Filter SymPy BooleanTrue/False out of equality results (the actual Freire
   seed-3 crash). Sample middle input ranges as well as small/high ranges.
9. Weaken bounds contradicted by later concrete traces instead of losing an
   otherwise useful weaker bound. The old symbolic bound implies the weaker
   one; equality claims are not weakened.
10. Supply stdio/assert headers when trace instrumentation adds their calls.
    H04 previously failed to compile its generated printf, despite an
    executable input program. Restore H18's loop bound from 5 to 100 to match
    both its documented assertion and the historical TSE benchmark.
11. Compile concrete C executions with signed-overflow traps and discard
    signal-terminated executions, including any already-printed trace prefix.
    The historical Geo3 seed-0 result had no equality output: 5 of its 271
    saved traces contradicted its documented polynomial because of overflow.
    This is a trace arithmetic mismatch, not evidence of successful recovery.
    The focused suite, including native overflow/header integration checks,
    passes 211 tests after this change.
12. Restore H41's historical four-variable trace (z, n, i, j). The current
    two-variable trace omitted the loop counter and sum used for TSE's
    nonlinear relations. Its historical campaign output did not imply z>2n.
    Use a degree-2 equality ceiling for this restored observation point.
13. Preserve the C backend's X_* entry-input namespace when replaying and
    excluding inputs. Complete unused input values in counterexample models,
    and serialize the namespace with symbolic states (including legacy-file
    compatibility). H20 previously generated zero concrete traces despite
    reachable symbolic states; it now recovers both assertions in 7.652 s.
14. Check polynomial output implications with exact rational polynomial
    division before SMT. A zero remainder is an equality-combination proof;
    a nonzero remainder supplies no verdict. Always check output consistency
    first, and do not use approximate coefficients for this certificate.
    This resolves Freire2's checker-unknown outcome without changing its output.
15. Keep degree hints within an explicit degree-1 ceiling. Use the documented
    nonlinear degrees for H05/H14/H17/H20/H21/H34/H41, and three-term linear
    bounds for Sqrt1's square-bound target. CohenCu's degree-2 basis already
    implies its cubic target and completes in 14.412 s.
16. Restore H31's two historical assertion locations. The initial fixture
    incorrectly applied its second assertion to a merged trace containing an
    extra exit location, where it is false for some negative inputs. Separate
    the first j-only observation from the second n/j/i observation, matching
    the historical assertion sites rather than imposing an invalid exit claim.
    Both targets now recover in 6.240 s. H41 and H21 recover in 4.481/13.050 s.

## Assessment of the solutions

Seven-seed recovery validates the combined implementation and recorded
configuration on these programs. It does not isolate the benefit of each
change or establish that the configuration is best for arbitrary programs.
The following judgments distinguish fixes we should keep from settings that
still deserve generalization.

| Program / change | Solution implemented | Assessment | Limit or follow-up |
| :--- | :--- | :--- | :--- |
| H20 / counterexample replay | Preserve `X_*` entry inputs, complete unused values, and use entry values for replay and exclusion; preserve the namespace in saved states. | **Permanent correctness fix.** Replaying mutated observation values was wrong. | Keep regression coverage for mutable and unused inputs and legacy saved states. |
| H04 / generated C | Supply stdio/assert headers required by instrumentation. | **Permanent correctness fix.** Valid source must not fail because instrumentation omitted its dependencies. | Additional instrumentation features should declare their own dependencies too. |
| H11/H30 / parameterless programs | Support empty input tuples and check available fitting relations when no additional inputs exist. | **Permanent support/correctness fix.** An arbitrary sample-count threshold must not prevent checking exact constants. | Sparse data still needs symbolic checking; this is not permission to trust an underdetermined fit. |
| Equality inference, including EGCD/Fermat/LCM | Check against all collected traces, add diverse violating rows, retain the fitting basis and large-coefficient generators, honor explicit degree ceilings, and preserve lower-degree results. | **Good general algorithmic improvements; keep them.** They address overfitting and accidental loss of useful equations. | More complete search can cost more; diversity selection and degree scheduling remain heuristics. These cases benefited from several fixes together, not a measured single-fix ablation. |
| CAV09a/d and symbolic checks | Reach deterministic concrete-counter tails, account for symbolic forks, substitute observed snapshots, and normalize identities before SMT. | **Good general implementation fixes.** They avoid unnecessary work and preserve reachable postconditions rather than moving trace markers to make a test pass. | Exploration is still bounded; reaching these exits does not establish completeness for other loops. |
| Freire crash | Exclude SymPy Boolean values from polynomial equality objects. | **Permanent type/representation fix.** A Boolean simplification result is not a polynomial generator. | Retain the regression; this does not resolve every real-arithmetic sampling issue. |
| Internal parallelism and trace checking | Run domains sequentially so internal pools work; flatten candidate testing and cache min/max evaluators. | **Good engineering changes; keep them.** No numerical domain is disabled by these scheduling/caching changes. | The best worker count and domain schedule may vary with hardware; separate DIG invocations must remain serialized. |
| Bound optimization and later trace checks | Certify integer maxima by SAT within a cap; reject unknown/nonintegral results; weaken eligible violated inequality bounds and retest. | **Good conservative design, with a coverage tradeoff.** It avoids accepting an uncertified optimum and can retain a useful weaker bound. | Caps can omit valid large bounds. Equality claims are never weakened; bounded-state evidence still needs a separate inductive proof for unbounded use. |
| Solver and Groebner budgets | Bound optional optimization/simplification queries; keep candidates on unknown redundancy; keep the original polynomial basis if simplification times out. | **Good durable safeguards; numeric limits are provisional tuning.** Cosmetic postprocessing should not block the entire analysis or destroy available results. | Time limits affect repeatability and output compactness; caps can reduce inference coverage. Graded reverse lexicographic order worked here but is not always fastest. |
| Geo3 / native overflow | Compile with `-ftrapv` and discard signal-terminated executions, including printed prefixes. | **Necessary safeguard for the current mathematical-integer trace pipeline, not a complete arithmetic solution.** Keep rejection of faulty executions. | This loses samples and relies on compiler trap behavior; it does not supply arbitrary-precision execution or a full C arithmetic model. A stronger trace backend should align arithmetic semantics explicitly. |
| Cohencu / congruences | Exclude congruences in the recovery configuration. | **Temporary workaround.** It avoids the observed congruence simplification bottleneck but removes a supported invariant family. | Preserve the successful configuration for reproduction; separately validate a full-domain configuration before claiming the congruence problem is fully solved. |
| Prod4br/Prodbin, EGCD3, H34, and explicit template/input settings | Use shallow per-program depths (usually 4; EGCD3 6; H34 12), recorded degree/input/template settings, and a 600-second ceiling. | **Effective recovery settings, not a general zero-configuration solution.** The old 120-second ceiling was insufficient for EGCD3. | Depth affects reachable-state coverage; manual ceilings/settings can miss other relations. Adaptive exploration and search scheduling would generalize this success. Raising a timeout alone is not an algorithmic improvement. |
| H18/H31/H41 / historical comparison | Restore the historical bound or trace variables/sites and correct the invalid merged-site target fixture. | **Necessary benchmark/evaluation repairs, not DIG algorithm improvements.** They make the comparison ask the intended question. | Keep changed benchmark hashes and the original baseline evidence. Success on the corrected observation is not a result on the earlier mismatched fixture. |
| Freire2 / PLDI09 fig2 target checker | Certify exact rational polynomial consequences and linear combinations, after output consistency checking. | **Permanent evaluation improvement.** Different bases should not be reported as failures solely because SMT is inconclusive. | A nonzero remainder is inconclusive, not a refutation. This improves recognition of recovered targets, not DIG's inferred output or unbounded program verification. |
| Knuth | Preserve the timed-out profile and defer further optimization. | **Unresolved; no implemented solution is claimed.** | Resume only if the user prioritizes it; existing evidence points to expensive active symbolic computation. |

My recommendation is to keep the correctness fixes and conservative
postprocessing safeguards. Treat congruence exclusion and manual per-program
search settings as reproducible recovery configurations, not as the final
general-purpose answer. The most useful remaining improvements are restoring
full-domain performance, making depth/degree scheduling adaptive, and giving
the trace backend an explicit arithmetic-semantics contract. These are future
work, not changes made or validated in this campaign.

## Preliminary evidence

Saved logs and manifests are in `results/tse_recovery/` and the earlier
`results/recheck_three/`. These include recovered targets for LCM1 at all
three locations, LCM2, EGCD including its determinant relation, H11/H30,
both CAV09 cases, H24, and Fermat1/Fermat2. Latest recorded sequential seed-0
times for the CAV09 cases are 4.675/3.872 s, H24 3.271 s, and Fermat1/Fermat2
11.961/11.952 s. They use different implementation checkpoints and must not
be combined into a final performance table.

EGCD3 recovered all 11 targets at depth 6 in 152.921 s (seed 0). H04 recovered
its positive-y target in 2.920 s after the header fix, and the restored H18
recovered j=100 in 4.072 s; the final seven-seed campaign also recovered it.
At the user's request, defer further Knuth optimization: the latest depth-4
profile timed out at 180 s and showed substantial symbolic exploration and
SymPy substitution costs. Keep Knuth unresolved rather than treating this as
recovery or repeatedly spending effort on it. Existing `fail.md` campaign
counts have not been overwritten.

The `validation_v1` campaign was explicitly interrupted after Cohencu seeds
0..4 passed, to fix the independently demonstrated Geo3 overflow issue.
These runs predate the overflow guard and are not final-source evidence.
The overflow follow-up recovered Geo3 (18.491 s), Geo1 (6.389 s), Geo2
(6.290 s), and Ps6 (9.338 s), all on seed 0. The full fixture now undergoes
a seed-0 pass excluding Knuth before another seven-seed campaign.

The remaining seed-0 probe completed all 63 requested programs successfully.
The first frozen-source seven-seed campaign ran in `results/tse_recovery/final_v1`.
It runs each seed across the suite before advancing to the next seed. Existing
successful runs are reused only after source/benchmark/target/settings checks
and a fresh check of their saved output. Their original logs and timings are
preserved; reused output is not presented as a newly executed benchmark.
Its seed-0 pass now covers all 91 required entries successfully: the 90 TSE
successes being pursued after the Knuth deferral, plus the Freire integer
control. That interim seed-0 result was not seven-seed completion. A later
seed-3 quartic checker unknown was resolved by exact rational row reduction,
and `final_v2` resumed with matching successes freshly checked before reuse.
The completed campaign and final audit are summarized at the top of this file.

## Commands

```bash
/usr/bin/python3 benchmark/run_tse_recovery.py --programs nla/lcm1 --seeds 0 1 2 3 4 5 6 --out benchmark/results/tse_recovery/final
/usr/bin/python3 benchmark/run_tse_recovery.py --exclude nla/knuth --seeds 0 1 2 3 4 5 6 --timeout 600 --stop-on-failure --out benchmark/results/tse_recovery/final
/usr/bin/python3 benchmark/run_tse_recovery.py --exclude nla/knuth --seeds 0 1 2 3 4 5 6 --timeout 600 --stop-on-failure --reuse-results benchmark/results/tse_recovery --out benchmark/results/tse_recovery/final_v1
/usr/bin/python3 -m pytest tests/test_bound_search.py tests/test_eqt_refinement.py tests/test_symex_postconditions.py tests/test_symex_c.py tests/test_recurrence.py -q
/usr/bin/python3 benchmark/generate_tse_recovery_report.py
```

For diagnostic worker stacks, add `--profile`. This uses `dig_profile.py` and
must not be treated as the performance configuration.

`TSE_RECOVERY_STATUS.md` lists every fixture and required seed. Its generator
excludes other source/benchmark versions and profiling runs, verifies the
listed target evidence and result/log presence, and shows the latest matching
run for each program/seed. It is a campaign summary, not an independent proof
checker. The historical HOLA target audit found missing targets in H20 and
H41 despite successful process exits. Its initial H31 check used an invalid
all-site assertion; the audit artifact records that caveat and the fixture
now matches the two historical assertion locations.

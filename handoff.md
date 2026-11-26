# Handoff Documentation: DIG-KN (Focus on Fixing Failures, Timeouts & Bad Results)

## Latest state — TSE recovery completed (2026-10-07)

The required C recovery scope is complete: **90 TSE successes plus the Freire
integer control pass all seven seeds, 637/637 runs**. Knuth remains deferred
and unresolved at the user's request. The Java disjunction suite is outside
this C campaign; the initial 111-program campaign remains historical evidence.

`benchmark/results/tse_recovery/final_v2` exited with status 0; no campaign is
still running. A fresh audit of all saved outputs, coverage, settings, and
source/benchmark hashes reconfirmed **1,092 target implications**. See
`benchmark/results/tse_recovery/final_audit.json`,
`benchmark/TSE_RECOVERY_STATUS.md`, and `benchmark/TSE_RECOVERY_INVARIANTS.md`
(with its JSON companion). The paper reports final seven-seed coverage and
timing medians/ranges. These checks establish target recovery, not unbounded
inductiveness of every emitted candidate.
`benchmark/TSE_RECOVERY.md` now assesses each solution's durability and limits;
the paper includes the same distinction. Congruence exclusion and manual search
settings are recovery workarounds, whereas input replay/instrumentation/type
fixes are lasting corrections. Overflow trapping is a safeguard, not a full
arithmetic-semantics solution. Do not describe all these interventions as
equally general or claim that Knuth has been solved.

Keep the one-DIG-at-a-time policy and preserve interesting alternative
polynomial bases. The older `tests/golden.json` remains a historical string
baseline, separate from semantic recovery. Earlier pending/run-status notes
below describe checkpoints and are superseded by this completed state.

This document provides a comprehensive operational briefing for restarting the session, with immediate focus on **debugging, optimizing, and fixing the remaining benchmark failures, timeouts, and underdetermined results**.

## Required benchmark execution policy

**Run benchmarks one at a time: never run multiple `dig.py` benchmark invocations
concurrently, including separate seeds.** Each run may use all available threads
and internal multiprocessing. Wait for the run and its workers to finish before
starting another, and coordinate across agents/sessions to prevent overlap.
Configure campaign runners with outer concurrency of one before using them;
several existing runners default to multiple concurrent DIG processes.
This explicit user requirement (2026-10-06) is also recorded in
[`AGENTS.md`](AGENTS.md).

### Follow-up on congruences (2026-10-06)

For the focused reruns of `cohencu`, `prod4br`, and `prodbin`, disable congruences
with `-types eqt,ieq,minmax,array,recurrence`. Keep internal multiprocessing on.
Sequential seed-0 runs recovered all expected equalities: `cohencu` in 9.596 s
at depth 16, `prod4br` in 17.052 s at depth 4, and `prodbin` in 10.384 s at
depth 4, with normal solver budgets. Congruence postprocessing explains the
`cohencu` timeout; the multiplication programs' depth-16 bottleneck occurs
earlier, in symbolic-state generation. These are focused diagnostics, not a
replacement seven-seed campaign. See
[`RECHECK.md`](benchmark/results/recheck_three/RECHECK.md) for commands and evidence.

---

## 1. Mission Objective & Current Status

- **Goal:** Fix and reduce the remaining 20 failing/timed-out programs across the 111 executable benchmarks.
- **Repository Root:** `/home/tnguyen/git/projects/dig`
- **Main Tool Core:** [`src/dig.py`](src/dig.py), [`src/alg.py`](src/alg.py), [`src/data/symex_c.py`](src/data/symex_c.py), [`src/infer/`](src/infer/)
- **Active Campaign Data:** `benchmark/results/campaign_extended_111/`
- **Current Performance Baseline (7 seeds, budget 120.0s, depth 16):**
  - **91 / 111 programs solved** (633 / 777 completed runs, **81.5% pass rate**).
  - **Suite Medians:** NLA: **18.33s**, NLA-mosaic: **20.97s**, Complexity: **15.55s**, HOLA: **9.42s**, Overall: **12.83s** (TSE'21 historical baseline: 38.2s).
  - **Remaining Unsolved Programs:** **20 programs** (16 SMT timeouts, 2 symbolic depth limits, 2 underdetermined parameterless traces).

---

## 2. Comprehensive Failure Catalog & Action Plan

All 20 failing benchmarks are categorized in [`fail.md`](fail.md) and Table 6 of [`paper/paper.tex`](paper/paper.tex).

### Group 1: Nonlinear SMT Solver Timeouts (16 Programs)

| Suite | Benchmark Programs |
| :--- | :--- |
| **NLA** (12 progs) | `cohencu.c`, `egcd.c`, `egcd2.c`, `egcd3.c`, `fermat1.c`, `fermat2.c`, `knuth.c`, `lcm1.c`, `lcm2.c`, `prod4br.c`, `prodbin.c`, `wensley.c` |
| **NLA-mosaic** (3 progs) | `berggren.c`, `fibonacci_trace.c`, `symplectic_euler.c` |
| **HOLA** (1 prog) | `24.dig.c` |

#### Root Cause Analysis:
1. **Monomial Combinatorial Explosion in CEGIR:**
   - On programs with $V \ge 4$ variables and non-linear polynomial templates of degree $d \ge 3$, the monomial basis size $\binom{V+d}{d}$ exceeds 35–56 terms.
   - During CEGIR in [`src/infer/eqt.py`](src/infer/eqt.py), checking candidate equalities $\Pi_L \land \neg(p(\sigma_L) = 0)$ over multi-branch symbolic paths generates hard non-linear integer arithmetic ($QF\_NIA$) queries in Z3.
2. **SMT Redundancy Simplification Bottlenecks:**
   - In [`src/infer/invs.py`](src/infer/invs.py) (`dinvs.simplify()`), testing pairwise implications $\bigwedge (\mathcal{C} \setminus \{p\}) \implies p$ across dozens of non-linear candidates repeatedly invokes Z3 on non-linear arithmetic formulas without query-level timeouts.

#### Actionable Strategies to Fix:
- **Strategy 1A: Query-Level SMT Timeouts & Fallback Tactics in CEGIR:**
  - In `infer/eqt.py` and `infer/mp.py`, wrap Z3 solver calls with a deterministic per-query `rlimit` / timeout (e.g. 2–5 seconds per candidate check). If a counterexample query times out, discard the unprovable high-degree candidate rather than hanging the entire tool.
- **Strategy 1B: Monomial Pruning by Trace Covariance:**
  - Before instantiating the full $\binom{V+d}{d}$ template matrix, analyze sampled trace variance: if two variables never covary or a monomial term has zero correlation, prune it from the candidate basis.
- **Strategy 1C: Incremental / Staged Redundancy Simplification:**
  - In `dinvs.simplify()`, simplify linear and octagonal constraints first, then simplify non-linear equalities against the reduced basis.
- **Strategy 1D: Static Kapur Ideal Pre-Pass for Straight-Line Programs:**
  - For programs with straight-line transitions (e.g. `cohencu.c`, `fibonacci_trace.c`), invoke the algebraic ideal solver ([`src/infer/kapur.py`](src/infer/kapur.py)), which computes Gröbner bases in $<0.15$\,s without SMT CEGIR loops.

---

### Group 2: Symbolic Loop Depth Limits on Postconditions (2 Programs)

| Suite | Benchmark Programs | Root Cause |
| :--- | :--- | :--- |
| **Complexity** | `cav09_fig1a.c`, `cav09_fig1d.c` | Postcondition `vtrace_post` placed after a symbolic loop with 100 iterations (`while (x < 100)`). |

#### Root Cause Analysis:
- In `cav09_fig1a.c`, `while(x < 100) { if (y < m) y++; else x++; }` takes a symbolic input parameter `m`.
- The branch `if (y < m)` is symbolic, forking true/false paths on every iteration.
- Because $x$ only increments on the false branch, reaching the exit $x = 100$ requires $>100$ symbolic loop iterations, exceeding `--se_maxdepth 16`.

#### Actionable Strategies to Fix:
- **Option A (State Merging):** Enable state merging (`--merge-states` in `src/data/symex_c.py`), collapsing the if/else diamond into an `If(y < m, y+1, y)` expression, reducing $2^{16}$ paths to 1 merged symbolic path.
- **Option B (Loop Summarization / Loop-Head Instrumentation):** Instrument the loop head `vtrace(m, x, y, tCtr)` rather than only the postcondition after 100 iterations, enabling DIG to infer inductive relations during iteration.

---

### Group 3: Underdetermined Single-Point Traces on `mainQ(void)` (2 Programs)

| Suite | Benchmark Programs | Status & Root Cause |
| :--- | :--- | :--- |
| **HOLA** | `11.dig.c`, `30.dig.c` | Concrete unrolling reaches postcondition (100 iters in 0.15s, 1000 iters in 1.31s). Produces 1 data point because `mainQ(void)` has no parameters. |

#### Root Cause Analysis:
- With the newly added concrete loop fast-path in `src/data/symex_c.py`, both `11.dig.c` and `30.dig.c` execute completely to `vtrace` with $(j=200, x=100)$ and $(c=499500)$.
- However, because `mainQ(void)` has no input parameters, concrete execution produces only **1 trace point**.
- Dynamic equation fitting over 1 point is mathematically underdetermined ($c_1 j + c_2 x + c_0 = 0$ has 3 unknowns).

#### Actionable Strategies to Fix:
- For postcondition invariant discovery: Parameterize input bounds (e.g., `mainQ(int x)`) or record loop-head iterations `vtrace(i, j, x)` so dynamic sampling captures $\ge 3$ distinct states.
- In inductive prover mode (`--prove`), DIG proves the loop invariant $j = 2i$ in $<0.02$\,s.

---

### Group 4: Flaky / Isolated Seed Errors (3 Programs)

| Suite | Benchmark | Issue | Recommended Fix |
| :--- | :--- | :--- | :--- |
| **NLA** | `freire1.c` | 1/7 seed crash (`error_exit_1`) | Inspect exception trace on seed 3; add guard in AST expression evaluator for float/int division edge cases. |
| **NLA** | `bresenham.c` | 1/7 seed timeout | Tighten solver work budget (`rlimit`) to avoid single-seed solver stall. |
| **NLA-mosaic** | `welford.c` | 2/7 seed timeouts | High-degree variance polynomial ($d=2$ over rational divisions); prune higher-order templates when rational terms are present. |

---

## 3. Recent Implementation State

1. **Concrete Loop Fast-Path in `src/data/symex_c.py`:**
   - Concrete guards (`z3.is_true(cond)`) execute in $O(1)$ without SMT branching or depth consumption up to `MAX_CONCRETE_STEPS = 50_000`.
   - Iterative worklist loop eliminates Python recursion depth limits.
   - All 184 tests in [`tests/test_symex_c.py`](tests/test_symex_c.py) pass.
2. **Structural / Input Anomaly Relocations:**
   - Moved non-executable / unreachable benchmarks to `benchmark/bad-programs/`:
     - `benchmark/bad-programs/pldi09_fig1.c` (placeholder file lacking C `main()`).
     - `benchmark/bad-programs/04.dig.c` (unreachable trace under precondition).
3. **Paper & Documentation Alignment:**
   - `paper/paper.tex` compiles with 0 errors to [`paper/paper.pdf`](paper/paper.pdf) (Springer LNCS format).
   - Claims accurately reflect symbolic-state constraint verification as the default inference mechanism.

---

## 4. Key Execution & Reproduction Commands

### Reproducing a Single Benchmark Failure:
```bash
# Example: SMT timeout on knuth.c
python3 -O src/dig.py benchmark/c/nla/knuth.c --se_maxdepth 16 -seed 42

# Example: SMT timeout on cohencu.c
python3 -O src/dig.py benchmark/c/nla/cohencu.c --se_maxdepth 16 -seed 42

# Example: Underdetermined trace on 11.dig.c
python3 -O src/dig.py benchmark/c/hola/11.dig.c --se_maxdepth 16 -seed 42
```

### Running Test Suites:
```bash
# Run all symbolic execution tests
pytest tests/test_symex_c.py

# Run recurrence solver tests
pytest tests/test_recurrence.py
```

### Running Full Campaign & Generating Reports:
```bash
# Execute extended campaign across all 111 benchmarks
python3 benchmark/run_extended_campaign.py

# Generate report and updated fail.md
python3 benchmark/generate_extended_report.py benchmark/results/campaign_extended_111
```

### Compiling LaTeX Paper:
```bash
make -B -C paper
```


## TSE recovery follow-up (2026-10-06)

Use `benchmark/TSE_RECOVERY.md` and the target manifests for the latest
recovery state; the original campaign counts above remain historical.

- The user asked to defer further Knuth optimization rather than spend
  excessive effort on it. Its latest depth-4 diagnostic timed out at 180 s.
- EGCD3 now reaches all four locations at depth 6 and recovered all 11 listed
  equalities in 152.921 s (seed 0); seven-seed validation is pending.
- H04 was incorrectly described above as unreachable. Its generated trace
  program lacked stdio.h for printf. Supplying instrumentation headers
  recovered its y>0 target in 2.920 s. Its staged relocation is preserved.
- H18's loop bound was 5, inconsistent with its assertion j=100 and the TSE
  benchmark. Restoring 100 recovered its target in 4.072 s.
- The target fixture now includes 91 successes from TSE's NLA, complexity,
  and HOLA tables plus a Freire integer control. All 162 target expressions
  parse and reference declared trace variables. Expanded target execution
  and seven-seed validation remain required.
- A sequential validation campaign excludes Knuth and uses source hashes,
  target implication checks, and stop-on-failure. Never infer recovery from
  process exit alone or run a second DIG invocation while it is active.

The first validation campaign was explicitly interrupted after Cohencu seeds
0..4 passed. Historical Geo3 seed-0 output had no equality and 5/271 saved
traces contradicted its target because of signed integer overflow. Concrete
C executions now use -ftrapv, and signal-terminated executions contribute no
traces, including printed prefixes. The focused suite passes 211 tests.
Revalidate the campaign with the final source; validation_v1 predates this fix.

Further target audits recovered H20 through the X_* entry-input namespace
fix (including unused-input completion and input exclusion). H31 now has
its two historical assertion locations; the earlier all-site target was
invalid at an extra exit trace for some negative inputs. H41's historical
four-variable observation has been restored. Freire2 target implication
uses exact rational polynomial division when possible, after output
consistency checking. The focused suite passes 218 tests.

A sequential remaining-seed-0 probe checks 63 programs under the current
source, stopping at the first target failure. Its output is in
benchmark/results/tse_recovery/remaining_seed0. Regenerate
benchmark/TSE_RECOVERY_STATUS.md with generate_tse_recovery_report.py.
Full seven-seed validation remains pending; do not mark recovery complete.

The remaining-seed-0 probe completed all 63 programs with successful target
checks. The frozen-source campaign now runs seeds 0..6 in final_v1, excluding
Knuth. It traverses the suite for each seed, reusing prior matching successes
only after fresh output implication/consistency checks and settings checks.
The original log paths/timings are retained in reused rows. This campaign
still needs to finish before seven-seed recovery can be claimed.

final_v1 has completed all 91 required seed-0 entries successfully (90 TSE
successes excluding deferred Knuth, plus the Freire integer control). Seeds
1..6 are now running. Do not restart the live campaign merely because a
status poll is quiet; resume its current session/job and keep runs serialized.

The user clarified that recovered equalities need not look exactly like the
historical equations. Preserve interesting high-degree alternatives for review.
`benchmark/TSE_RECOVERY_INVARIANTS.md` and its JSON companion now catalog actual
polynomial equalities per program/location/seed, including degrees and monomial
counts; the JSON retains commands, hashes, timings, target outcomes, and saved
DIG statuses. Refresh with `benchmark/catalog_tse_invariants.py` (reads saved
results only). This observational catalog is separate from semantic target
recovery and from the older string-based `tests/golden.json` baseline.

`paper/paper.tex` was updated on 2026-10-07 with the current recovery protocol,
seed-0 coverage and selected timings, semantic acceptance and alternative
equation recording, implementation fixes, and benchmark/fixture alignment.
The original campaign statistics are explicitly baseline observations rather
than current target-recovery claims; the old failure taxonomy now records the
observed follow-up instead of speculative root causes. Seven-seed validation
is still marked pending. `make -C paper paper.pdf` succeeded, and all ten new
timing rows were checked against the final_v1 manifest. The final LaTeX log
has no errors or undefined references/citations (ordinary layout warnings remain).

The live final_v1 campaign has now completed all 91 required entries at seeds
0, 1, and 2: 273 target-confirmed checks, with no failures. Seeds 3--6 remain
in progress. The status/equality catalogs and paper snapshot have been refreshed;
the PDF rebuild passed. Keep using the existing live runner rather than starting
a second campaign, and do not claim seven-seed completion yet.

final_v1 stopped (terminal exit 1) at `complexity/pldi09_fig2` seed 3 because
one quartic implication returned unknown. Exact analysis of its saved output
proved the target by a constant linear combination of three generators. The
target checker now uses rational row reduction before raw polynomial division;
four focused checker tests pass, and the saved output passes all three targets.
The inference source is unchanged. `quartic_checker_audit.json` preserves both
the original unknown outcome and the fresh certificate-based checks.
The serialized campaign has resumed in `final_v2`, reusing matching successes
only after fresh checks, and rerunning the formerly unknown case. final_v1 is
no longer live; do not resume or restart it alongside final_v2.

final_v2 has completed all 91 required entries at seeds 0--3: 364 successful
target checks. The quartic case passed a fresh seed-3 run with the improved
checker. Seed 4 is now live, and seeds 4--6 remain required. The paper snapshot
includes the exact quartic cancellation certificate and four-seed coverage.

final_v2 has since completed every required entry at seeds 0--4: 455 successful
checks. Seed 5 is live; seeds 5 and 6 remain required. No new target failure
has appeared after the exact-combination checker correction. Reports and the
paper snapshot now reflect five complete seeds.

final_v2 has completed seeds 0--5 for every required entry: 546 successful
checks. Seed 6, the final required seed, is now running. Cohencu has already
passed all seven seeds. Reports and the paper snapshot reflect six complete
seeds; keep the goal active until every required seed-6 result is checked.

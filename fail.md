# DIG-KN Evaluation Campaign: Failed & Timed-Out Benchmarks

**Follow-up completed (2026-10-07):** all 90 pursued TSE successes and the
Freire integer control pass all seven seeds (637/637 runs). A fresh audit
reconfirmed 1,092 target implications with matching source/benchmark hashes
and settings. Knuth remains deferred. See
[`TSE_RECOVERY_STATUS.md`](benchmark/TSE_RECOVERY_STATUS.md) and
[`final_audit.json`](benchmark/results/tse_recovery/final_audit.json).
The original failure counts below are historical and are preserved.
The [solution assessment](benchmark/TSE_RECOVERY.md#assessment-of-the-solutions)
records each implemented remedy, whether it is a lasting fix or a recovery
workaround, and the remaining limitations.

**Campaign Directory:** `benchmark/results/campaign_extended_111`  
**Git Commit:** `859839a1b83c5fd74db13cf09cc25bc5fdf24236`  
**Timeout Budget:** 120.0s per seed  
**Depth Limit:** --se_maxdepth 16  
**Total Attempted Runs:** 777 (across 111 programs)  
**Total Failed / Timed-Out Runs:** 144 / 777  

## 1. Summary by Suite

| Suite | Total Programs | Programs with Failures/Timeouts | Total Failed Runs | Primary Failure Causes |
| :--- | :---: | :---: | :---: | :--- |
| **COMPLEXITY** | 19 | 2 | 14 | depth_limit: 14 |
| **HOLA** | 45 | 3 | 21 | depth_limit: 14, timeout: 7 |
| **NLA** | 33 | 14 | 86 | timeout: 85, error_exit_1: 1 |
| **NLA-MOSAIC** | 14 | 4 | 23 | timeout: 23 |

## 2. Failure Classification Breakdown

- **`timeout`** (115 runs): Execution exceeded the 120.0s per-seed timeout budget. This outcome alone does not identify the stage: follow-up checks found congruence redundancy simplification in `cohencu` and symbolic-state generation in `prod4br` and `prodbin` (see below).
- **`depth_limit`** (28 runs): Symbolic execution could not reach target trace locations within exploration depth (`--se_maxdepth 16`).
- **`error_exit_1`** (1 runs): Non-zero exit code or exception during execution.

## 3. Program-by-Program Failure Catalog

| Suite | Program | Failed Runs / Total | Failure Outcomes | Sample Log File |
| :--- | :--- | :---: | :--- | :--- |
| COMPLEXITY | `cav09_fig1a.c` | 7/7 | depth_limit (7x) | [`benchmark/results/campaign_extended_111/logs/complexity/cav09_fig1a/seed_1.log`](benchmark/results/campaign_extended_111/logs/complexity/cav09_fig1a/seed_1.log) |
| COMPLEXITY | `cav09_fig1d.c` | 7/7 | depth_limit (7x) | [`benchmark/results/campaign_extended_111/logs/complexity/cav09_fig1d/seed_0.log`](benchmark/results/campaign_extended_111/logs/complexity/cav09_fig1d/seed_0.log) |
| HOLA | `11.dig.c` | 7/7 | depth_limit (7x) | [`benchmark/results/campaign_extended_111/logs/hola/11.dig/seed_0.log`](benchmark/results/campaign_extended_111/logs/hola/11.dig/seed_0.log) |
| HOLA | `24.dig.c` | 7/7 | timeout (7x) | [`benchmark/results/campaign_extended_111/logs/hola/24.dig/seed_0.log`](benchmark/results/campaign_extended_111/logs/hola/24.dig/seed_0.log) |
| HOLA | `30.dig.c` | 7/7 | depth_limit (7x) | [`benchmark/results/campaign_extended_111/logs/hola/30.dig/seed_0.log`](benchmark/results/campaign_extended_111/logs/hola/30.dig/seed_0.log) |
| NLA | `bresenham.c` | 1/7 | timeout (1x) | [`benchmark/results/campaign_extended_111/logs/nla/bresenham/seed_6.log`](benchmark/results/campaign_extended_111/logs/nla/bresenham/seed_6.log) |
| NLA | `cohencu.c` | 7/7 | timeout (7x) | [`benchmark/results/campaign_extended_111/logs/nla/cohencu/seed_0.log`](benchmark/results/campaign_extended_111/logs/nla/cohencu/seed_0.log) |
| NLA | `egcd.c` | 7/7 | timeout (7x) | [`benchmark/results/campaign_extended_111/logs/nla/egcd/seed_0.log`](benchmark/results/campaign_extended_111/logs/nla/egcd/seed_0.log) |
| NLA | `egcd2.c` | 7/7 | timeout (7x) | [`benchmark/results/campaign_extended_111/logs/nla/egcd2/seed_0.log`](benchmark/results/campaign_extended_111/logs/nla/egcd2/seed_0.log) |
| NLA | `egcd3.c` | 7/7 | timeout (7x) | [`benchmark/results/campaign_extended_111/logs/nla/egcd3/seed_0.log`](benchmark/results/campaign_extended_111/logs/nla/egcd3/seed_0.log) |
| NLA | `fermat1.c` | 7/7 | timeout (7x) | [`benchmark/results/campaign_extended_111/logs/nla/fermat1/seed_0.log`](benchmark/results/campaign_extended_111/logs/nla/fermat1/seed_0.log) |
| NLA | `fermat2.c` | 7/7 | timeout (7x) | [`benchmark/results/campaign_extended_111/logs/nla/fermat2/seed_0.log`](benchmark/results/campaign_extended_111/logs/nla/fermat2/seed_0.log) |
| NLA | `freire1.c` | 1/7 | error_exit_1 (1x) | [`benchmark/results/campaign_extended_111/logs/nla/freire1/seed_3.log`](benchmark/results/campaign_extended_111/logs/nla/freire1/seed_3.log) |
| NLA | `knuth.c` | 7/7 | timeout (7x) | [`benchmark/results/campaign_extended_111/logs/nla/knuth/seed_0.log`](benchmark/results/campaign_extended_111/logs/nla/knuth/seed_0.log) |
| NLA | `lcm1.c` | 7/7 | timeout (7x) | [`benchmark/results/campaign_extended_111/logs/nla/lcm1/seed_0.log`](benchmark/results/campaign_extended_111/logs/nla/lcm1/seed_0.log) |
| NLA | `lcm2.c` | 7/7 | timeout (7x) | [`benchmark/results/campaign_extended_111/logs/nla/lcm2/seed_0.log`](benchmark/results/campaign_extended_111/logs/nla/lcm2/seed_0.log) |
| NLA | `prod4br.c` | 7/7 | timeout (7x) | [`benchmark/results/campaign_extended_111/logs/nla/prod4br/seed_0.log`](benchmark/results/campaign_extended_111/logs/nla/prod4br/seed_0.log) |
| NLA | `prodbin.c` | 7/7 | timeout (7x) | [`benchmark/results/campaign_extended_111/logs/nla/prodbin/seed_0.log`](benchmark/results/campaign_extended_111/logs/nla/prodbin/seed_0.log) |
| NLA | `wensley.c` | 7/7 | timeout (7x) | [`benchmark/results/campaign_extended_111/logs/nla/wensley/seed_0.log`](benchmark/results/campaign_extended_111/logs/nla/wensley/seed_0.log) |
| NLA-MOSAIC | `berggren.c` | 7/7 | timeout (7x) | [`benchmark/results/campaign_extended_111/logs/NLA-mosaic/berggren/seed_0.log`](benchmark/results/campaign_extended_111/logs/NLA-mosaic/berggren/seed_0.log) |
| NLA-MOSAIC | `fibonacci_trace.c` | 7/7 | timeout (7x) | [`benchmark/results/campaign_extended_111/logs/NLA-mosaic/fibonacci_trace/seed_0.log`](benchmark/results/campaign_extended_111/logs/NLA-mosaic/fibonacci_trace/seed_0.log) |
| NLA-MOSAIC | `symplectic_euler.c` | 7/7 | timeout (7x) | [`benchmark/results/campaign_extended_111/logs/NLA-mosaic/symplectic_euler/seed_0.log`](benchmark/results/campaign_extended_111/logs/NLA-mosaic/symplectic_euler/seed_0.log) |
| NLA-MOSAIC | `welford.c` | 2/7 | timeout (2x) | [`benchmark/results/campaign_extended_111/logs/NLA-mosaic/welford/seed_3.log`](benchmark/results/campaign_extended_111/logs/NLA-mosaic/welford/seed_3.log) |

---

### Diagnostic Notes & Recommended Resolutions

#### Congruence follow-up — 2026-10-06

**Congruence postprocessing caused the `cohencu` timeout in the focused recheck.**
The program discovered its equalities quickly, then stalled during redundancy
simplification. Excluding congruences with
`-types eqt,ieq,minmax,array,recurrence` let it finish in **9.596 s** at the
original depth 16 and normal solver budget, recovering all three expected
equalities. Use this type selection for follow-up failure diagnostics; retain
internal multiprocessing and run only one `dig.py` invocation at a time.

| Program | Depth without congruences | Wall time | Expected equalities |
| :--- | :---: | :---: | :--- |
| `cohencu.c` | 16 | 9.596 s | All three recovered |
| `prod4br.c` | 4 | 17.052 s | Multiplication identity recovered |
| `prodbin.c` | 4 | 10.384 s | Loop and exit identities recovered |

For `prod4br` and `prodbin`, the original depth-16 timeout occurs **before
congruence inference**, during symbolic-state generation. Both also complete
at depth 4 with congruences enabled (16.703 s and 9.782 s, respectively).
Their remedy is shallower/adaptive exploration; disabling congruences alone
does not address the observed bottleneck. Congruences have not been established
as the cause of the other catalogued failures.

These are sequential **seed-0 diagnostics**, not a replacement seven-seed
campaign. The failure counts above remain the original campaign results.
Commands, logs, and target checks are recorded in
[`RECHECK.md`](benchmark/results/recheck_three/RECHECK.md).

#### Other diagnostic guidance

1. **For `timeout` benchmarks:** Identify the stage from logs before increasing solver budgets or template degrees. Nonlinear candidate checking, symbolic-path exploration, and redundancy simplification can each exhaust the run budget. The focused rechecks do not support the earlier blanket claim that `cohencu`, `prod4br`, and `prodbin` require degree-four-or-higher templates.
2. **For `depth_limit` benchmarks:** Inspect the generated symbolic exit states and concrete trace handling before assuming deep unrolling is required. Current CAV09a/d exit states are available at depth 4; H11/H30 recovered through parameterless trace/fitting handling. The earlier explanation that these cases necessarily require unrolling 100--1000 iterations was not supported by the rechecks.


#### Target-level audit follow-up — 2026-10-07

The campaign's successful exits are not evidence that its expected targets
were recovered. The broader TSE audit found additional gaps:

- **Geo3:** historical seed 0 emitted no equality. Five of 271 saved traces
  contradicted its documented polynomial because of signed integer overflow.
  Native runs now trap signed overflow and discard signal-terminated runs,
  including printed trace prefixes. The target subsequently recovered.
- **H20:** entry-input symbols (`X_*`) were not used for replay/exclusion, so
  symbolic counterexamples failed to generate full concrete input tuples.
  Preserving that namespace and completing unused inputs recovered both
  assertions (7.652 s, seed 0).
- **H41:** the current trace omitted two variables recorded in TSE. Restoring
  z/n/i/j recovered the assertion (4.481 s, seed 0).
- **H31:** the initial comparison incorrectly imposed its second assertion
  on a merged trace containing an extra exit site. It is false there for
  some negative inputs. Restoring the two historical assertion sites
  recovered both required assertions (6.240 s, seed 0).
- **Freire2:** an implication check returned unknown even though two output
  equalities imply the cubic target. Exact rational polynomial division now
  certifies that consequence after checking output consistency.

These are preliminary target checks at different checkpoints, not final
seven-seed campaign results. Use `benchmark/TSE_RECOVERY_STATUS.md` for
current-source coverage, and retain the original campaign counts above.
Knuth remains deferred at the user's request.

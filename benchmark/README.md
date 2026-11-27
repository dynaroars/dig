# DIG Benchmarks

This directory contains the C benchmark suites used to evaluate DIG's invariant inference and Lean 4 certification pipelines.

---

## Active Benchmark Suites

| Suite | Path | Count | Focus |
| --- | --- | --- | --- |
| **NLA** | `benchmark/c/nla/` | 29 `.c` | Core nonlinear arithmetic benchmarks (SV-COMP `nla-digbench` / TSE'21 Table 1): integer division, GCD/LCM, power sums (`ps2`–`ps6`), geometric series, Bresenham, Fermat, Dijkstra, etc. |
| **NLA-mosaic** | `benchmark/c/NLA-mosaic/` | 14 `.c` | Curated modern nonlinear benchmarks beyond TSE'21: Fibonacci/Cassini quartic, Fibonacci 3D trace map, Chebyshev polynomials (`T_n` and `T_n`/`U_{n-1}`), continued fractions, Berggren Pythagorean triples, Markov, Nagata, Pell, symplectic Euler, Welford. |
| **Complexity** | `benchmark/c/complexity/` | 19 `.c` | Runtime complexity bound benchmarks from TSE'21 Table 2 (CAV'09, PLDI'09, POPL'09). |
| **HOLA** | `benchmark/c/hola/` | 46 `.c` | Linear / disjunctive / assertion-checking benchmarks from SyGuS / TSE'21 Table 4 (untouched in this audit). |

---

## Cleanup Audit & Removal Decisions

The following redundant, trivial, or stale items were removed to keep the benchmark set focused and maintainable:

1. **`benchmark/c/nla_full/` (removed entire directory — 26 `.c` files + `a.out`, `fail`, `printf`):**
   - 25 of 26 `.c` files were older Sage-era duplicates of `benchmark/c/nla/` (differing only by extra exit `vtrace` calls and commented assertions), plus stray compiled/scratch files (`a.out`, `fail`, `printf`). Not referenced by `tests/dig_harness.py`, `tests/golden.json`, or `web/`.
   - The single extra file (`knuth_nosqrt.c`) was a variant of `knuth.c`, which is deferred per `AGENTS.md`.
2. **`benchmark/c/nla/ps1.c` (removed):**
   - Trivial linear loop (`x == y`), not in TSE'21 Table 1. `ps2.c`–`ps6.c` already cover degree 2–6 power sums.
3. **`benchmark/c/nla/freire1.c` (removed):**
   - Floating-point duplicate of `benchmark/c/nla/freire1_int.c` (TSE'21 Table 1 used the integer version). `freire2.c` is retained as the representative floating-point benchmark from TSE'21 Table 1.
4. **`benchmark/c/nla/ariths.c` and `benchmark/c/nla/wensley.c` (removed):**
   - Extra floating-point benchmarks not in TSE'21 Table 1 and outside the integer scope of DIG's Lean 4 certifier.
5. **`benchmark/c/complexity/pldi09_fig1.c` (removed):**
   - Not in TSE'21 Table 2 and a persistent failure in `tests/golden.json`.
6. **`benchmark/c/NLA-mosaic/__pycache__/` (removed):**
   - Stray Python bytecode cache.

### Deliberately Retained
- **`benchmark/c/nla/isqrt.c`:** Retained because `tests/test_certify_lean.py` uses it directly to test real-guard (`while ((r+1)*(r+1) <= n)`) Lean certification and non-1-inductive handling.
- **`benchmark/c/nla/freire2.c`:** Retained as the TSE'21 Table 1 floating-point benchmark (also exercises graceful `unsupported` handling in `--certify-lean`).
- **`benchmark/c/nla/knuth.c`:** Retained for historical completeness and deferred per `AGENTS.md`.
- **All 14 `benchmark/c/NLA-mosaic/` files:** Every file tests a distinct invariant degree or mathematical family (e.g., quartic Cassini `fibonacci.c` vs. degree-2 sign-tracked `fibonacci_sign.c` vs. cubic 3D trace map `fibonacci_trace.c`), and the suite is served directly by `web/server.py`.
- **`tests/golden.json`:** Left untouched per `AGENTS.md` (do not automatically overwrite the golden baseline); `tests/test_benchmarks.py` only iterates over `.c` files present on disk.

---

## Running Benchmarks

Per `AGENTS.md`, run DIG benchmarks **strictly one at a time** (never launch multiple `dig.py` processes concurrently; internal multiprocessing within a single run stays enabled):

```bash
.venv/bin/python -O src/dig.py benchmark/c/nla/cohendiv.c -seed 42
.venv/bin/python -O src/dig.py benchmark/c/nla/cohendiv.c -seed 42 --certify-lean
```

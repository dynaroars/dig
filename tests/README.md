# Tests

## symex_c unit tests + benchmark (fast, no DIG run)

`test_symex_c.py` unit-tests the Python symbolic execution engine
(`src/data/symex_c.py`) in isolation: each test writes a tiny C program to a
tmp dir, runs `CSymEx`, and checks the resulting `(loc, pc, slocal)` z3
records by entailment/satisfiability (not string matching). Covers parsing,
sorts (int/double), arithmetic (int vs real division, mod, casts), vassume,
if/while/for/break/continue/return, infeasible-path pruning, C truthiness
(`if (x % 2)`), `vassert` (per-path z3 check with counterexample models),
`unknown()`/`nondet()` as fresh symbolic values, C-accurate `/` and `%` on
negatives (truncation toward zero), side effects in conditions
(`while (i++ < n)`), the ternary operator, 1-D arrays (z3 arrays: `{…}`
inits, aliasing, `int a[]` params), structs by value (nested fields,
typedefs, `q = p` copies, array fields), auto safety checks
(`check_safety=True`: division-by-zero + array bounds with counterexample
inputs), k-induction (`prove_inductive`: unbounded loop-invariant proofs,
base/step violations with cex), replay harnesses (`gen_test_harness`:
compilable C driver calling mainQ once per path; gcc-verified), state
merging (`merge_states=True`: if/else diamonds → one If-valued state,
16→1 paths on the diamond program), user-defined function inlining
(branching/loop helpers, recursion cap, caller-local shielding), globals
(zero-init, helper writes persist), signed-overflow checking
(`check_overflow=True`), houdini invariant pruning + C-syntax invariant
parsing (`parse_c_expr`, CLI `--prove`/`--check-inv`/`--houdini`),
k-induction with `k > 1` (2-inductive alternation invariants), termination
proofs via ranking functions (`prove_termination`, CLI `--terminates` +
`--assume`), witness traces on violations (branch decisions with source
coords, CLI "witness trace:"), `#define` preprocessing via cpp, modeled calls (`isqrt`), post-run APIs
(`gen_inputs`, `unreached_locs`, `check_inv`), the MAX_STATES cap, output
contract, and run-to-run determinism.

Every engine feature also has a standalone, self-checking C program in
`tests/symex_progs/` (verified via `vassert`; `*_bad.c` programs must
produce a violation + counterexample). pytest runs them all, and they
double as CLI demos: `python -m data.symex_c tests/symex_progs/arrays.c
--depth 8`. **When adding an engine feature, add a program there.**

`symex_c.py` also runs standalone:

```sh
python -m data.symex_c prog.c --depth 4    # from src/; prints symstates,
                                           # unreached-vtrace warnings, safety
                                           # findings (on by default), and
                                           # vassert verdicts w/ counterexamples
python -m data.symex_c prog.c --gen-tests  # + one concrete input per path
python -m data.symex_c prog.c --gen-harness replay.c   # C replay driver
python -m data.symex_c prog.c --merge      # merge if/else diamonds
python -m data.symex_c prog.c --no-safety  # disable auto safety checks
python -m data.symex_c prog.c --check-overflow          # 32-bit int range
python -m data.symex_c prog.c --prove "q*y + r == x"    # unbounded induction
python -m data.symex_c prog.c --check-inv vtrace1 "r >= 0"  # bounded check
python -m data.symex_c prog.c --houdini "q >= 0" --houdini "r >= 0"
                                           # largest inductive subset
```

```sh
pytest tests/test_symex_c.py           # ~0.3s
```

`bench_symex.py` benchmarks `CSymEx` alone (no DIG) over the C benchmarks:
per (program, depth) it reports wall time, record count, and a signature hash
used for determinism and baseline diffs. Each run is a fresh subprocess with
a timeout. Baseline lives in `tests/symex_baseline.json`.

```sh
python tests/bench_symex.py                         # nla, depths 2,3,4
python tests/bench_symex.py --programs cohendiv --depths 2 3 4 5
python tests/bench_symex.py --repeat 3              # determinism check
python tests/bench_symex.py --save                  # record baseline
python tests/bench_symex.py --check                 # diff vs baseline
                                                    # (nonzero exit on change)
```

## Benchmark regression tests (full DIG, slow)

Runs DIG on every C benchmark (`benchmark/c/{nla,complexity,hola}`) and checks
the result against a committed golden signature, so refactors can be validated
quickly instead of by hand.

What's checked per program (see `test_benchmarks.py`):
- **status** — `ok` / `timeout` / `fail` must match the golden (a solving
  program must not start hanging/crashing; a known timeout/fail stays known).
- **equalities** — every recorded eqt must still be found, sign-normalized so
  `p==0` and `-p==0` are equal. Eqts are the most deterministic + meaningful
  invariants, so they drive correctness.
- **count floor** — total invariant count must not drop below the recorded min
  (a loose guard on the wobblier types: congruences/octs).

The eqt check retries a couple times to tolerate residual trace
nondeterminism (a few programs sit at the edge of trace sufficiency).

## Running

```sh
pip install pytest            # plus DIG's deps (see pyproject.toml)
pytest tests/                 # full suite (slow: runs DIG on every program)
pytest tests/ -k nla          # one suite
pytest tests/ -k cohendiv     # one program
pytest tests/ --dig-timeout 300
```

## Updating the golden

After an intentional behavior change, regenerate (runs each program a few
times; eqts kept are those found in *every* run, so flaky ones aren't baked in):

```sh
python tests/gen_golden.py 3                 # 3 runs each
python tests/gen_golden.py 2 --only nla      # just one suite
```

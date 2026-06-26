# Benchmark regression tests

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

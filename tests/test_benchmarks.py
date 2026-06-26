"""
Regression tests over the C benchmarks (nla, complexity, hola).

Each program is checked against a committed golden signature (tests/golden.json,
produced by gen_golden.py):

  - status must match (so a program that should solve doesn't start to hang/
    crash, and a known timeout/fail stays known rather than silently breaking
    the suite);
  - every golden equality must still be found (sign-normalized);
  - total invariant count must not drop below the recorded floor.

The eqt check retries a couple times before failing, to tolerate the residual
trace nondeterminism (a few programs sit at the edge of trace sufficiency).

Run:    pytest tests/                  (full; slow — runs DIG on every program)
        pytest tests/ -k nla           (one suite)
        pytest tests/ -k cohendiv      (one program)
Regenerate golden after an intentional behavior change:
        python tests/gen_golden.py
"""
import json
from pathlib import Path

import pytest

from dig_harness import programs, prog_id, run_dig

_GOLDEN_PATH = Path(__file__).parent / "golden.json"
_GOLDEN = json.loads(_GOLDEN_PATH.read_text()) if _GOLDEN_PATH.exists() else {}


@pytest.mark.parametrize("cfile", programs(), ids=prog_id)
def test_benchmark(cfile, request):
    pid = prog_id(cfile)
    gold = _GOLDEN.get(pid)
    if gold is None:
        pytest.skip(f"no golden entry for {pid} (run gen_golden.py)")

    timeout = request.config.getoption("--dig-timeout")
    res = run_dig(cfile, timeout=timeout)

    assert res["status"] == gold["status"], (
        f"{pid}: status {res['status']!r}, expected {gold['status']!r}")

    if gold["status"] != "ok":
        return  # known timeout/fail reproduced — nothing more to check

    # every recorded equality must still be found; retry for flaky trace cases
    expected = set(gold["eqts"])
    missing = expected - set(res["eqts"])
    for _ in range(2):
        if not missing:
            break
        res = run_dig(cfile, timeout=timeout)
        missing = expected - set(res["eqts"])
    assert not missing, f"{pid}: missing equalities {sorted(missing)}"

    assert res["n_invs"] >= gold["min_invs"], (
        f"{pid}: {res['n_invs']} invs < floor {gold['min_invs']}")

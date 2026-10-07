"""Bound search must certify integer maxima and decline inconclusive queries."""
import sys
from pathlib import Path

import pytest
import z3

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "src"))
from data.symstates import SymStates


@pytest.mark.parametrize("maximum", [-50, -7, 0, 7, 50])
def test_certified_integer_maximum_preserves_solver_scope(maximum):
    x = z3.Int("x")
    solver = z3.Solver()
    solver.add(x <= maximum)
    before = list(solver.assertions())
    value, status = SymStates._solve_max(solver, x, 50)
    assert value == maximum
    assert status == z3.sat
    assert list(solver.assertions()) == before


@pytest.mark.parametrize("kind", ["unbounded", "over_cap", "below_cap", "infeasible", "fractional"])
def test_unreportable_maxima_are_omitted(kind):
    x = z3.Real("x") if kind == "fractional" else z3.Int("x")
    solver = z3.Solver()
    if kind == "over_cap": solver.add(x <= 51)
    if kind == "below_cap": solver.add(x <= -51)
    if kind == "infeasible": solver.add(z3.BoolVal(False))
    if kind == "fractional": solver.add(x <= z3.RealVal("1/2"))
    value, _ = SymStates._solve_max(solver, x, 50)
    assert value is None

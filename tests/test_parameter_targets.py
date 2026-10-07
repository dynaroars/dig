"""Exact output implication must distinguish proof from numerical fitting."""
from pathlib import Path
from types import SimpleNamespace
import sys

import sympy

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "src"), str(ROOT / "benchmark")]

from data.traces import DTraces, Trace
from infer.eqt import Eqt
from parameter_oracle import check_targets, polynomial_consequence


def test_freire_cubic_is_exact_consequence_of_two_output_equations():
    a, r, s, x = sympy.symbols("a r s x")
    invs = [Eqt(sympy.Eq(12*r**2-4*s+1, 0)),
            Eqt(sympy.Eq(-24*a+8*r*s+16*r-12*s+24*x-3, 0))]
    assert polynomial_consequence(invs, "4*r**3-6*r**2+3*r+4*x-4*a-1 == 0")
    assert not polynomial_consequence(invs, "4*r**3-6*r**2+3*r+4*x-4*a == 0")


def test_approximate_coefficients_do_not_supply_exact_certificate():
    x = sympy.Symbol("x")
    invs = [Eqt(sympy.Eq(x-sympy.Float("0.1"), 0))]
    assert not polynomial_consequence(invs, "10*x == 1")


def test_quartic_target_can_require_cancellation_between_generators():
    M, N, P, t = sympy.symbols("M N P tCtr")
    factor = (M+P-t+1)*(M*N-M*P+N-t)
    invs = [Eqt(sympy.Eq(sympy.expand(N*factor), 0)),
            Eqt(sympy.Eq(sympy.expand((131*M+137*P+137*t-41046)*factor), 0)),
            Eqt(sympy.Eq(sympy.expand((131*M+137*N+137*P-41046)*factor), 0))]
    target = "tCtr*(tCtr-M-P-1)*(tCtr-(M+1)*N+M*P) == 0"
    assert polynomial_consequence(invs, target)
    assert polynomial_consequence(list(reversed(invs)), target)
    assert not polynomial_consequence(invs, target.replace("== 0", "== 1"))


def test_inconsistent_output_cannot_recover_target(tmp_path):
    source = tmp_path / "example.c"
    source.write_text("void vtrace(int x) {} void mainQ(int x) {}")
    x = sympy.Symbol("x")
    traces = DTraces()
    traces.add("vtrace", Trace(("x",), (sympy.Integer(0),)))
    result = SimpleNamespace(filename=source,
                             dinvs={"vtrace": [Eqt(sympy.Eq(x, 0)),
                                               Eqt(sympy.Eq(x-1, 0))]},
                             dtraces=traces)
    checks = check_targets(result, [{"location": "vtrace", "expression": "x == 2"}])
    assert checks[0]["outcome"] == "inconsistent"

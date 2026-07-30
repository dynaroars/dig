"""
Unit tests for the static equality engines: src/infer/recurrence.py
(solvable-loop recurrences) and src/infer/kapur.py (RC-Kapur bounded-degree
invariant ideal).

Each test writes a small C program to a tmp dir and runs an engine on it
directly (no full DIG run). The focus is the input-updating loop class
(a loop that reassigns one of its own inputs), where a variable's initial
value must get a symbol distinct from its loop-head value: aliasing them
used to crash both engines (sympy.Rational on a symbolic orbit coordinate;
ilcm on a single denominator) and lose the invariants.

Run:    pytest tests/test_recurrence.py         (fast-ish; z3 k-induction)
"""
from __future__ import annotations

import sys
from pathlib import Path

import sympy

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "src"))

from infer.recurrence import RecurrenceInfer, _clear_denoms  # noqa: E402
from infer.kapur import KapurInfer  # noqa: E402


# input-updating loop with NO polynomial invariant over its observed
# (current-value) variables: s relates only to n's *initial* value
SUMDOWN = """\
void vtrace1(int s, int n);
void mainQ(int n) {
  int s = 0;
  while (n > 0) {
    vtrace1(s, n);
    s = s + n;
    n = n - 1;
  }
}
void main(int argc, char **argv) {}
"""

# input-updating loop WITH invariants over current values (a == n, b == 2n):
# found only if n's initial value is treated as a parameter and eliminated
TRIPCOUNT = """\
void vtrace1(int a, int b, int n);
void mainQ(int n) {
  int a = n;
  int b = n + n;
  while (n < 100) {
    vtrace1(a, b, n);
    a = a + 1;
    b = b + 2;
    n = n + 1;
  }
}
void main(int argc, char **argv) {}
"""


def write(tmp_path: Path, src: str) -> Path:
    f = tmp_path / "prog.c"
    f.write_text(src)
    return f


def proved(results) -> set[sympy.Expr]:
    """Sign-normalized proved polynomials from an engine's (poly, status)."""
    out = set()
    for p, status in results:
        if status != "valid":
            continue
        p = sympy.expand(p)
        terms = p.as_ordered_terms()
        if terms and terms[0].as_coeff_Mul()[0] < 0:
            p = -p
        out.add(p)
    return out


def test_clear_denoms_single_coeff():
    x = sympy.Symbol("x")
    assert _clear_denoms(x / 2, [x]) == x       # one denominator: ilcm arity
    assert _clear_denoms(x, [x]) == x
    assert _clear_denoms(x / 2 + sympy.Rational(1, 3), [x]) == 3 * x + 2


def test_recurrence_input_updating_loop_declines(tmp_path):
    _closed, results = RecurrenceInfer(write(tmp_path, SUMDOWN)).gen(0)
    assert proved(results) == set()             # no invariant over (s, n)


def test_recurrence_input_updating_loop_solves(tmp_path):
    _closed, results = RecurrenceInfer(write(tmp_path, TRIPCOUNT)).gen(0)
    a, b, n = sympy.symbols("a b n")
    assert proved(results) == {a - n, b - 2 * n}


def test_kapur_input_updating_loop_declines(tmp_path):
    results = KapurInfer(write(tmp_path, SUMDOWN)).gen(0, deg=2)
    assert proved(results) == set()


def test_kapur_input_updating_loop_solves(tmp_path):
    results = KapurInfer(write(tmp_path, TRIPCOUNT)).gen(0, deg=2)
    a, b, n = sympy.symbols("a b n")
    # the ideal's Groebner basis: same variety as {a - n, b - 2n}
    assert proved(results) == {b - 2 * n, 2 * a - b}

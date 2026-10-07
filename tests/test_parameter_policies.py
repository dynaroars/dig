"""Regression cases for the defects exposed by parameter analysis."""
import shlex
import sys
from pathlib import Path
from types import SimpleNamespace

import pytest
import sympy

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "src"))
import settings
from data.prog import Prog
from data.traces import Trace
from helpers.miscs import Miscs
from infer.eqt import Eqt


@pytest.mark.parametrize("limit", [1, 2, 10, 19, 20, 300])
def test_positive_input_limits_have_only_sampleable_ranges(monkeypatch, limit):
    monkeypatch.setattr(settings, "INP_MAX_V", limit)
    ranges = list(Prog._get_inp_ranges(2))
    assert ranges
    assert all(0 <= low < high <= limit for pair in ranges for low, high in pair)
    assert len(ranges) == len(set(ranges))


def test_large_valid_trace_refutes_equality():
    x = sympy.Symbol("x")
    trace = Trace(("x",), (sympy.Integer(10**12),))
    assert not Eqt(sympy.Eq(x, 0)).test_single_trace(trace)
    assert Eqt(sympy.Eq(x - 10**12, 0)).test_single_trace(trace)


def test_benchmark_options_roundtrip_degree_paths_and_terms():
    args = SimpleNamespace(**{k: False for k, *_ in settings._BOOL_FLAGS},
                           **{k: None for k, *_ in settings._STR_FLAGS},
                           **{k: None for k, *_ in settings._INT_FLAGS},
                           types="eqt,ieq", uterms="x**2 ; x*y+4", se_maxdepth=4,
                           tmpdir="/tmp/with spaces", log_level=2, maxdeg=3)
    args.writevtraces = "/tmp/traces with spaces.csv"
    args.readsstates = "/tmp/states with spaces.json"
    args.nomp = True
    argv = shlex.split(settings.setup(None, args))
    assert argv[argv.index("-maxdeg") + 1] == "3"
    assert argv[argv.index("-uterms") + 1] == args.uterms
    assert argv[argv.index("-tmpdir") + 1] == args.tmpdir
    assert argv[argv.index("-readsstates") + 1] == args.readsstates
    assert argv[argv.index("-writevtraces") + 1] == args.writevtraces
    assert "-nomp" in argv


@pytest.mark.parametrize("rows", [
    [[1, sympy.Rational(1, 2)], [1, sympy.Rational(1, 3)]],
    [[1, 10**9], [2, 2*10**9]],
    [[1, 10**400], [2, 2*10**400]],
    [[1, 1_000_003], [0, 1_000_003]],
    [[1_000_003, 0], [0, 1_000_003]],
    [[0, 0], [0, 0]],
    [[sympy.Rational(1, 1_000_003), 1]],
])
def test_certified_rank_and_nullspace_keep_exact_relations(rows):
    coefficients = sympy.symbols("c0:2")
    expressions = [sum(c*v for c, v in zip(coefficients, row)) for row in rows]
    matrix = sympy.Matrix(rows)
    vectors = Miscs._null_space_fast(expressions, list(coefficients))
    assert Miscs.coef_matrix_rank(expressions, list(coefficients)) == matrix.rank()
    assert len(vectors) == 2 - matrix.rank()
    assert all(matrix * vector == sympy.zeros(len(rows), 1) for vector in vectors)


def test_source_templates_find_square_bound_without_global_three_term_search():
    from infer.source_hints import polynomial_terms
    a, n, t, s = sympy.symbols("a n t s")
    source = Path(__file__).resolve().parent.parent / "benchmark/c/nla/sqrt1.c"
    hints = polynomial_terms(source, (a, n, t, s), 200)
    assert s - t - n in hints
    assert len(hints) < 10


def test_nested_solver_policies_restore_after_exception():
    from helpers.z3utils import Z3
    outer = settings.solver_policy("optimization")
    inner = settings.solver_policy("simplification")
    assert Z3._policy.get() is None
    with Z3.use_policy(outer):
        with pytest.raises(RuntimeError):
            with Z3.use_policy(inner):
                assert Z3._policy.get() == inner
                raise RuntimeError("stop")
        assert Z3._policy.get() == outer
    assert Z3._policy.get() is None


def test_large_coefficient_candidates_are_preserved():
    x, y = sympy.symbols("x y")
    expression = x - 1_000_000_007*y
    assert Miscs.refine([expression], do_reduce=False) == [expression]


def test_bound_cap_resolves_after_import(monkeypatch):
    from infer.oct import Infer
    monkeypatch.setattr(settings, "IUPPER", 123)
    assert Infer.bound_cap() == 123


def test_cached_linear_rows_match_general_coefficient_extraction():
    c0, c1, x = sympy.symbols("c0 c1 x")
    expressions = (3*c0 + sympy.Rational(1, 7)*c1, c0*x + c1, c0, sympy.Integer(0))
    expected = tuple(tuple(expr.coeff(c) for c in (c0, c1)) for expr in expressions)
    assert Miscs._coefficient_rows(expressions, (c0, c1)) == expected


def test_explicit_template_policy_keeps_octagonal_search(monkeypatch):
    from data.prog import DSymbs, Symbs, Symb
    from infer.oct import Infer
    names = ("a", "n", "t", "s")
    declarations = DSymbs({"vtrace1": Symbs([Symb(name, "I") for name in names])})
    source = Path(__file__).resolve().parent.parent / "benchmark/c/nla/sqrt1.c"
    prog = Prog("unused", Symbs([Symb("n", "I")]), declarations, source=source)
    monkeypatch.setattr(settings, "SOURCE_TEMPLATES", False)
    expressions = {term.term for term in Infer(None, prog).get_terms(sympy.symbols("a n t s"))}
    assert sympy.Symbol("s") - sympy.Symbol("t") - sympy.Symbol("n") not in expressions

"""Concrete counterexamples must refine fitting before bounded acceptance."""
import sympy
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "src"))

from data.traces import Trace, Traces
from infer.eqt import Infer
from data.prog import Src, Symbs, Symb
from data.traces import DTraces
from infer.inv import DInvs
from infer.eqt import Eqt
from infer.mp import MMP, Term
from infer.oct import Oct
import settings
from helpers.miscs import Miscs
from types import SimpleNamespace


def test_early_state_equalities_do_not_hide_later_relation():
    x, y = sympy.symbols("x y")
    c0, c1, c2 = sympy.symbols("c0 c1 c2")
    inference = Infer.__new__(Infer)
    # Simulate a shallow symbolic exploration containing only the initial
    # state: it cannot refute x=0 or y=0, unlike the collected concrete traces.
    inference.check = lambda invs, inps: ({}, invs)
    traces = Traces([
        Trace(("x", "y"), (sympy.Integer(n), sympy.Integer(n)))
        for n in (0, 1, 2)
    ])
    result = inference._infer("vtrace", [1, x, y], [c0, c1, c2], {c0}, traces)
    assert result
    polynomials = [inv.inv.lhs for inv in result]
    assert all(p.xreplace(trace.mydict) == 0 for p in polynomials for trace in traces)
    assert sympy.groebner(polynomials, x, y).reduce(x-y)[1] == 0


def test_void_input_signature_is_supported():
    inputs, declarations, name = Src.parse_type_info("mainQ; \nvtrace; I c")
    assert inputs.names == ()
    assert declarations["vtrace"].names == ("c",)
    assert name == "mainQ"


def test_parallel_trace_filter_preserves_only_valid_invariants(monkeypatch):
    x, y = sympy.symbols("x y")
    good = Eqt(sympy.Eq(x-y, 0))
    bad = Eqt(sympy.Eq(x+y, 0))
    maximum = MMP(Term.mk((x, y), y))
    traces = DTraces()
    for n in (0, 1, 2):
        traces.add("first", Trace(("x", "y"), (sympy.Integer(n), sympy.Integer(n))))
        traces.add("second", Trace(("x", "y"), (sympy.Integer(n), sympy.Integer(n))))
    invs = DInvs()
    for loc in traces:
        for inv in (good, bad, maximum):
            invs.add(loc, inv)
    for parallel in (False, True):
        monkeypatch.setattr(settings, "DO_MP", parallel)
        result = invs.test(traces)
        assert set(result) == set(traces)
        assert all(set(result[loc]) == {good, maximum} for loc in traces)


def test_minmax_evaluation_reuses_compiled_expression():
    x, y = sympy.symbols("x y")
    inv = MMP(Term.mk((x, y), y))
    Term._compile_lambda.cache_clear()
    for n in (0, 1, 2):
        assert inv.test_single_trace(Trace(("x", "y"), (sympy.Integer(n), sympy.Integer(n))))
    info = Term._compile_lambda.cache_info()
    assert info.misses == 1
    assert info.hits == 2


def test_explicit_degree_search_keeps_independent_cubic_relation(monkeypatch):
    x, y, z = sympy.symbols("x y z")
    declarations = {"vtrace": Symbs([Symb(n, "I") for n in ("x", "y", "z")])}
    inference = Infer.__new__(Infer)
    inference.inv_decls = declarations
    inference.inp_decls = Symbs([Symb("x", "I")])
    inference.prog = SimpleNamespace(locs=["vtrace"])
    inference.check = lambda invs, inps: ({}, invs)
    traces = Traces([Trace(("x", "y", "z"),
                          tuple(map(sympy.Integer, (n, 0, n**3)))) for n in range(20)])
    searched = []

    def initial(loc, degree, dtraces, inps, rate):
        searched.append(degree)
        dtraces[loc] = traces
        terms, coefficients, _ = Miscs.init_terms(("x", "y", "z"), degree, rate)
        template = sum(t*c for t, c in zip(terms, coefficients))
        return terms, coefficients, traces.instantiate(template, None)

    inference._get_init_traces = initial
    monkeypatch.setattr(settings, "DO_MP", False)
    invs, _ = inference.gen(3, complete=True)
    assert searched == [2, 3]
    basis = sympy.groebner([p.inv.lhs for p in invs["vtrace"]], x, y, z)
    assert basis.reduce(y)[1] == 0
    assert basis.reduce(z-x**3)[1] == 0


def test_degree_hint_respects_explicit_linear_ceiling(monkeypatch):
    x, y = sympy.symbols("x y")
    inference = Infer.__new__(Infer)
    inference.inv_decls = {"vtrace": Symbs([Symb("x", "I"), Symb("y", "I")])}
    inference.inp_decls = Symbs([Symb("x", "I")])
    inference.prog = SimpleNamespace(locs=["vtrace"])
    inference.check = lambda invs, inps: ({}, invs)
    traces = Traces([Trace(("x", "y"), tuple(map(sympy.Integer, (n, 2*n))))
                     for n in range(5)])
    searched = []

    def initial(loc, degree, dtraces, inps, rate):
        searched.append(degree)
        dtraces[loc] = traces
        terms, coefficients, _ = Miscs.init_terms(("x", "y"), degree, rate)
        template = sum(t*c for t, c in zip(terms, coefficients))
        return terms, coefficients, traces.instantiate(template, None)

    inference._get_init_traces = initial
    monkeypatch.setattr(settings, "DO_MP", False)
    invs, _ = inference.gen(1, deg_hints={"vtrace": 0}, complete=True)
    assert searched == [1]
    assert invs["vtrace"]


def test_bound_refuted_by_later_traces_is_weakened_instead_of_lost():
    y = sympy.Symbol("y")
    inv = Oct(sympy.Le(-y, -13), stat=Oct.PROVED)
    traces = Traces([Trace(("y",), (sympy.Integer(n),)) for n in (11, 13, 20)])
    weaker = inv.test_or_weaken(traces)
    assert weaker is not None
    assert weaker.inv == sympy.Le(-y, -11)
    assert weaker.stat == inv.stat
    assert weaker.test(traces)


def test_large_intermediate_coefficients_do_not_stop_counterexample_refinement():
    m, t = sympy.symbols("m t")
    terms, coefficients, _ = Miscs.init_terms(("m", "t"), 2, 1.5)
    template = sum(p*c for p, c in zip(terms, coefficients))
    initial = Traces([Trace(("m", "t"), tuple(map(sympy.Integer, (n, n+100))))
                      for n in range(9)])
    inference = Infer.__new__(Infer)
    inference.inv_decls = {"post": Symbs([Symb("m", "I"), Symb("t", "I")])}

    def check(invs, inps):
        counterexamples = {}
        for inv in invs["post"]:
            for n in range(-3, 9):
                values = {m: n, t: max(n, 0)+100}
                if inv.inv.lhs.xreplace(values) != 0:
                    inv.stat = inv.DISPROVED
                    counterexamples[str(inv)] = [{str(k): v for k, v in values.items()}]
                    break
            else:
                inv.stat = inv.PROVED
        return ({"post": counterexamples} if counterexamples else {}), invs

    inference.check = check
    result = inference._infer("post", terms, coefficients,
                              initial.instantiate(template, None), initial)
    assert result
    target = m*t-t**2-100*m+200*t-10000
    assert sympy.groebner([inv.inv.lhs for inv in result], m, t).reduce(target)[1] == 0

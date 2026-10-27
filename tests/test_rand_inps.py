"""Random input generation must respect the program's vassume precondition.

Each test compiles a tiny C program and drives Prog.gen_rand_inps directly, so
the generator is checked without running the whole inference pipeline.
"""
import itertools
import logging
import random
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "src"))

from data.prog import C, Prog
from data.traces import Inp
import settings


_builds = itertools.count()


@pytest.fixture(autouse=True)
def stable_execution(monkeypatch):
    """These tests assert on exact input sets, and a probe that looks invalid
    makes its sampling window look dead. Keep execution out of the way: no
    forking, and a run budget transient load cannot exhaust."""
    monkeypatch.setattr(settings, "DO_MP", False)
    monkeypatch.setattr(settings.C, "RUN_TIMEOUT", 20)


def build(tmp_path, body, inputs="int x", with_source=True, name="inp"):
    """Compile `body` as mainQ and return its Prog.

    with_source=False drops the source path, the way llm_infer builds a Prog:
    no precondition is then available and generation must behave as it always
    did.
    """
    names = [p.split()[-1] for p in inputs.split(",")]
    args = ", ".join(f"atoi(argv[{i + 1}])" for i in range(len(names)))
    source = tmp_path / f"{name}.c"
    source.write_text(f"""
        #include <stdio.h>
        #include <stdlib.h>
        void vassume(int b){{}}
        void vtrace1({inputs}, int i, int s){{}}
        int mainQ({inputs}){{
            {body}
            int i = 0;
            int s = 0;
            while (1) {{
                vtrace1({', '.join(names)}, i, s);
                if (!(i < 3)) break;
                s = s + {names[0]};
                i = i + 1;
            }}
            return s;
        }}
        int main(int argc, char **argv){{ mainQ({args}); return 0; }}
    """)
    work = tmp_path / f"work_{name}_{next(_builds)}"
    work.mkdir()
    compiled = C(source, work)
    return Prog(str(compiled.traceexe), compiled.inp_decls,
                compiled.inv_decls, source=source if with_source else None)


def gen(prog, n_needed, seed=1):
    random.seed(seed)
    return prog.gen_rand_inps(n_needed=n_needed)


# ───────────────────────────────── the fix ──────────────────────────────────

def test_narrow_precondition_delivers_feasible_inputs(tmp_path):
    """A window far narrower than the sampling ranges used to yield nothing."""
    for seed in (1, 2, 3):
        # a fresh Prog per seed: within one Prog, a later call deliberately
        # returns inputs the earlier ones did not (see the test below)
        prog = build(tmp_path, "vassume(x >= 100); vassume(x <= 105);",
                     name=f"narrow{seed}")
        inps = gen(prog, 60, seed=seed)
        assert inps, f"no inputs generated for seed {seed}"
        assert all(100 <= x <= 105 for (x,) in inps), inps
        # the admissible set has exactly 6 elements, all of them reachable
        assert len(inps) == 6, inps


def test_violating_candidates_are_never_executed(tmp_path, monkeypatch):
    """Inadmissible candidates must not cost a process execution."""
    prog = build(tmp_path, "vassume(x >= 0); vassume(x <= 10);")
    executed = []
    original = Prog._get_traces
    monkeypatch.setattr(Prog, "_get_traces",
                        lambda self, inp: executed.append(inp.vs) or original(self, inp))

    inps = gen(prog, 30)

    assert all(0 <= x <= 10 for (x,) in inps), inps
    assert executed, "range validation should still probe"
    assert all(0 <= x <= 10 for (x,) in executed), executed


def test_solver_sampled_inputs_are_diverse(tmp_path):
    """Diversity matters: equality fitting needs distinct observations, and
    z3's first model alone would hand back one value over and over."""
    prog = build(tmp_path, "vassume(x >= 100); vassume(x <= 105);")
    inps = gen(prog, 60)
    assert len({x for (x,) in inps}) == 6, inps


def test_later_calls_return_new_solver_inputs(tmp_path):
    """eqt asks repeatedly; the solver must not keep returning the same model."""
    prog = build(tmp_path, "vassume(x >= 100); vassume(x <= 105);")
    random.seed(1)
    first = prog.gen_rand_inps(n_needed=3)
    second = prog.gen_rand_inps(n_needed=3)
    assert first and second
    assert second - first, (first, second)


def test_generation_is_deterministic_per_seed(tmp_path):
    def run():
        prog = build(tmp_path, "vassume(x >= 100); vassume(x <= 105);",
                     name="det")
        return gen(prog, 20, seed=5)

    assert run() == run()


# ──────────────────────────── backward compatibility ────────────────────────

def test_no_assumptions_leaves_generation_unchanged(tmp_path):
    """A program without vassume must follow the original path exactly: the
    same inputs a Prog with no source at all (hence no precondition) gets."""
    with_src = build(tmp_path, "", name="plain_src")
    without = build(tmp_path, "", with_source=False, name="plain_nosrc")

    assert with_src.precondition == (None, True)
    assert without.precondition == (None, False)
    for seed in (1, 2, 3, 4, 5):
        assert gen(with_src, 60, seed=seed) == gen(without, 60, seed=seed)


def test_unreadable_source_falls_back_to_plain_generation(tmp_path):
    prog = build(tmp_path, "vassume(x >= 100);", name="gone")
    (tmp_path / "gone.c").unlink()
    assert prog.precondition == (None, False)
    assert gen(prog, 10)


# ───────────────────────── never assume satisfaction ────────────────────────

def test_undecidable_condition_is_not_rejected(tmp_path):
    """Three-valued check: a candidate the constraint cannot decide (here a
    division by zero, which z3 leaves uninterpreted) must be kept, not
    rejected and not counted as satisfied."""
    prog = build(tmp_path, "vassume(100 / x > 2);")
    assert prog._admits((10,)) is True     # 100/10 == 10 > 2
    assert prog._admits((60,)) is False    # 100/60 == 1, C truncation
    assert prog._admits((0,)) is None      # undecidable, so never rejected


def test_unsupported_condition_is_not_used(tmp_path):
    """A vassume this evaluator cannot translate is dropped, the precondition
    is marked incomplete, and generation still runs."""
    source = tmp_path / "helper.c"
    source.write_text("""
        #include <stdio.h>
        #include <stdlib.h>
        void vassume(int b){}
        void vtrace1(int x){}
        int helper(int x){ return x; }
        int mainQ(int x){
            vassume(helper(x) > 0);
            vtrace1(x);
            return x;
        }
        int main(int argc, char **argv){ mainQ(atoi(argv[1])); return 0; }
    """)
    work = tmp_path / "work_helper"
    work.mkdir()
    compiled = C(source, work)
    prog = Prog(str(compiled.traceexe), compiled.inp_decls,
                compiled.inv_decls, source=source)

    constraint, complete = prog.precondition
    assert constraint is None and complete is False
    assert gen(prog, 10)                   # unchanged generation


def test_partial_precondition_only_rules_inputs_out(tmp_path):
    """With one usable and one unusable condition, the usable one filters and
    the unusable one is ignored -- candidates it would reject are still kept
    and left to the actual execution."""
    source = tmp_path / "partial.c"
    source.write_text("""
        #include <stdio.h>
        #include <stdlib.h>
        void vassume(int b){}
        void vtrace1(int x){}
        int g;
        int mainQ(int x){
            vassume(x >= 10);
            vassume(g == 0);
            vtrace1(x);
            return x;
        }
        int main(int argc, char **argv){ mainQ(atoi(argv[1])); return 0; }
    """)
    work = tmp_path / "work_partial"
    work.mkdir()
    compiled = C(source, work)
    prog = Prog(str(compiled.traceexe), compiled.inp_decls,
                compiled.inv_decls, source=source)

    constraint, complete = prog.precondition
    assert constraint is not None and complete is False
    assert prog._admits((3,)) is False     # decided by the usable condition
    assert prog._admits((42,)) is True     # the dropped one is not consulted
    assert all(x >= 10 for (x,) in gen(prog, 20))


def test_nested_assumption_is_ignored(tmp_path):
    """A vassume inside a loop is not an entry precondition."""
    source = tmp_path / "nested.c"
    source.write_text("""
        #include <stdio.h>
        #include <stdlib.h>
        void vassume(int b){}
        void vtrace1(int x, int i){}
        int mainQ(int x){
            int i = 0;
            while (i < 3) { vassume(x > 100); vtrace1(x, i); i = i + 1; }
            return i;
        }
        int main(int argc, char **argv){ mainQ(atoi(argv[1])); return 0; }
    """)
    work = tmp_path / "work_nested"
    work.mkdir()
    compiled = C(source, work)
    prog = Prog(str(compiled.traceexe), compiled.inp_decls,
                compiled.inv_decls, source=source)
    assert prog.precondition == (None, False)


# ──────────────────────── bounded, distinguishable outcomes ─────────────────

def test_unsatisfiable_assumptions_report_and_return_empty(tmp_path, caplog):
    """Unsatisfiability is established by a dedicated solver check, so it can
    be reported as such -- and nothing is executed."""
    prog = build(tmp_path, "vassume(x > 5); vassume(x < 3);")
    with caplog.at_level(logging.DEBUG, logger="data.prog"):
        inps = gen(prog, 20)
    assert inps == set()
    assert any("unsatisfiable" in r.message for r in caplog.records), caplog.text
    assert not prog.execution_outcomes       # no program run at all


def test_exhausted_domain_delivers_all_of_it_and_reports(tmp_path, caplog):
    """Asking for more inputs than exist must deliver every admissible one and
    say so, rather than silently returning a handful."""
    prog = build(tmp_path, "vassume(x >= 0); vassume(x <= 3);")
    with caplog.at_level(logging.DEBUG, logger="data.prog"):
        inps = gen(prog, 50)
    assert {x for (x,) in inps} == {0, 1, 2, 3}, inps
    assert any("no further input satisfies" in r.message and "of 50" in r.message
               for r in caplog.records), caplog.text


def test_assumptions_outside_inp_max_v_are_reported(tmp_path, caplog, monkeypatch):
    """Satisfiable, but not within -inpMaxV: the generator looks beyond the
    range and says that it did."""
    monkeypatch.setattr(settings, "INP_MAX_V", 50)
    prog = build(tmp_path, "vassume(x >= 1000); vassume(x <= 1010);")
    with caplog.at_level(logging.DEBUG, logger="data.prog"):
        inps = gen(prog, 5)
    assert inps and all(1000 <= x <= 1010 for (x,) in inps), inps
    assert any("inpMaxV" in r.message for r in caplog.records), caplog.text


def test_solver_phase_respects_its_call_cap(tmp_path, monkeypatch):
    """The solver phase is hard-bounded; it cannot spin on a hard constraint."""
    prog = build(tmp_path, "vassume(x >= 100); vassume(x <= 105);")
    calls = []
    original = Prog._solver_sample

    def counted(self, k, found, constraint):
        out, status, n = original(self, k, found, constraint)
        calls.append((k, status, n))
        return out, status, n

    monkeypatch.setattr(Prog, "_solver_sample", counted)
    gen(prog, 60)
    assert calls, "the solver phase should have run"
    for k, _, n in calls:
        assert n <= 2 * k + settings.INP_SOLVER_CALL_SLACK, (k, n)


def test_unknown_solver_result_is_not_read_as_unsatisfiable(tmp_path, monkeypatch):
    """An unknown verdict concludes nothing: no empty result claiming the
    assumptions are unsatisfiable, no exhaustion claim."""
    import z3
    from helpers.z3utils import Z3

    prog = build(tmp_path, "vassume(x >= 100); vassume(x <= 105);")
    original = Z3.create_solver

    class Unknown:
        def __init__(self, inner):
            self._inner = inner

        def add(self, *a):
            self._inner.add(*a)

        def check(self, *a):
            return z3.unknown

    monkeypatch.setattr(Z3, "create_solver",
                        classmethod(lambda cls, **kw: Unknown(original(**kw))))
    out, status, n_calls = prog._solver_sample(5, set(), prog.precondition[0])
    assert out == set() and status == "unknown" and n_calls == 1


# ─────────────── defects found in adversarial validation ────────────────────

def test_declaration_moving_an_input_is_not_an_entry_condition(tmp_path):
    """`int t = x++;` shifts the parameter, so `vassume(x >= 10)` after it says
    nothing about the input. Treating it as an entry condition rejected x=9,
    which the program actually accepts."""
    source = tmp_path / "moved.c"
    source.write_text("""
        #include <stdio.h>
        #include <stdlib.h>
        void vassume(int b){}
        void vtrace1(int x){}
        int mainQ(int x){
            int t = x++;
            vassume(x >= 10);
            vtrace1(t);
            return t;
        }
        int main(int argc, char **argv){ mainQ(atoi(argv[1])); return 0; }
    """)
    work = tmp_path / "work_moved"
    work.mkdir()
    compiled = C(source, work)
    prog = Prog(str(compiled.traceexe), compiled.inp_decls,
                compiled.inv_decls, source=source)

    assert prog.precondition == (None, False)
    # x=9 passes the real precondition (x+1 >= 10) and must not be rejected
    assert prog._admits((9,)) is None
    assert prog._get_traces(Inp(("x",), (9,)))


def test_free_input_is_not_reported_as_exhausted(tmp_path, caplog):
    """With one input constrained and one free, running out of values for the
    constrained one is not the admissible set running out: there are still
    inputs, and claiming otherwise both lies and stops generation early."""
    prog = build(tmp_path, "vassume(y >= 100); vassume(y <= 105);",
                 inputs="int x, int y", name="free")
    with caplog.at_level(logging.DEBUG, logger="data.prog"):
        inps = gen(prog, 60)
    assert len(inps) == 60, len(inps)
    assert all(100 <= y <= 105 for _, y in inps), inps
    assert len({x for x, _ in inps}) > 6, "the free input should still vary"
    assert not any("no further input" in r.message for r in caplog.records), caplog.text


def test_solver_sample_distinguishes_values_from_exhaustion(tmp_path):
    """The raw status must not say "exhausted" while free inputs remain."""
    prog = build(tmp_path, "vassume(y >= 100); vassume(y <= 105);",
                 inputs="int x, int y", name="freeraw")
    random.seed(1)
    _, status, _ = prog._solver_sample(60, set(), prog.precondition[0])
    assert status in ("ok", "budget"), status


def test_outside_inp_max_v_is_reported_even_when_exhausted(tmp_path, caplog):
    """Requesting more inputs than exist outside -inpMaxV must still say that
    the range was left behind, not report a limit the inputs do not obey."""
    prog = build(tmp_path, "vassume(x >= 1000); vassume(x <= 1010);", name="beyond")
    with caplog.at_level(logging.DEBUG, logger="data.prog"):
        inps = gen(prog, 60)
    assert inps and all(x >= 1000 for (x,) in inps), inps
    assert any("sampled beyond it" in r.message for r in caplog.records), caplog.text


def test_tiny_domain_keeps_returning_inputs_on_later_calls(tmp_path, monkeypatch):
    """Once a small admissible set has been handed out, a later call must not
    come back empty -- the caller would give up on random inputs entirely.
    The wide sampling range makes the windows miss the domain every time, so
    only the solver phase can supply it."""
    monkeypatch.setattr(settings, "INP_MAX_V", 100_000)
    prog = build(tmp_path, "vassume(x >= 100); vassume(x <= 102);", name="tiny3")
    random.seed(1)
    first = prog.gen_rand_inps(n_needed=5)
    assert {x for (x,) in first} == {100, 101, 102}, first
    for call in (2, 3):
        later = prog.gen_rand_inps(n_needed=5)
        assert later, f"call {call} returned nothing at all"
        assert all(100 <= x <= 102 for (x,) in later), later


def test_variable_free_constraint_is_reported_as_unsolvable(tmp_path, caplog):
    """A vassume mentioning no input cannot steer the search. The status for
    that existed already; the report must name it instead of blaming a budget
    the search never reached."""
    prog = build(tmp_path, "vassume(1);", name="const")
    constraint, complete = prog.precondition
    assert constraint is not None and complete is True
    random.seed(1)
    out, status, calls = prog._solver_sample(5, set(), constraint)
    assert out == set() and status == "unsolvable" and calls == 0

    with caplog.at_level(logging.DEBUG, logger="data.prog"):
        prog._log_rand_inps(60, 5, 0, 10, "unsolvable", 0, True)
    assert any("constrain no input" in r.message for r in caplog.records), caplog.text
    assert not any("search budget" in r.message for r in caplog.records), caplog.text


def test_precondition_does_not_shrink_the_probe_sample(tmp_path, monkeypatch):
    """Range validation probes one input per sampling window. When the
    precondition rules most windows out, the probes must be replaced from the
    surviving ones -- otherwise the bootstrap trace set shrinks with the
    number of admissible windows, which cost geo2 two true invariants and
    admitted a spurious congruence."""
    # of the four windows (0,30) (270,300) (0,15) (75,225) only the last is
    # admissible, but its feasible set is wide
    prog = build(tmp_path, "vassume(x >= 75); vassume(x <= 225);", name="shrink")
    n_windows = len(list(Prog._get_inp_ranges(1)))
    random.seed(1)
    prog.gen_rand_inps(n_needed=1)
    executed = {inp.vs for inp in prog.execution_outcomes}
    assert all(75 <= x <= 225 for (x,) in executed), executed
    assert len(executed) >= n_windows - 1, (
        f"probe sample collapsed to {len(executed)} of {n_windows} windows")

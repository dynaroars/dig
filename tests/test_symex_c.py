"""
Unit tests for src/data/symex_c.py (CSymEx), the Python symbolic execution
engine for simple C programs.

Each test writes a small self-contained C program to a tmp dir, runs CSymEx
on it, and checks the returned (loc, pc, slocal) z3 records. Semantic checks
are done with z3 itself (entailment / satisfiability), not string matching,
so they are robust to expression formatting.

Run:    pytest tests/test_symex_c.py            (fast; no DIG run)
        pytest tests/test_symex_c.py -k while
"""
from __future__ import annotations

import shutil
import subprocess
import sys
from pathlib import Path

import pytest
import z3

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "src"))

from data.symex_c import (  # noqa: E402
    CSymEx,
    _strip_comments,
    _strip_includes,
)

# ─────────────────────────────────────────────────────────── helpers ──

HEADER = """\
void vassume(int b){}
void vassert(int b){}
int unknown(void);
void vtrace1(int a, int b, int c, int d){}
void vtrace2(int a, int b, int c, int d){}
"""


def symex(tmp_path: Path, src: str, depth: int = 5,
          header: str = HEADER) -> tuple[CSymEx, list]:
    """Write `header + src` to a file, run CSymEx, return (engine, records)."""
    f = tmp_path / "prog.c"
    f.write_text(header + src)
    eng = CSymEx(f, depth)
    return eng, eng.run()


def implied(pc: z3.BoolRef, slocal: z3.BoolRef, claim: z3.BoolRef) -> bool:
    """True iff (pc ∧ slocal) ⇒ claim."""
    s = z3.Solver()
    s.add(pc, slocal, z3.Not(claim))
    return s.check() == z3.unsat


def satisfiable(*exprs: z3.BoolRef) -> bool:
    s = z3.Solver()
    s.add(*exprs)
    return s.check() == z3.sat


def assert_record_implies(rec, claim: z3.BoolRef):
    loc, pc, slocal = rec
    assert implied(pc, slocal, claim), (
        f"record at {loc} does not imply {claim}\n  pc: {pc}\n  slocal: {slocal}")


X = z3.Int
R = z3.Real


# ─────────────────────────────────────────────────────────── parsing ──

class TestParsing:
    def test_mainq_params_and_vtrace_signatures(self, tmp_path):
        eng, _ = symex(tmp_path, """
            int mainQ(int x, double y){
                vtrace1(x, x, x, x);
                return 0;
            }
        """)
        assert eng.mainq_params == [("x", "int"), ("y", "double")]
        assert eng.vtrace_params["vtrace1"] == ["a", "b", "c", "d"]
        assert eng.vtrace_params["vtrace2"] == ["a", "b", "c", "d"]

    def test_missing_mainq_raises(self, tmp_path):
        f = tmp_path / "nomain.c"
        f.write_text("int foo(int x){ return x; }")
        with pytest.raises(AssertionError, match="mainQ"):
            CSymEx(f, 3).run()

    def test_int_param_is_int_sort_double_param_is_real_sort(self, tmp_path):
        eng, _ = symex(tmp_path, "int mainQ(int i, double d){ return 0; }")
        st = eng._make_init_state()
        assert st.env["i"].sort() == z3.IntSort()
        assert st.env["d"].sort() == z3.RealSort()

    def test_comments_and_includes_are_stripped(self, tmp_path):
        src = """\
#include <stdio.h>
#include <stdlib.h>
// line comment with junk: #include @$%
/* block comment
   spanning lines */
""" + HEADER + """
            int mainQ(int x, int y){
                int t = 1; // trailing comment
                vtrace1(t, x, y, t);
                return 0;
            }
        """
        f = tmp_path / "prog.c"
        f.write_text(src)
        _, res = CSymEx(f, 3).run(), None
        # parse succeeded and produced records
        eng = CSymEx(f, 3)
        assert len(eng.run()) == 1

    def test_strip_comments_preserves_string_literals(self):
        src = 'char *s = "not // a comment"; int x = 1; /* gone */'
        out = _strip_comments(src)
        assert '"not // a comment"' in out
        assert "gone" not in out

    def test_strip_includes_only_removes_include_lines(self):
        src = "#include <a.h>\nint x;\n  #include \"b.h\"\nint y;"
        out = _strip_includes(src)
        assert "#include" not in out
        assert "int x;" in out and "int y;" in out


# ─────────────────────────────────────────────── straight-line code ──

class TestStraightLine:
    def test_constant_propagation_through_assignments(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int a = 5;
                int b = a + 2;
                b = b * 3;
                vtrace1(a, b, x, y);
                return 0;
            }
        """)
        assert len(res) == 1
        assert_record_implies(res[0], z3.And(X("a") == 5, X("b") == 21))

    def test_slocal_relates_vtrace_args_to_input_symbols(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int s = x + y;
                vtrace1(s, x, y, s);
                return 0;
            }
        """)
        assert len(res) == 1
        assert_record_implies(res[0], X("a") == X("b") + X("c"))

    def test_compound_assignment_operators(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int a = 10;
                a += 5;
                a -= 2;
                a *= 3;
                vtrace1(a, x, y, a);
                return 0;
            }
        """)
        assert_record_implies(res[0], X("a") == 39)

    def test_increment_decrement_statements(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int i = 0;
                i++;
                ++i;
                i--;
                vtrace1(i, x, y, i);
                return 0;
            }
        """)
        assert_record_implies(res[0], X("a") == 1)

    def test_uninitialized_var_is_fresh_symbolic(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int u;
                vtrace1(u, x, y, u);
                return 0;
            }
        """)
        loc, pc, slocal = res[0]
        # u is unconstrained: both a==7 and a==8 must be consistent
        assert satisfiable(pc, slocal, X("a") == 7)
        assert satisfiable(pc, slocal, X("a") == 8)

    def test_unknown_calls_are_ignored(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                printf("hello");
                int a = 1;
                vtrace1(a, x, y, a);
                return 0;
            }
        """)
        assert len(res) == 1
        assert_record_implies(res[0], X("a") == 1)


# ─────────────────────────────────────────────────────── arithmetic ──

class TestArithmetic:
    def test_integer_division_truncates(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int q = 7 / 2;
                vtrace1(q, x, y, q);
                return 0;
            }
        """)
        assert_record_implies(res[0], X("a") == 3)

    def test_mod(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int m = 7 % 3;
                vtrace1(m, x, y, m);
                return 0;
            }
        """)
        assert_record_implies(res[0], X("a") == 1)

    def test_double_constant_is_exact_rational(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                double d = 3.25;
                double e = d * 4;
                vtrace1(e, x, y, x);
                return 0;
            }
        """, header=HEADER.replace("vtrace1(int a", "vtrace1(double a"))
        assert_record_implies(res[0], R("a") == z3.RealVal(13))

    def test_mixed_int_real_promotes_to_real_division(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                double d = 7.0 / 2;
                vtrace1(d, x, y, x);
                return 0;
            }
        """, header=HEADER.replace("vtrace1(int a", "vtrace1(double a"))
        assert_record_implies(res[0], R("a") == z3.RealVal("3.5"))

    def test_cast_real_to_int_and_back(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                double d = 3.75;
                int i = (int) d;
                vtrace1(i, x, y, i);
                return 0;
            }
        """)
        # z3 ToInt is floor; for positive values this matches C truncation
        assert_record_implies(res[0], X("a") == 3)

    def test_int_decl_of_real_expr_truncates(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int i = 2.5;
                vtrace1(i, x, y, i);
                return 0;
            }
        """)
        assert_record_implies(res[0], X("a") == 2)

    def test_unary_minus_and_plus(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int a = -x;
                int b = +x;
                vtrace1(a, b, x, y);
                return 0;
            }
        """)
        assert_record_implies(res[0], z3.And(X("a") == -X("c"), X("b") == X("c")))

    def test_bitwise_not_approximation(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int a = ~x;
                vtrace1(a, x, y, a);
                return 0;
            }
        """)
        assert_record_implies(res[0], X("a") == -X("b") - 1)


# ────────────────────────────────────────────── vassume / branching ──

class TestVassumeAndBranching:
    def test_vassume_appears_in_path_condition(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                vassume(x >= 1 && y >= 1);
                vtrace1(x, y, x, y);
                return 0;
            }
        """)
        loc, pc, slocal = res[0]
        assert implied(pc, slocal, z3.And(X("a") >= 1, X("b") >= 1))

    def test_contradictory_vassumes_kill_the_path(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                vassume(x > 0);
                vassume(x < 0);
                vtrace1(x, y, x, y);
                return 0;
            }
        """)
        assert res == []

    def test_if_forks_two_paths(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int a;
                if (x > 0) { a = 1; } else { a = 2; }
                vtrace1(a, x, y, a);
                return 0;
            }
        """)
        assert len(res) == 2
        claims = {1: X("b") > 0, 2: z3.Not(X("b") > 0)}
        seen = set()
        for rec in res:
            loc, pc, slocal = rec
            for val, cond in claims.items():
                if implied(pc, slocal, z3.And(X("a") == val, cond)):
                    seen.add(val)
        assert seen == {1, 2}

    def test_if_without_else_keeps_fallthrough_path(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int a = 0;
                if (x > 0) { a = 1; }
                vtrace1(a, x, y, a);
                return 0;
            }
        """)
        assert len(res) == 2

    def test_infeasible_branch_is_pruned(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                vassume(x > 10);
                int a = 0;
                if (x < 0) { a = 1; }
                vtrace1(a, x, y, a);
                return 0;
            }
        """)
        assert len(res) == 1
        assert_record_implies(res[0], X("a") == 0)

    def test_logical_not_condition(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                vassume(x == 5);
                int a = 0;
                if (!(x == 5)) { a = 1; }
                vtrace1(a, x, y, a);
                return 0;
            }
        """)
        assert len(res) == 1
        assert_record_implies(res[0], X("a") == 0)

    def test_nested_if_produces_four_paths(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int a = 0;
                if (x > 0) { a = a + 1; } else { a = a - 1; }
                if (y > 0) { a = a + 10; } else { a = a - 10; }
                vtrace1(a, x, y, a);
                return 0;
            }
        """)
        assert len(res) == 4


# ─────────────────────────────────────────────────────────── loops ──

class TestLoops:
    def test_concrete_bounded_while_fully_unrolls(self, tmp_path):
        # loop bound is concrete, so infeasible early exits are pruned:
        # exactly one path with i == 3
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int i = 0;
                while (i < 3) { i = i + 1; }
                vtrace1(i, x, y, i);
                return 0;
            }
        """, depth=10)
        assert len(res) == 1
        assert_record_implies(res[0], X("a") == 3)

    def test_symbolic_while_yields_depth_plus_one_paths(self, tmp_path):
        # exits after 0..depth-1 iterations, plus the depth-exhausted path
        depth = 3
        _, res = symex(tmp_path, """
            int mainQ(int n, int y){
                int i = 0;
                while (i < n) { i = i + 1; }
                vtrace1(i, n, y, i);
                return 0;
            }
        """, depth=depth)
        assert len(res) == depth + 1
        # each exit path fixes i to its iteration count
        for k in range(depth + 1):
            assert any(implied(pc, slocal, X("a") == k) for _, pc, slocal in res)

    def test_while_one_with_break(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int n, int y){
                int i = 0;
                while (1) {
                    if (!(i < n)) break;
                    i = i + 1;
                }
                vtrace1(i, n, y, i);
                return 0;
            }
        """, depth=3)
        # while(1) at max depth discards the still-running path,
        # so only the 0..depth-1 iteration exits survive
        assert len(res) == 3
        for k in range(3):
            assert any(implied(pc, slocal, X("a") == k) for _, pc, slocal in res)

    def test_continue_skips_rest_of_body(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int i = 0;
                int hits = 0;
                while (i < 4) {
                    i = i + 1;
                    if (i == 2) continue;
                    hits = hits + 1;
                }
                vtrace1(i, hits, x, y);
                return 0;
            }
        """, depth=10)
        assert len(res) == 1
        assert_record_implies(res[0], z3.And(X("a") == 4, X("b") == 3))

    def test_return_inside_loop_ends_path_before_vtrace(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int i = 0;
                while (i < 3) {
                    i = i + 1;
                    if (i == 2) return 0;
                }
                vtrace1(i, x, y, i);
                return 0;
            }
        """, depth=10)
        # the only feasible path returns at i==2 and never reaches vtrace1
        assert res == []

    def test_vtrace_inside_loop_records_every_iteration(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int i = 0;
                while (i < 3) {
                    vtrace1(i, x, y, i);
                    i = i + 1;
                }
                return 0;
            }
        """, depth=10)
        assert len(res) == 3
        for k in range(3):
            assert any(implied(pc, slocal, X("a") == k) for _, pc, slocal in res)

    def test_for_loop_desugars_to_while(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int s = 0;
                int i;
                for (i = 0; i < 3; i++) { s = s + i; }
                vtrace1(s, i, x, y);
                return 0;
            }
        """, depth=10)
        assert len(res) == 1
        assert_record_implies(res[0], z3.And(X("a") == 3, X("b") == 3))

    def test_nested_loops_share_depth_budget(self, tmp_path):
        # cohendiv-style nesting must terminate and produce records
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                vassume(x >= 1 && y >= 1);
                int q = 0;
                int r = x;
                while (1) {
                    vtrace1(q, r, x, y);
                    if (!(r >= y)) break;
                    int b = y;
                    while (1) {
                        if (!(r >= 2*b)) break;
                        b = 2 * b;
                    }
                    r = r - b;
                    q = q + 1;
                }
                return q;
            }
        """, depth=3)
        assert len(res) >= 2
        # the loop head invariant q*y + r == x holds at every vtrace1
        for rec in res:
            assert_record_implies(
                rec, X("a") * X("d") + X("b") == X("c"))

    def test_max_states_cap_is_respected(self, tmp_path):
        f = tmp_path / "prog.c"
        f.write_text(HEADER + """
            int mainQ(int n, int y){
                int i = 0;
                int s = 0;
                while (i < n) {
                    if (y > i) { s = s + 1; } else { s = s - 1; }
                    i = i + 1;
                }
                vtrace1(i, s, n, y);
                return 0;
            }
        """)
        eng = CSymEx(f, 6)
        eng.MAX_STATES = 4  # instance override, shadows the class attr
        res = eng.run()     # must terminate quickly and not explode
        assert 0 < len(res) <= 64


# ───────────────────────────────────────────────────── modeled calls ──

class TestModeledCalls:
    def test_isqrt_decl_adds_defining_constraints(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int n, int y){
                vassume(n >= 0);
                int s = isqrt(n);
                vtrace1(s, n, y, s);
                return 0;
            }
        """)
        assert len(res) == 1
        loc, pc, slocal = res[0]
        # s*s <= n < (s+1)^2 must be entailed
        a, b = X("a"), X("b")
        assert implied(pc, slocal, z3.And(a >= 0, a * a <= b,
                                          (a + 1) * (a + 1) > b))

    def test_isqrt_assignment_form(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int n, int y){
                vassume(n == 10);
                int s;
                s = isqrt(n);
                vtrace1(s, n, y, s);
                return 0;
            }
        """)
        assert len(res) == 1
        assert_record_implies(res[0], X("a") == 3)


# ──────────────────────────────────────────────── C truthiness ──────

class TestTruthiness:
    def test_int_expression_as_if_condition(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int a = 0;
                if (x % 2) { a = 1; }
                vtrace1(a, x, y, a);
                return 0;
            }
        """)
        assert len(res) == 2
        # the a==1 path must imply x is odd
        for _, pc, slocal in res:
            if implied(pc, slocal, X("a") == 1):
                assert implied(pc, slocal, X("b") % 2 != 0)
                break
        else:
            pytest.fail("no path with a == 1")

    def test_int_expression_as_while_condition(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int n = 3;
                while (n) { n = n - 1; }
                vtrace1(n, x, y, n);
                return 0;
            }
        """, depth=10)
        assert len(res) == 1
        assert_record_implies(res[0], X("a") == 0)

    def test_logical_and_on_int_operands(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int a = 0;
                if (x && y) { a = 1; }
                vtrace1(a, x, y, a);
                return 0;
            }
        """)
        for _, pc, slocal in res:
            if implied(pc, slocal, X("a") == 1):
                assert implied(pc, slocal,
                               z3.And(X("b") != 0, X("c") != 0))
                break
        else:
            pytest.fail("no path with a == 1")

    def test_bang_on_int_variable(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int a = 0;
                if (!x) { a = 1; }
                vtrace1(a, x, y, a);
                return 0;
            }
        """)
        for _, pc, slocal in res:
            if implied(pc, slocal, X("a") == 1):
                assert implied(pc, slocal, X("b") == 0)
                break
        else:
            pytest.fail("no path with a == 1")


# ───────────────────────────────────────────────────── vassert ──────

class TestVassert:
    def test_valid_assert(self, tmp_path):
        eng, _ = symex(tmp_path, """
            int mainQ(int x, int y){
                vassume(x > 0);
                vassert(x >= 1);
                return 0;
            }
        """)
        assert [a.status for a in eng.assert_results] == ["valid"]
        assert eng.assert_results[0].cex is None

    def test_violated_assert_yields_concrete_counterexample(self, tmp_path):
        eng, _ = symex(tmp_path, """
            int mainQ(int x, int y){
                vassume(x >= 0);
                vassert(x > 0);
                return 0;
            }
        """)
        (a,) = eng.assert_results
        assert a.status == "violated"
        assert a.cex["X_x"] == "0"   # the only input value that falsifies it

    def test_checked_per_path(self, tmp_path):
        eng, _ = symex(tmp_path, """
            int mainQ(int x, int y){
                int a;
                if (x > 0) { a = 1; } else { a = -1; }
                vassert(a > 0);
                return 0;
            }
        """)
        assert sorted(a.status for a in eng.assert_results) == \
            ["valid", "violated"]

    def test_assume_after_assert_constrains_downstream(self, tmp_path):
        eng, res = symex(tmp_path, """
            int mainQ(int x, int y){
                vassert(x > 0);
                int a = 0;
                if (x <= 0) { a = 1; }
                vtrace1(a, x, y, a);
                return 0;
            }
        """)
        assert eng.assert_results[0].status == "violated"
        # downstream treats x > 0 as assumed: the x <= 0 branch is dead
        assert len(res) == 1
        assert_record_implies(res[0], X("a") == 0)

    def test_always_false_assert_kills_the_path(self, tmp_path):
        eng, res = symex(tmp_path, """
            int mainQ(int x, int y){
                vassume(x == 0);
                vassert(x != 0);
                vtrace1(x, y, x, y);
                return 0;
            }
        """)
        assert eng.assert_results[0].status == "violated"
        assert res == []   # no input satisfies pc ∧ cond

    def test_bounded_verification_inside_loop(self, tmp_path):
        eng, _ = symex(tmp_path, """
            int mainQ(int n, int y){
                int i = 0;
                int s = 0;
                while (i < n) {
                    i = i + 1;
                    s = s + i;
                    vassert(2*s == i*(i+1));
                }
                return 0;
            }
        """, depth=4)
        assert len(eng.assert_results) == 4   # one per unrolled iteration
        assert all(a.status == "valid" for a in eng.assert_results)

    def test_int_condition_in_assert(self, tmp_path):
        eng, _ = symex(tmp_path, """
            int mainQ(int x, int y){
                vassume(x == 3);
                vassert(x);
                return 0;
            }
        """)
        assert eng.assert_results[0].status == "valid"


# ───────────────────────────────────────────── unknown()/nondet ─────

class TestUnknown:
    def test_unknown_is_unconstrained(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int u = unknown();
                vtrace1(u, x, y, u);
                return 0;
            }
        """)
        _, pc, slocal = res[0]
        assert satisfiable(pc, slocal, X("a") == 5)
        assert satisfiable(pc, slocal, X("a") == -7)

    def test_each_call_is_a_fresh_value(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int a = unknown();
                int b = unknown();
                vtrace1(a, b, x, y);
                return 0;
            }
        """)
        _, pc, slocal = res[0]
        assert satisfiable(pc, slocal, X("a") == X("b"))
        assert satisfiable(pc, slocal, X("a") != X("b"))

    def test_unknown_as_branch_condition(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int a = 0;
                if (unknown()) { a = 1; }
                vtrace1(a, x, y, a);
                return 0;
            }
        """)
        assert len(res) == 2


# ─────────────────────────────────────────────────── ternary ────────

class TestTernary:
    def test_max_via_ternary(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int m = x > y ? x : y;
                vtrace1(m, x, y, m);
                return 0;
            }
        """)
        assert len(res) == 1   # ternary is an If expression, not a path fork
        _, pc, slocal = res[0]
        assert implied(pc, slocal, z3.And(X("a") >= X("b"), X("a") >= X("c")))
        assert implied(pc, slocal,
                       z3.Or(X("a") == X("b"), X("a") == X("c")))

    def test_ternary_narrowed_by_path_condition(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                vassume(x < 0);
                int s = x >= 0 ? 1 : -1;
                vtrace1(s, x, y, s);
                return 0;
            }
        """)
        assert_record_implies(res[0], X("a") == -1)


# ─────────────────────────────────────── C division semantics ───────

class TestCDivision:
    """C truncates toward zero; remainder takes the dividend's sign."""

    CASES = [  # (x, y, x/y, x%y) per C99
        (7, 2, 3, 1),
        (-7, 2, -3, -1),
        (7, -2, -3, 1),
        (-7, -2, 3, -1),
    ]

    @pytest.mark.parametrize("x,y,q,r", CASES)
    def test_div_mod_matches_c(self, tmp_path, x, y, q, r):
        _, res = symex(tmp_path, f"""
            int mainQ(int a, int b){{
                vassume(a == ({x}) && b == ({y}));
                int q = a / b;
                int r = a % b;
                vtrace1(q, r, a, b);
                return 0;
            }}
        """)
        assert len(res) == 1
        assert_record_implies(res[0], z3.And(X("a") == q, X("b") == r))

    def test_symbolic_negative_dividend_identity(self, tmp_path):
        # (a/b)*b + a%b == a and remainder non-positive for a <= 0 < b
        eng, _ = symex(tmp_path, """
            int mainQ(int a, int b){
                vassume(a <= 0 && b >= 1);
                int q = a / b;
                int r = a % b;
                vassert(q*b + r == a);
                vassert(r <= 0);
                return 0;
            }
        """)
        assert [x.status for x in eng.assert_results] == ["valid", "valid"]

    def test_nonneg_fast_path_form_unchanged(self, tmp_path):
        # under vassume(a >= 0, b > 0) the plain z3 div form is kept,
        # so pre-existing symstates stay byte-identical
        _, res = symex(tmp_path, """
            int mainQ(int a, int b){
                vassume(a >= 0 && b >= 1);
                int q = a / b;
                vtrace1(q, a, b, q);
                return 0;
            }
        """)
        _, _, slocal = res[0]
        assert "If" not in str(slocal)


# ─────────────────────────────── side effects in conditions ─────────

class TestConditionSideEffects:
    def test_post_increment_in_while_condition(self, tmp_path):
        # i++ evaluated on every test, including the failing one: exit i == 4
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int i = 0;
                while (i++ < 3) { }
                vtrace1(i, x, y, i);
                return 0;
            }
        """, depth=10)
        assert len(res) == 1
        assert_record_implies(res[0], X("a") == 4)

    def test_symbolic_bound_exit_value(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int n, int y){
                vassume(n == 2);
                int i = 0;
                while (i++ < n) { }
                vtrace1(i, n, y, i);
                return 0;
            }
        """, depth=6)
        assert len(res) == 1
        assert_record_implies(res[0], X("a") == X("b") + 1)

    def test_decrement_in_if_condition_applies_to_both_branches(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                vassume(x == 1);
                int a = 0;
                if (x-- > 0) { a = 1; }
                vtrace1(a, x, y, a);
                return 0;
            }
        """)
        assert len(res) == 1
        assert_record_implies(res[0], z3.And(X("a") == 1, X("b") == 0))

    def test_pre_vs_post_increment_value(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int i = 5;
                int j = 5;
                int a = ++i;
                int b = j++;
                vtrace1(a, b, i, j);
                return 0;
            }
        """)
        assert_record_implies(res[0], z3.And(
            X("a") == 6, X("b") == 5, X("c") == 6, X("d") == 6))


# ─────────────────────────────────────────── post-run APIs ──────────

class TestPostRunAPIs:
    DIVIDER = """
        int mainQ(int x, int y){
            vassume(x >= 1 && y >= 1);
            int q = 0;
            int r = x;
            while (r >= y) { r = r - y; q = q + 1; }
            vtrace1(q, r, x, y);
            return q;
        }
    """

    def test_gen_inputs_covers_every_path_and_satisfies_pc(self, tmp_path):
        eng, res = symex(tmp_path, self.DIVIDER, depth=3)
        inputs = eng.gen_inputs()
        assert len(inputs) == len(res)
        for (loc, vals), (rloc, pc, _) in zip(inputs, res):
            assert loc == rloc == "vtrace1"
            x, y = int(vals["x"]), int(vals["y"])
            assert x >= 1 and y >= 1
            # the concrete input must satisfy that path's condition
            s = z3.Solver()
            s.add(pc, z3.Int("X_x") == x, z3.Int("X_y") == y)
            assert s.check() == z3.sat

    def test_gen_inputs_distinguish_paths(self, tmp_path):
        # paths differ in iteration count, so q = x/y differs per input
        eng, _ = symex(tmp_path, self.DIVIDER, depth=3)
        quotients = {int(v["x"]) // int(v["y"]) for _, v in eng.gen_inputs()}
        assert len(quotients) >= 2

    def test_unreached_vtrace_is_reported(self, tmp_path):
        eng, res = symex(tmp_path, """
            int mainQ(int x, int y){
                vtrace1(x, y, x, y);
                if (x > 0 && x < 0) { vtrace2(x, y, x, y); }
                return 0;
            }
        """)
        assert eng.unreached_locs() == ["vtrace2"]
        assert [loc for loc, _, _ in res] == ["vtrace1"]

    def test_check_inv_valid(self, tmp_path):
        eng, _ = symex(tmp_path, self.DIVIDER, depth=3)
        # vtrace1(q, r, x, y) binds to declared params (a, b, c, d)
        status, cex = eng.check_inv(
            "vtrace1", X("a") * X("d") + X("b") == X("c"))
        assert status == "valid" and cex is None

    def test_check_inv_violated_with_counterexample(self, tmp_path):
        eng, _ = symex(tmp_path, self.DIVIDER, depth=3)
        status, cex = eng.check_inv("vtrace1", X("q") >= 1)  # false: q can be 0
        assert status == "violated"
        assert cex  # concrete assignment falsifying the claim


# ─────────────────────────────────────────────────── arrays ─────────

class TestArrays:
    def test_concrete_store_and_select(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int a[10];
                a[0] = 5;
                a[1] = a[0] + 2;
                vtrace1(a[1], x, y, a[0]);
                return 0;
            }
        """)
        assert len(res) == 1
        assert_record_implies(res[0], z3.And(X("a") == 7, X("d") == 5))

    def test_symbolic_index_aliasing(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int i, int j){
                vassume(i == j);
                int a[10];
                a[i] = 5;
                int v = a[j];
                vtrace1(v, i, j, v);
                return 0;
            }
        """)
        assert_record_implies(res[0], X("a") == 5)

    def test_distinct_indices_do_not_clobber(self, tmp_path):
        eng, _ = symex(tmp_path, """
            int mainQ(int i, int j){
                vassume(i != j);
                int a[10];
                a[i] = 1;
                a[j] = 2;
                vassert(a[i] == 1 && a[j] == 2);
                return 0;
            }
        """)
        assert [a.status for a in eng.assert_results] == ["valid"]

    def test_init_list_and_zero_fill(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int a[4] = {3, 4};
                vtrace1(a[0], a[1], a[2], a[3]);
                return 0;
            }
        """)
        assert_record_implies(res[0], z3.And(
            X("a") == 3, X("b") == 4, X("c") == 0, X("d") == 0))

    def test_loop_sum_over_initialized_array(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int a[3] = {1, 2, 3};
                int s = 0;
                int i;
                for (i = 0; i < 3; i++) { s = s + a[i]; }
                vtrace1(s, x, y, s);
                return 0;
            }
        """, depth=6)
        assert len(res) == 1
        assert_record_implies(res[0], X("a") == 6)

    def test_array_parameter_is_symbolic_input(self, tmp_path):
        eng, _ = symex(tmp_path, """
            int mainQ(int a[], int i){
                vassume(a[i] > 0);
                vassert(a[i] >= 1);
                vassert(a[i+1] >= 1);
                return 0;
            }
        """)
        assert eng.mainq_params == [("a", "int[]"), ("i", "int")]
        # a[i] is constrained, a[i+1] is not
        assert [a.status for a in eng.assert_results] == ["valid", "violated"]

    def test_array_element_increment_statement(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int a[2] = {10, 20};
                a[0]++;
                a[1]--;
                vtrace1(a[0], a[1], x, y);
                return 0;
            }
        """)
        assert_record_implies(res[0], z3.And(X("a") == 11, X("b") == 19))

    def test_swap_idiom(self, tmp_path):
        eng, _ = symex(tmp_path, """
            int mainQ(int i, int j){
                vassume(i != j);
                int a[10];
                int x = a[i];
                int y = a[j];
                int t = a[i];
                a[i] = a[j];
                a[j] = t;
                vassert(a[i] == y && a[j] == x);
                return 0;
            }
        """)
        assert [a.status for a in eng.assert_results] == ["valid"]


# ─────────────────────────────────────────────────── structs ────────

class TestStructs:
    def test_tag_struct_field_write_read(self, tmp_path):
        _, res = symex(tmp_path, """
            struct Point { int x; int y; };
            int mainQ(int u, int v){
                struct Point p;
                p.x = 3;
                p.y = p.x + 1;
                vtrace1(p.x, p.y, u, v);
                return 0;
            }
        """)
        assert len(res) == 1
        assert_record_implies(res[0], z3.And(X("a") == 3, X("b") == 4))

    def test_typedef_struct_and_init_list(self, tmp_path):
        _, res = symex(tmp_path, """
            typedef struct { int w; int h; } Rect;
            int mainQ(int u, int v){
                Rect r = {4, 5};
                int area = r.w * r.h;
                vtrace1(area, r.w, r.h, area);
                return 0;
            }
        """)
        assert_record_implies(res[0], z3.And(
            X("a") == 20, X("b") == 4, X("c") == 5))

    def test_whole_struct_copy(self, tmp_path):
        _, res = symex(tmp_path, """
            struct Point { int x; int y; };
            int mainQ(int u, int v){
                struct Point p;
                p.x = u; p.y = v;
                struct Point q;
                q = p;
                p.x = 99;
                vtrace1(q.x, q.y, p.x, u);
                return 0;
            }
        """)
        # q keeps the copied values; later writes to p don't leak into q
        assert_record_implies(res[0], z3.And(
            X("a") == X("d"), X("c") == 99))

    def test_nested_struct(self, tmp_path):
        _, res = symex(tmp_path, """
            struct Inner { int v; };
            struct Outer { struct Inner in; int k; };
            int mainQ(int u, int v){
                struct Outer o;
                o.in.v = 7;
                o.k = o.in.v * 2;
                vtrace1(o.in.v, o.k, u, v);
                return 0;
            }
        """)
        assert_record_implies(res[0], z3.And(X("a") == 7, X("b") == 14))

    def test_struct_field_in_condition_and_assert(self, tmp_path):
        eng, res = symex(tmp_path, """
            struct Acc { int sum; int n; };
            int mainQ(int u, int v){
                vassume(u > 0);
                struct Acc a;
                a.sum = 0; a.n = 0;
                while (a.n < u) { a.sum = a.sum + 2; a.n = a.n + 1; }
                vassert(a.sum == 2 * a.n);
                vtrace1(a.sum, a.n, u, v);
                return 0;
            }
        """, depth=3)
        assert all(r.status == "valid" for r in eng.assert_results)
        for rec in res:
            assert_record_implies(rec, X("a") == 2 * X("b"))

    def test_struct_field_increment_statement(self, tmp_path):
        _, res = symex(tmp_path, """
            struct C { int n; };
            int mainQ(int u, int v){
                struct C c;
                c.n = 5;
                c.n++;
                vtrace1(c.n, u, v, c.n);
                return 0;
            }
        """)
        assert_record_implies(res[0], X("a") == 6)

    def test_struct_with_array_field(self, tmp_path):
        _, res = symex(tmp_path, """
            struct Buf { int data[4]; int len; };
            int mainQ(int u, int v){
                struct Buf b;
                b.len = 0;
                b.data[0] = 42;
                b.len = b.len + 1;
                vtrace1(b.data[0], b.len, u, v);
                return 0;
            }
        """)
        assert_record_implies(res[0], z3.And(X("a") == 42, X("b") == 1))


# ─────────────────────────────────────── auto safety checks ─────────

class TestSafetyChecks:
    def run_safety(self, tmp_path, src, depth=5):
        f = tmp_path / "prog.c"
        f.write_text(HEADER + src)
        eng = CSymEx(f, depth, check_safety=True)
        eng.run()
        return eng

    def test_reachable_division_by_zero(self, tmp_path):
        eng = self.run_safety(tmp_path, """
            int mainQ(int x, int y){
                vassume(y >= 0);
                int q = x / y;
                vtrace1(q, x, y, q);
                return q;
            }
        """)
        (s,) = eng.safety_results
        assert s.kind == "division-by-zero" and s.status == "violated"
        assert s.cex["X_y"] == "0"

    def test_guarded_division_reports_nothing(self, tmp_path):
        eng = self.run_safety(tmp_path, """
            int mainQ(int x, int y){
                vassume(y >= 1);
                int q = x / y;
                int r = x % y;
                vtrace1(q, r, x, y);
                return q;
            }
        """)
        assert eng.safety_results == []

    def test_mod_by_possibly_zero(self, tmp_path):
        eng = self.run_safety(tmp_path, """
            int mainQ(int x, int y){
                int r = x % y;
                vtrace1(r, x, y, r);
                return r;
            }
        """)
        assert [s.kind for s in eng.safety_results] == ["division-by-zero"]
        assert eng.safety_results[0].status == "violated"

    def test_reachable_out_of_bounds_read(self, tmp_path):
        eng = self.run_safety(tmp_path, """
            int mainQ(int i, int y){
                vassume(i >= 0);
                int a[4] = {1, 2, 3, 4};
                int v = a[i];
                vtrace1(v, i, y, v);
                return v;
            }
        """)
        (s,) = eng.safety_results
        assert s.kind == "array-bounds" and s.status == "violated"
        assert int(s.cex["X_i"]) >= 4

    def test_in_bounds_access_reports_nothing(self, tmp_path):
        eng = self.run_safety(tmp_path, """
            int mainQ(int i, int y){
                vassume(i >= 0 && i < 4);
                int a[4] = {1, 2, 3, 4};
                a[i] = 9;
                vtrace1(a[i], i, y, i);
                return 0;
            }
        """)
        assert eng.safety_results == []

    def test_unsized_param_arrays_are_never_checked(self, tmp_path):
        eng = self.run_safety(tmp_path, """
            int mainQ(int a[], int i){
                int v = a[i];
                vtrace1(v, i, v, i);
                return v;
            }
        """)
        assert eng.safety_results == []

    def test_default_off(self, tmp_path):
        f = tmp_path / "prog.c"
        f.write_text(HEADER + """
            int mainQ(int x, int y){
                int q = x / y;
                vtrace1(q, x, y, q);
                return q;
            }
        """)
        eng = CSymEx(f, 5)   # check_safety not set
        eng.run()
        assert eng.safety_results == []


# ───────────────────────────────────────────── k-induction ──────────

class TestKInduction:
    DIVIDER = HEADER + """
        int mainQ(int x, int y){
            vassume(x >= 0 && y >= 1);
            int q = 0;
            int r = x;
            while (r >= y) { r = r - y; q = q + 1; }
            vtrace1(q, r, x, y);
            return q;
        }
    """

    def engine(self, tmp_path, src=None, depth=1):
        # depth=1 on purpose: induction must not depend on unrolling
        f = tmp_path / "prog.c"
        f.write_text(src or self.DIVIDER)
        return CSymEx(f, depth)

    def test_valid_invariant_proved_unbounded(self, tmp_path):
        eng = self.engine(tmp_path)
        status, cex = eng.prove_inductive(
            X("q") * X("y") + X("r") == X("x"))
        assert status == "valid" and cex is None

    def test_base_violation(self, tmp_path):
        eng = self.engine(tmp_path)
        status, cex = eng.prove_inductive(X("q") == 1)  # q == 0 at entry
        assert status == "base-violated"
        assert cex  # concrete X_* inputs

    def test_step_violation_with_pre_iteration_state(self, tmp_path):
        eng = self.engine(tmp_path)
        status, cex = eng.prove_inductive(X("q") <= 5)  # not preserved
        assert status == "step-violated"
        assert any(k.startswith("_ind_") for k in cex)

    def test_for_loop_invariant(self, tmp_path):
        eng = self.engine(tmp_path, HEADER + """
            int mainQ(int n, int y){
                vassume(n >= 0);
                int s = 0;
                int i;
                for (i = 0; i < n; i++) { s = s + 2; }
                vtrace1(s, i, n, y);
                return s;
            }
        """)
        status, _ = eng.prove_inductive(z3.And(
            X("i") >= 0, X("i") <= X("n"), X("s") == 2 * X("i")))
        assert status == "valid"

    def test_run_results_not_polluted(self, tmp_path):
        eng = self.engine(tmp_path, depth=3)
        res = eng.run()
        n_records = len(eng.records)
        eng.prove_inductive(X("q") * X("y") + X("r") == X("x"))
        assert len(eng.records) == n_records  # prove didn't add records

    ALTERNATING = HEADER + """
        int mainQ(int n, int y){
            int x = 0;
            int i = 0;
            while (i < n) { x = -x; i = i + 1; }
            vtrace1(x, i, n, y);
            return x;
        }
    """

    def test_two_inductive_invariant_needs_k2(self, tmp_path):
        eng = self.engine(tmp_path, self.ALTERNATING)
        inv = X("x") != 1
        status1, _ = eng.prove_inductive(inv, k=1)
        assert status1 == "step-violated"   # havoc x = -1 flips to 1
        status2, _ = eng.prove_inductive(inv, k=2)
        assert status2 == "valid"           # two heads exclude x = -1

    def test_in_body_vassert_does_not_leak_into_step(self):
        # k2induction.c asserts x != 1 INSIDE the loop body; its
        # assume-after-assert must not smuggle the property into the
        # induction step (that made k=1 vacuously "valid" once)
        eng = CSymEx(PROGS_DIR / "k2induction.c", 1)
        s1, _ = eng.prove_inductive(X("x") != 1, k=1)
        assert s1 == "step-violated"
        s2, _ = eng.prove_inductive(X("x") != 1, k=2)
        assert s2 == "valid"

    def test_k2_base_covers_second_head(self, tmp_path):
        eng = self.engine(tmp_path, HEADER + """
            int mainQ(int n, int y){
                int i = 0;
                while (i < n) { i = i + 1; }
                vtrace1(i, n, y, i);
                return i;
            }
        """)
        inv = X("i") != 1
        s1, _ = eng.prove_inductive(inv, k=1)
        assert s1 == "step-violated"        # base head 0 (i=0) passes
        s2, cex = eng.prove_inductive(inv, k=2)
        assert s2 == "base-violated"        # head 1 has i == 1
        assert cex                          # concrete inputs reaching it


# ─────────────────────────────────────────────── termination ────────

class TestTermination:
    def engine(self, tmp_path):
        f = tmp_path / "prog.c"
        f.write_text(TestKInduction.DIVIDER)
        return CSymEx(f, 1)   # depth-independent, like induction

    def test_divider_terminates_with_supporting_invariant(self, tmp_path):
        eng = self.engine(tmp_path)
        y_pos = X("y") >= 1
        assert eng.houdini([y_pos]) == [y_pos]   # sound to assume
        status, cex = eng.prove_termination(X("r"), assume=[y_pos])
        assert status == "terminates" and cex is None

    def test_without_the_invariant_no_proof(self, tmp_path):
        # havoc allows y (and hence r >= y) below 0: bound fails first
        eng = self.engine(tmp_path)
        status, cex = eng.prove_termination(X("r"))
        assert status == "bound-violated"
        assert int(cex["_ind_r"]) < 0

    def test_non_decreasing_rank_rejected(self, tmp_path):
        # q >= 0 makes the bound pass, so the increase is what fails
        eng = self.engine(tmp_path)
        status, _ = eng.prove_termination(
            X("q"), assume=[X("y") >= 1, X("q") >= 0])
        assert status == "decrease-violated"   # q increases

    def test_unbounded_rank_rejected(self, tmp_path):
        eng = self.engine(tmp_path)
        status, _ = eng.prove_termination(-X("q"), assume=[X("y") >= 1])
        assert status == "bound-violated"      # -q < 0 for havoc q > 0

    def test_cli_terminates_with_assume(self):
        prog = PROGS_DIR / "termination.c"
        ok = subprocess.run(
            [sys.executable, str(ENGINE_FILE), str(prog), "--depth", "2",
             "--terminates", "r", "--assume", "y >= 1"],
            capture_output=True, text=True)
        assert ok.returncode == 0, ok.stdout + ok.stderr
        assert "terminates (rank r): terminates" in ok.stdout

        bad = subprocess.run(
            [sys.executable, str(ENGINE_FILE), str(prog), "--depth", "2",
             "--terminates", "q", "--assume", "y >= 1", "--assume", "q >= 0"],
            capture_output=True, text=True)
        assert bad.returncode == 1
        assert "decrease-violated" in bad.stdout   # q >= 0 passes the bound


# ───────────────────────────────────────────── witness traces ───────

class TestWitnessTraces:
    def test_violation_carries_branch_decisions(self):
        eng = CSymEx(PROGS_DIR / "witness_bad.c", 4)
        eng.run()
        (bad,) = [a for a in eng.assert_results if a.status == "violated"]
        trace = " | ".join(bad.trace)
        assert "assume" in trace
        assert "if-true" in trace      # took x > 0
        assert "if-false" in trace     # took the else of y > x
        assert "witness_bad.c:" in trace   # real source coords

    def test_loop_iterations_are_traced(self, tmp_path):
        f = tmp_path / "prog.c"
        f.write_text(HEADER + """
            int mainQ(int x, int y){
                vassume(x == 2);
                int i = 0;
                while (i < x) { i = i + 1; }
                vassert(i == 3);   /* wrong on purpose */
                return i;
            }
        """)
        eng = CSymEx(f, 6)
        eng.run()
        (bad,) = [a for a in eng.assert_results if a.status == "violated"]
        trace = " | ".join(bad.trace)
        assert "loop-iter 1" in trace and "loop-iter 2" in trace
        assert "loop-exit" in trace

    def test_cli_prints_witness_trace(self):
        out = subprocess.run(
            [sys.executable, str(ENGINE_FILE),
             str(PROGS_DIR / "witness_bad.c")],
            capture_output=True, text=True)
        assert out.returncode == 1
        assert "witness trace:" in out.stdout
        assert "if-false" in out.stdout


# ─────────────────────────────────────────── replay harness ─────────

class TestReplayHarness:
    def test_harness_contents(self, tmp_path):
        f = tmp_path / "prog.c"
        f.write_text(HEADER + """
            int mainQ(int x, int y){
                vassume(x >= 1 && y >= 1);
                int q = 0;
                int r = x;
                while (r >= y) { r = r - y; q = q + 1; }
                vtrace1(q, r, x, y);
                return q;
            }
        """)
        eng = CSymEx(f, 3)
        res = eng.run()
        harness = eng.gen_test_harness()
        assert "extern int mainQ(int x, int y);" in harness
        assert harness.count("mainQ(") == len(res) + 1  # calls + extern decl
        assert "-> vtrace1" in harness

    def test_array_params_not_supported(self, tmp_path):
        f = tmp_path / "prog.c"
        f.write_text(HEADER + """
            int mainQ(int a[], int i){
                vtrace1(a[i], i, i, i);
                return 0;
            }
        """)
        eng = CSymEx(f, 3)
        eng.run()
        assert "not supported" in eng.gen_test_harness()

    @pytest.mark.skipif(shutil.which("gcc") is None, reason="no gcc")
    def test_harness_compiles_and_runs(self, tmp_path):
        prog = PROGS_DIR / "divider_bad.c"   # defines mainQ, no main
        eng = CSymEx(prog, 4)
        eng.run()
        harness = tmp_path / "harness.c"
        harness.write_text(eng.gen_test_harness())
        exe = tmp_path / "replay"
        cc = subprocess.run(["gcc", str(prog), str(harness), "-o", str(exe)],
                            capture_output=True, text=True)
        assert cc.returncode == 0, cc.stderr
        run = subprocess.run([str(exe)], capture_output=True)
        assert run.returncode == 0


# ─────────────────────────────────────────── state merging ──────────

class TestStateMerging:
    def test_diamonds_merge_to_one_path(self):
        prog = PROGS_DIR / "merge_diamonds.c"
        plain = CSymEx(prog, 4)
        n_plain = len(plain.run())
        merged = CSymEx(prog, 4, merge_states=True)
        n_merged = len(merged.run())
        assert n_plain == 16   # monotone conds prune 64 combos to 16
        assert n_merged == 1
        # semantics preserved: the vassert still verifies on the merged state
        assert all(a.status == "valid" for a in merged.assert_results)

    def test_merged_state_still_precise(self, tmp_path):
        f = tmp_path / "prog.c"
        f.write_text(HEADER + """
            int mainQ(int x, int y){
                int a;
                if (x > 0) { a = 1; } else { a = -1; }
                vtrace1(a, x, y, a);
                return a;
            }
        """)
        eng = CSymEx(f, 3, merge_states=True)
        res = eng.run()
        assert len(res) == 1
        _, pc, slocal = res[0]
        # If-term keeps the branch correlation exactly
        assert implied(pc, slocal,
                       z3.Or(z3.And(X("a") == 1, X("b") > 0),
                             z3.And(X("a") == -1, z3.Not(X("b") > 0))))
        assert not satisfiable(pc, slocal, X("a") == 1, X("b") <= 0)

    def test_no_merge_when_branch_adds_constraints(self, tmp_path):
        f = tmp_path / "prog.c"
        f.write_text(HEADER + """
            int mainQ(int x, int y){
                int a = 0;
                if (x > 0) { vassume(x > 5); a = 1; }
                vtrace1(a, x, y, a);
                return a;
            }
        """)
        eng = CSymEx(f, 3, merge_states=True)
        res = eng.run()
        assert len(res) == 2   # vassume added a constraint: kept separate

    def test_default_off_preserves_path_counts(self):
        prog = PROGS_DIR / "merge_diamonds.c"
        eng = CSymEx(prog, 4)
        assert len(eng.run()) == 16


# ─────────────────────────────────────── function inlining ──────────

class TestInlining:
    def test_branching_helper_forks_caller_paths(self, tmp_path):
        eng, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int a = iabs(x);
                vtrace1(a, x, y, a);
                return a;
            }
        """, header=HEADER + """
            int iabs(int v){ if (v < 0) { return -v; } return v; }
        """)
        assert len(res) == 2   # helper's two paths fork the caller
        for rec in res:
            assert_record_implies(rec, X("a") >= 0)

    def test_loop_helper(self, tmp_path):
        eng, _ = symex(tmp_path, """
            int mainQ(int x, int y){
                int s = sum_to(3);
                vassert(s == 6);
                vtrace1(s, x, y, s);
                return s;
            }
        """, header=HEADER + """
            int sum_to(int n){
                int s = 0;
                int i;
                for (i = 1; i <= n; i++) { s = s + i; }
                return s;
            }
        """, depth=6)
        assert [a.status for a in eng.assert_results] == ["valid"]

    def test_caller_locals_shielded_from_callee(self, tmp_path):
        eng, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int a = 1;
                int r = clobber(a);
                vtrace1(a, r, x, y);
                return r;
            }
        """, header=HEADER + """
            int clobber(int a){ a = 99; return a; }
        """)
        # callee wrote its own 'a'; the caller's survives
        assert_record_implies(res[0], z3.And(X("a") == 1, X("b") == 99))

    def test_unbounded_recursion_capped_to_fresh_value(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int r = rec(x);
                vtrace1(r, x, y, r);
                return r;
            }
        """, header=HEADER + """
            int rec(int n){ return rec(n); }
        """)
        assert len(res) == 1
        _, pc, slocal = res[0]
        # capped call yields an unconstrained fresh value, not a crash
        assert satisfiable(pc, slocal, X("a") == 7)
        assert satisfiable(pc, slocal, X("a") == 8)

    def test_statement_call_only_globals_survive(self, tmp_path):
        eng, res = symex(tmp_path, """
            int mainQ(int x, int y){
                int local = 5;
                noop(local);
                vtrace1(local, x, y, local);
                return 0;
            }
        """, header=HEADER + """
            void noop(int v){ v = v + 1; }
        """)
        assert_record_implies(res[0], X("a") == 5)


# ───────────────────────────────────────────────── globals ──────────

class TestGlobals:
    def test_zero_init_and_explicit_init(self, tmp_path):
        eng, _ = symex(tmp_path, """
            int mainQ(int x, int y){
                vassert(g == 0);
                vassert(t == 10);
                return 0;
            }
        """, header=HEADER + "int g;\nint t = 10;\n")
        assert all(a.status == "valid" for a in eng.assert_results)

    def test_global_writes_persist(self, tmp_path):
        eng, res = symex(tmp_path, """
            int mainQ(int x, int y){
                t = t + x;
                t = t + 1;
                vtrace1(t, x, y, t);
                return t;
            }
        """, header=HEADER + "int t = 10;\n")
        assert_record_implies(res[0], X("a") == 11 + X("b"))

    def test_helper_call_updates_global(self, tmp_path):
        eng, _ = symex(tmp_path, """
            int mainQ(int x, int y){
                bump();
                bump();
                vassert(g == 2);
                return g;
            }
        """, header=HEADER + """
            int g;
            void bump(){ g = g + 1; }
        """)
        assert [a.status for a in eng.assert_results] == ["valid"]


# ───────────────────────────────────────── overflow checking ────────

class TestOverflowCheck:
    def test_square_of_input_overflows(self, tmp_path):
        f = tmp_path / "prog.c"
        f.write_text(HEADER + """
            int mainQ(int x, int y){
                vassume(x > 0);
                int sq = x * x;
                vtrace1(sq, x, y, sq);
                return sq;
            }
        """)
        eng = CSymEx(f, 4, check_overflow=True)
        eng.run()
        hits = [s for s in eng.safety_results
                if s.kind == "signed-overflow" and s.status == "violated"]
        assert hits
        assert int(hits[0].cex["X_x"]) > 46340

    def test_range_bounded_arithmetic_is_clean(self, tmp_path):
        f = tmp_path / "prog.c"
        f.write_text(HEADER + """
            int mainQ(int x, int y){
                vassume(x >= 0 && x <= 1000);
                int sq = x * x;
                vtrace1(sq, x, y, sq);
                return sq;
            }
        """)
        eng = CSymEx(f, 4, check_overflow=True)
        eng.run()
        assert eng.safety_results == []

    def test_default_off(self, tmp_path):
        f = tmp_path / "prog.c"
        f.write_text(HEADER + """
            int mainQ(int x, int y){
                int sq = x * x;
                vtrace1(sq, x, y, sq);
                return sq;
            }
        """)
        eng = CSymEx(f, 4)
        eng.run()
        assert eng.safety_results == []


# ──────────────────────────────── expression parsing + houdini ──────

class TestParseAndHoudini:
    DIVIDER = HEADER + """
        int mainQ(int x, int y){
            vassume(x >= 0 && y >= 1);
            int q = 0;
            int r = x;
            while (r >= y) { r = r - y; q = q + 1; }
            vtrace1(q, r, x, y);
            return q;
        }
    """

    def test_parse_c_expr_matches_manual_z3(self, tmp_path):
        f = tmp_path / "prog.c"
        f.write_text(self.DIVIDER)
        eng = CSymEx(f, 2)
        parsed = eng.parse_c_expr("q*y + r == x")
        manual = X("q") * X("y") + X("r") == X("x")
        s = z3.Solver()
        s.add(parsed != manual)
        assert s.check() == z3.unsat   # logically identical

    def test_parse_c_expr_ternary_and_mod(self, tmp_path):
        f = tmp_path / "prog.c"
        f.write_text(self.DIVIDER)
        eng = CSymEx(f, 2)
        e = eng.parse_c_expr("(x > 0 ? x : -x) >= 0 && x % 2 != 2")
        assert z3.is_bool(e)
        assert eng.safety_results == []   # parsing must not record checks

    def test_houdini_keeps_inductive_subset(self, tmp_path):
        f = tmp_path / "prog.c"
        f.write_text(self.DIVIDER)
        eng = CSymEx(f, 2)
        good1 = eng.parse_c_expr("q*y + r == x")
        good2 = eng.parse_c_expr("q >= 0")
        good3 = eng.parse_c_expr("r >= 0")
        bad = eng.parse_c_expr("q <= 5")       # not preserved by the step
        kept = eng.houdini([good1, good2, good3, bad])
        kept_ids = {id(e) for e in kept}
        assert {id(good1), id(good2), id(good3)} <= kept_ids
        assert id(bad) not in kept_ids

    def test_houdini_empty_when_nothing_inductive(self, tmp_path):
        f = tmp_path / "prog.c"
        f.write_text(self.DIVIDER)
        eng = CSymEx(f, 2)
        assert eng.houdini([eng.parse_c_expr("q == 1")]) == []

    def test_cli_prove_and_houdini(self):
        prog = PROGS_DIR / "kinduction.c"
        ok = subprocess.run(
            [sys.executable, str(ENGINE_FILE), str(prog), "--depth", "2",
             "--prove", "q*y + r == x",
             "--check-inv", "vtrace1", "r >= 0",   # over vtrace1's params
             "--houdini", "q >= 0", "--houdini", "q <= 5"],
            capture_output=True, text=True)
        assert ok.returncode == 0, ok.stdout + ok.stderr
        assert "prove q*y + r == x: valid" in ok.stdout
        assert "check r >= 0 at vtrace1: valid" in ok.stdout
        assert "houdini q >= 0: kept (inductive)" in ok.stdout
        assert "houdini q <= 5: dropped" in ok.stdout

        bad = subprocess.run(
            [sys.executable, str(ENGINE_FILE), str(prog), "--depth", "2",
             "--prove", "q == 1"],
            capture_output=True, text=True)
        assert bad.returncode == 1
        assert "base-violated" in bad.stdout


# ───────────────────────────────────────────── preprocessing ────────

class TestPreprocessing:
    @pytest.mark.skipif(shutil.which("cpp") is None, reason="no cpp")
    def test_defines_are_expanded(self, tmp_path):
        f = tmp_path / "prog.c"
        f.write_text("#define FIVE 5\n" + HEADER + """
            int mainQ(int x, int y){
                int a = FIVE;
                vtrace1(a, x, y, a);
                return a;
            }
        """)
        _, res = CSymEx(f, 3), None
        eng = CSymEx(f, 3)
        res = eng.run()
        loc, pc, slocal = res[0]
        assert implied(pc, slocal, X("a") == 5)

    def test_directive_free_files_untouched_without_cpp(self, tmp_path):
        # no directives -> cpp never invoked -> works everywhere
        f = tmp_path / "prog.c"
        f.write_text(HEADER + """
            int mainQ(int x, int y){
                vtrace1(x, y, x, y);
                return 0;
            }
        """)
        assert len(CSymEx(f, 3).run()) == 1


# ─────────────────────────────────────── feature test programs ──────

PROGS_DIR = Path(__file__).parent / "symex_progs"
ENGINE_FILE = Path(__file__).parent.parent / "src" / "data" / "symex_c.py"


class TestFeaturePrograms:
    """
    Standalone .c programs in tests/symex_progs/, one per engine feature,
    self-checking via vassert. Programs named *_bad.c must produce at
    least one violated assertion (with a concrete counterexample);
    everything else must verify completely.
    """

    @pytest.mark.parametrize("cfile", sorted(PROGS_DIR.glob("*.c")),
                             ids=lambda p: p.stem)
    def test_program(self, cfile):
        if cfile.stem == "defines" and shutil.which("cpp") is None:
            pytest.skip("cpp not available")
        eng = CSymEx(cfile, 8, check_safety=True,
                     check_overflow="overflow" in cfile.stem)
        res = eng.run()
        assert res, "no vtrace records collected"
        combined = eng.assert_results + eng.safety_results
        assert combined, "feature programs must self-check"
        if cfile.stem.endswith("_bad"):
            violations = [a for a in combined if a.status == "violated"]
            assert violations
            for a in violations:
                assert a.cex, "violation must carry a counterexample"
        else:
            statuses = [a.status for a in eng.assert_results]
            assert statuses and all(s == "valid" for s in statuses), statuses
            bad_safety = [s for s in eng.safety_results
                          if s.status == "violated"]
            assert not bad_safety, bad_safety

    def test_unreached_program_reports_dead_vtrace(self):
        eng = CSymEx(PROGS_DIR / "unreached.c", 4)
        eng.run()
        assert eng.unreached_locs() == ["vtrace2"]

    def test_single_file_runs_standalone(self, tmp_path):
        # the engine is one dependency-free file: copy it anywhere and run it
        import shutil
        import subprocess
        engine = shutil.copy(ENGINE_FILE, tmp_path / "csymex.py")

        ok = subprocess.run(
            [sys.executable, engine, str(PROGS_DIR / "arrays.c"),
             "--depth", "8"], capture_output=True, text=True)
        assert ok.returncode == 0, ok.stderr
        assert "valid" in ok.stdout

        bad = subprocess.run(
            [sys.executable, engine, str(PROGS_DIR / "divider_bad.c"),
             "--depth", "6", "--gen-tests"], capture_output=True, text=True)
        assert bad.returncode == 1
        assert "counterexample" in bad.stdout
        assert "input reaching vtrace1" in bad.stdout


# ───────────────────────────────────────────── output contract ──────

class TestOutputContract:
    def test_records_are_loc_pc_slocal_boolrefs(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                vassume(x > 0);
                vtrace1(x, y, x, y);
                return 0;
            }
        """)
        loc, pc, slocal = res[0]
        assert loc == "vtrace1"
        assert isinstance(pc, z3.BoolRef)
        assert isinstance(slocal, z3.BoolRef)

    def test_unconstrained_path_has_true_pc(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                vtrace1(x, y, x, y);
                return 0;
            }
        """)
        _, pc, _ = res[0]
        assert z3.simplify(pc).eq(z3.BoolVal(True))

    def test_multiple_vtrace_locations(self, tmp_path):
        _, res = symex(tmp_path, """
            int mainQ(int x, int y){
                vtrace1(x, y, x, y);
                int a = x + 1;
                vtrace2(a, y, x, a);
                return 0;
            }
        """)
        assert [loc for loc, _, _ in res] == ["vtrace1", "vtrace2"]

    def test_deterministic_across_runs(self, tmp_path):
        src = HEADER + """
            int mainQ(int x, int y){
                vassume(x >= 1 && y >= 1);
                int q = 0;
                int r = x;
                while (r >= y) { r = r - y; q = q + 1; }
                vtrace1(q, r, x, y);
                return 0;
            }
        """
        f = tmp_path / "prog.c"
        f.write_text(src)

        def signature():
            return [(loc, str(pc), str(sl))
                    for loc, pc, sl in CSymEx(f, 4).run()]

        assert signature() == signature() == signature()

    def test_custom_solver_rlimit_is_applied(self, tmp_path):
        f = tmp_path / "prog.c"
        f.write_text(HEADER + "int mainQ(int x, int y){ vtrace1(x,y,x,y); return 0; }")
        eng = CSymEx(f, 3, solver_rlimit=1_000)
        assert eng.run()  # tiny rlimit: unknown feasibility keeps paths (optimistic)

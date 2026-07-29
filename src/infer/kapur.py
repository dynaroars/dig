"""
Bounded-degree polynomial invariant generation (Rodriguez-Carbonell & Kapur).

    In memory of Deepak Kapur (1950-2026), whose work on algebraic methods
    for program reasoning -- ideals, Groebner bases, and quantifier
    elimination -- is the foundation this module rests on.

This is a second *static* equality engine for DIG, algorithmically distinct
from infer/recurrence.py. Rather than solving recurrences to closed forms and
eliminating the loop counter, it computes the loop's **ideal of polynomial
invariants up to a degree bound d** directly, following:

    E. Rodriguez-Carbonell and D. Kapur, "Automatic generation of polynomial
    invariants of bounded degree using abstract interpretation", Science of
    Computer Programming 64(1), 2007; and "Generating all polynomial
    invariants in simple loops", J. Symbolic Computation 42(4), 2007.

Idea. A polynomial `p` of degree <= d is an invariant at the loop head iff it
vanishes on every reachable state. The reachable states are the orbit of the
loop's transition `tau` from the initial state: s_0, tau(s_0), tau^2(s_0), ...
Working over the finite-dimensional space of monomials of degree <= d, the
invariants are the polynomials `p = sum c_a * m_a` with `p(s_i) = 0` for all i.

Each `p(s_i)` is a polynomial in the program's *parameters* (the loop-invariant
inputs), so `p(s_i) = 0` means every parameter-monomial coefficient vanishes --
a homogeneous linear system in the unknown coefficients `c_a`. Its null space is
the degree-<= d invariant vector space (a Macaulay/evaluation-matrix view of the
bounded-degree invariant ideal). Because the space is finite-dimensional and the
orbit is symbolic (parameters kept as indeterminates), finitely many orbit
points determine it exactly -- the computation terminates. The resulting
invariants are returned as a **Groebner basis** (the canonical presentation of
the invariant ideal), then each is confirmed with DIG's k-induction/houdini
oracle before being reported PROVED.

The bounded degree is the price of termination on all solvable loops (including
geometric ones such as geo*): to capture a degree-k invariant, run with
`--deg k`. (The recurrence engine gets the exact degree for free but only on
loops with polynomial closed forms; the two engines are complementary.)

Run standalone:

    python -m infer.kapur ../benchmark/c/nla/ps2.c [--loop N] [--deg d]
"""

from __future__ import annotations

import itertools
import sys
from pathlib import Path

import sympy
import z3

from data.symex_c import CSymEx, _find_loops
from infer.recurrence import (
    RecurrenceInfer,
    _clear_denoms,
    _sympy_to_z3,
    _loop_head_vtrace,
)


def _monomials(variables: list, deg: int) -> list:
    """All monomials in `variables` of total degree 0..deg (1 first)."""
    monos = []
    for d in range(deg + 1):
        for combo in itertools.combinations_with_replacement(variables, d):
            m = sympy.Integer(1)
            for v in combo:
                m *= v
            monos.append(m)
    return monos


class KapurInfer:
    """Bounded-degree invariant ideal via the reachable-state null space."""

    N_EXTRA_POINTS = 4      # orbit points beyond #monomials, for a safe rank

    def __init__(self, filename: Path, depth: int = 5) -> None:
        self.rec = RecurrenceInfer(filename, depth)   # reuse symex extraction
        self.engine = self.rec.engine

    def invariant_ideal(self, loop: int = 0, deg: int = 2):
        """Groebner basis of the degree-<= deg polynomial invariant ideal at
        the loop head, plus (dynamic vars, params). Raises ValueError if the
        loop body is not a single polynomial map."""
        variables, init, update = self.rec.extract(loop)
        S = {v: sympy.Symbol(v) for v in variables}

        dynamic = [v for v in variables
                   if sympy.expand(update[v] - S[v]) != 0]
        params = [v for v in variables if v not in dynamic]
        if not dynamic:
            raise ValueError("loop has no state change")

        allvars = [S[v] for v in variables]
        psyms = [S[v] for v in params]

        # symbolic orbit: s_0 = init, s_{i+1} = tau(s_i); each coordinate is a
        # polynomial in the parameters (kept as indeterminates)
        def tau_step(state: dict) -> dict:
            sub = {S[w]: state[w] for w in variables}
            return {v: sympy.expand(update[v].xreplace(sub)) for v in variables}

        state = {v: sympy.expand(sympy.sympify(init[v])) for v in variables}
        orbit = [state]

        monos = _monomials(allvars, deg)
        # With no parameters each orbit point gives one linear equation, so we
        # need ~#monomials points. With parameters, one point gives many
        # equations (one per parameter-monomial), so a few points suffice --
        # and capping them is essential: a geometric orbit's coordinates grow
        # to degree i in the parameters after i steps, so many points would
        # blow up. houdini drops any spurious candidate from using few points.
        n_points = len(monos) + self.N_EXTRA_POINTS
        if psyms:
            n_points = min(n_points, 3 * deg + 3)
        for _ in range(n_points):
            state = tau_step(state)
            orbit.append(state)

        # linear constraints: p(s_i) = 0 for every orbit point, split into one
        # equation per parameter-monomial (p(s_i) is a polynomial in params)
        rows: list[list] = []
        for state in orbit:
            sub = {S[w]: state[w] for w in variables}
            evals = [sympy.expand(m.xreplace(sub)) for m in monos]
            if psyms:
                dicts = [sympy.Poly(e, *psyms).as_dict() if e != 0 else {}
                         for e in evals]
                pmons = set().union(*dicts) if dicts else set()
                for pm in pmons:
                    rows.append([sympy.Rational(d.get(pm, 0)) for d in dicts])
            else:
                rows.append([sympy.Rational(e) for e in evals])  # e is numeric

        null = sympy.Matrix(rows).nullspace()

        invs = []
        for vec in null:
            p = sympy.expand(sum(vec[a] * monos[a] for a in range(len(monos))))
            if p == 0 or p.is_number:
                continue
            invs.append(_clear_denoms(p, sorted(p.free_symbols, key=str)))

        # canonical presentation of the invariant ideal
        if invs:
            gb = sympy.groebner(invs, *allvars, order="grevlex")
            invs = [sympy.expand(g) for g in gb.exprs if not g.is_number]
        return invs, dynamic, params

    def gen(self, loop: int = 0, deg: int = 2):
        """(invariant generators, verified results). The bounded-degree null
        space is sound by construction; each generator is still confirmed with
        houdini (k-induction), matching the recurrence engine's contract."""
        invs, _dyn, _par = self.invariant_ideal(loop, deg)
        z3invs = [_sympy_to_z3(p) == 0 for p in invs]
        kept = self.engine.houdini(z3invs, loop=loop)
        kept_strs = {str(z3.simplify(e)) for e in kept}
        results = [(p, "valid" if str(z3.simplify(z)) in kept_strs
                    else "not-inductive")
                   for p, z in zip(invs, z3invs)]
        return results


# ────────────────────────────────── DIG integration entry point ──

def gen_all(filename: Path, depth: int = 5, max_deg: int = 3):
    """{loc: [Eqt, ...]} proved equality invariants per loop-head vtrace,
    computed by the RC-Kapur bounded-degree method. Each loop is tried at
    increasing degree bounds (up to max_deg) and the richest proved set is
    kept. Loops that aren't single polynomial maps are skipped."""
    import infer.eqt
    import infer.inv

    probe = CSymEx(filename, depth)
    probe._parse()
    loops = _find_loops(probe.func_bodies["mainQ"])

    out: dict[str, list] = {}
    for i, node in enumerate(loops):
        loc = _loop_head_vtrace(node)
        if loc is None:
            continue
        best: list = []
        for deg in range(2, max_deg + 1):
            try:
                results = KapurInfer(filename, depth).gen(i, deg)
            except Exception:
                continue
            proved = [p for p, s in results if s == "valid"]
            if len(proved) > len(best):
                best = proved
        eqts = []
        for poly in best:
            eqt = infer.eqt.Eqt(sympy.Eq(poly, sympy.Integer(0)))
            eqt.set_stat(infer.inv.Inv.PROVED)
            eqts.append(eqt)
        if eqts:
            out.setdefault(loc, []).extend(eqts)
    return out


# ────────────────────────────────────────────────────────── CLI ──

def main() -> None:
    import argparse

    ap = argparse.ArgumentParser(description=__doc__.splitlines()[1])
    ap.add_argument("file", type=Path)
    ap.add_argument("--loop", type=int, default=0)
    ap.add_argument("--depth", type=int, default=5)
    ap.add_argument("--deg", type=int, default=2,
                    help="max total degree of invariants (default 2)")
    args = ap.parse_args()

    inf = KapurInfer(args.file, args.depth)
    try:
        results = inf.gen(args.loop, args.deg)
    except (ValueError, NotImplementedError) as ex:
        print(f"declined: {ex}")
        sys.exit(2)

    print(f"invariant ideal, degree <= {args.deg} "
          "(RC-Kapur bounded-degree, verified by k-induction):")
    if not results:
        print("    (none)")
    for p, status in results:
        mark = "PROVED" if status == "valid" else status
        print(f"    {p} == 0    [{mark}]")


if __name__ == "__main__":
    main()

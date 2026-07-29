"""
Static (recurrence-based) equality-invariant generation for DIG.

This is the *static* counterpart to infer/eqt.py. Where eqt.py guesses a
polynomial template and fits it to concrete traces (dynamic analysis), this
module reads the loop's transition relation directly and *solves* for the
invariants:

    loop body  --(symbolic execution, one iteration)-->  update map
               --(z3 -> sympy, rsolve)---------------->  closed forms  x(n)=...
               --(eliminate the counter n, Groebner)-->  polynomial equalities
               --(prove_inductive, k-induction)-------->  SOUND invariants

No program is ever run and no traces are collected. Generation is purely
algebraic and verification is unbounded (k-induction), so a "valid" result is
a genuine loop invariant, not one that merely held up to some unroll depth.

Scope of this prototype: single loops whose continue-path body is a
straight-line polynomial (affine, in the benchmarks) update, i.e. the classic
"solvable loop" class that covers most of DIG's NLA power-sum/geo benchmarks
(ps2..ps6, geo*, cohencu, ...). Branching bodies (piecewise recurrences) and
loops with no closed form fall back to DIG's dynamic engine -- this module
just declines them.

Run standalone:

    python -m infer.recurrence ../benchmark/c/nla/ps2.c [--loop N] [--depth N]
"""

from __future__ import annotations

import sys
from pathlib import Path

import sympy
import z3

from pycparser import c_ast

import settings

from data.symex_c import (
    CSymEx,
    Exit,
    SymState,
    _as_bool,
    _find_loops,
    _loop_cond_body,
)


# ────────────────────────────────────────────── name normalisation ──

def _base_name(z3name: str) -> str:
    """Program-variable name behind an internal symbol.

    The symex engine names symbols _rec_x (our havoc), _ind_x (induction),
    _uninit_x (uninitialised locals) and X_x (mainQ inputs). They all refer
    to the same program variable x -- collapse them so the recurrence and the
    initial condition talk about the same sympy symbol.
    """
    for prefix in ("_rec_", "_ind_", "_uninit_", "X_"):
        if z3name.startswith(prefix):
            return z3name[len(prefix):]
    return z3name


# ───────────────────────────────────────────────── z3  ->  sympy ──

def _z3_to_sympy(e: z3.ExprRef) -> sympy.Expr:
    """Translate an integer/rational z3 arithmetic expression to sympy.

    Only the operators the solvable-loop class produces are handled
    (+ - * unary-minus, integer/rational literals, and constants). Anything
    else (div, mod, if-then-else from a branch) raises NotImplementedError so
    the caller can decline the loop rather than emit a wrong recurrence.
    """
    if z3.is_int_value(e):
        return sympy.Integer(e.as_long())
    if z3.is_rational_value(e):
        return sympy.Rational(e.numerator_as_long(), e.denominator_as_long())
    if z3.is_const(e):                       # a variable / uninterpreted const
        return sympy.Symbol(_base_name(str(e)))

    if z3.is_add(e):
        return sympy.Add(*[_z3_to_sympy(c) for c in e.children()])
    if z3.is_mul(e):
        return sympy.Mul(*[_z3_to_sympy(c) for c in e.children()])
    if z3.is_sub(e):
        cs = [_z3_to_sympy(c) for c in e.children()]
        return cs[0] - sympy.Add(*cs[1:])

    decl = e.decl().kind()
    if decl == z3.Z3_OP_UMINUS:
        return -_z3_to_sympy(e.children()[0])
    if decl == z3.Z3_OP_POWER:
        b, p = e.children()
        return _z3_to_sympy(b) ** _z3_to_sympy(p)

    raise NotImplementedError(f"z3->sympy: unsupported {e.sexpr()}")


def _sympy_to_z3(e: sympy.Expr) -> z3.ExprRef:
    """Translate an integer-coefficient polynomial sympy expr to a z3 Int expr
    over program-variable names (z3.Int('x') etc.)."""
    e = sympy.expand(e)
    if e.is_Integer:
        return z3.IntVal(int(e))
    if e.is_Symbol:
        return z3.Int(e.name)
    if e.is_Add:
        return z3.Sum(*[_sympy_to_z3(t) for t in e.args])
    if e.is_Mul:
        out = None
        for f in e.args:
            z = _sympy_to_z3(f)
            out = z if out is None else out * z
        return out
    if e.is_Pow:
        base, exp = e.args
        assert exp.is_Integer and int(exp) >= 1, e
        out = _sympy_to_z3(base)
        for _ in range(int(exp) - 1):
            out = out * _sympy_to_z3(base)
        return out
    raise NotImplementedError(f"sympy->z3: unsupported {e!r}")


def _clear_denoms(e: sympy.Expr, gens: list[sympy.Symbol]) -> sympy.Expr:
    """Scale a rational-coefficient polynomial to integer coefficients."""
    poly = sympy.Poly(sympy.expand(e), *gens)
    denoms = [c.q for c in poly.coeffs()]        # rationals -> denominators
    mult = sympy.ilcm(*denoms) if denoms else 1
    return sympy.expand(e * mult)


# ─────────────────────────────────────── extract the update map ──

class RecurrenceInfer:
    def __init__(self, filename: Path, depth: int = 5) -> None:
        self.engine = CSymEx(filename, depth)

    def _int_vars(self, env: dict[str, z3.ExprRef]) -> list[str]:
        return [v for v, val in env.items()
                if z3.is_int(val) or (z3.is_const(val) and val.sort() == z3.IntSort())
                or z3.is_arith(val) and not val.sort() == z3.RealSort()]

    def extract(self, loop: int = 0):
        """Return (pre_env, init, update) for the given loop:

          pre_env  : loop-head variable names (int scalars)
          init     : {v: sympy init value at loop entry}
          update   : {v: sympy expr for v after one continue-path iteration},
                     in terms of the loop-head symbols.

        Raises ValueError if the loop head is unreachable or the body's
        continue path is not a single straight-line state (piecewise update).
        """
        eng = self.engine
        node, entry = eng._loop_target(loop)
        if not entry:
            raise ValueError(f"loop #{loop} head unreachable")
        env0 = entry[0].env
        variables = [v for v in env0 if z3.is_arith(env0[v])
                     and env0[v].sort() == z3.IntSort()]

        cond_node, body, nxt = _loop_cond_body(node)

        # Havoc one iteration: fresh symbol per loop var, assume the loop
        # guard, run the body, keep the continue (loop-back) path.
        presym = {v: z3.Int(f"_rec_{v}") for v in variables}
        havoc = SymState(env={**env0, **presym})

        saved = (eng.records, eng.assert_results, eng.safety_results)
        eng.records, eng.assert_results, eng.safety_results = [], [], []
        eng._hypothetical = True
        try:
            graw, h = eng._eval_expr_effects(cond_node, havoc)
            h = h.add_constraint(_as_bool(graw))
            post = eng._after_body(eng._exec_compound(body, [h]), nxt)
        finally:
            eng._hypothetical = False
            eng.records, eng.assert_results, eng.safety_results = saved

        loops_back = [s for s in post if s.exit == Exit.NORMAL]
        if len(loops_back) != 1:
            raise ValueError(
                f"loop #{loop} body is not straight-line "
                f"({len(loops_back)} continue paths; piecewise recurrence)")
        post_env = loops_back[0].env

        init = {v: _z3_to_sympy(env0[v]) for v in variables}
        update = {v: _z3_to_sympy(post_env[v]) for v in variables}
        return variables, init, update

    def extract_paths(self, loop: int = 0):
        """Multi-path (CRA-style) variant of extract().

        A branching loop body has several continue paths, each with its own
        straight-line update map. Return (variables, init, [update, ...]) with
        one update map per continue path whose body is polynomial (paths with
        division/mod/if-terms that z3->sympy can't render are dropped). Paths
        keep only their variable *updates*, not their branch guards: each is fed
        to solve()/eliminate() as if it were the whole loop, producing candidate
        equalities that houdini then filters against the real (all-paths) loop.
        So generation is per-path and heuristic; soundness comes from the joint
        k-induction check in gen_multipath(), exactly as in the single-path gen().

        Raises ValueError if the head is unreachable or no polynomial continue
        path exists (nothing for the multi-path engine to work with).
        """
        eng = self.engine
        node, entry = eng._loop_target(loop)
        if not entry:
            raise ValueError(f"loop #{loop} head unreachable")
        env0 = entry[0].env
        variables = [v for v in env0 if z3.is_arith(env0[v])
                     and env0[v].sort() == z3.IntSort()]

        cond_node, body, nxt = _loop_cond_body(node)

        presym = {v: z3.Int(f"_rec_{v}") for v in variables}
        havoc = SymState(env={**env0, **presym})

        saved = (eng.records, eng.assert_results, eng.safety_results)
        eng.records, eng.assert_results, eng.safety_results = [], [], []
        eng._hypothetical = True
        try:
            graw, h = eng._eval_expr_effects(cond_node, havoc)
            h = h.add_constraint(_as_bool(graw))
            post = eng._after_body(eng._exec_compound(body, [h]), nxt)
        finally:
            eng._hypothetical = False
            eng.records, eng.assert_results, eng.safety_results = saved

        loops_back = [s for s in post if s.exit == Exit.NORMAL]
        if not loops_back:
            raise ValueError(f"loop #{loop}: no continue path")

        init = {v: _z3_to_sympy(env0[v]) for v in variables}
        updates = []
        for s in loops_back:
            try:
                upd = {v: _z3_to_sympy(s.env[v]) for v in variables}
            except NotImplementedError:
                continue        # this path uses div/mod/ite: not polynomial
            updates.append(upd)
        if not updates:
            raise ValueError(f"loop #{loop}: no polynomial continue path")
        return variables, init, updates

    # ───────────────────────────────────── solve the recurrences ──

    def solve(self, variables, init, update):
        """Closed forms {v: g_v(n)} by topological rsolve. Variables whose
        update equals themselves are loop constants (parameters); they get no
        recurrence and appear as free sympy symbols."""
        # counter symbol must not collide with a program variable literally
        # named n (e.g. cohencu), so pick a fresh name
        ctr = "n"
        while ctr in variables:
            ctr = "_" + ctr
        n = sympy.Symbol(ctr, integer=True, nonnegative=True)
        S = {v: sympy.Symbol(v) for v in variables}

        updated = [v for v in variables
                   if sympy.expand(update[v] - S[v]) != 0]
        upd_set = set(updated)

        # dependency edges v <- w (w != v, w updated) if S[w] occurs in update[v]
        deps = {v: {w for w in upd_set if w != v
                    and S[w] in update[v].free_symbols}
                for v in updated}

        order, seen = [], set()

        def visit(v, stack):
            if v in seen:
                return
            if v in stack:
                raise ValueError(f"coupled recurrence through {v} "
                                 "(cyclic dependency; matrix solve needed)")
            for w in deps[v]:
                visit(w, stack | {v})
            seen.add(v)
            order.append(v)

        for v in updated:
            visit(v, set())

        closed = {}
        for v in order:
            f = sympy.Function(f"_f_{v}")
            subs = {}
            for w in upd_set:
                if w == v:
                    subs[S[w]] = f(n - 1)
                elif w in closed:
                    subs[S[w]] = closed[w].subs(n, n - 1)
                # else w is a not-yet/never-updated symbol: leave as-is
            rhs = update[v].subs(subs, simultaneous=True)
            sol = sympy.rsolve(f(n) - rhs, f(n), {f(0): init[v]})
            if sol is None:
                raise ValueError(f"rsolve failed for {v}")
            closed[v] = sympy.expand(sol)
        return n, S, updated, closed

    # ───────────────────────────────────── eliminate the counter ──

    def eliminate(self, n, S, updated, closed):
        """Polynomial equalities among the program variables.

        Pure-polynomial closed forms (ps*, cohencu) are handled directly by
        eliminating the counter n. Geometric/exponential closed forms (geo*,
        where a variable is multiplied by a base each iteration) contain
        base**(a*n+b) terms -- the P-solvable case. For each distinct base we
        introduce an auxiliary variable T = base**n, rewrite base**(a*n+b) as
        base**b * T**a, add the multiplicative relations among numeric bases,
        and eliminate n *and* the T's. The base may be a program variable
        (e.g. geo1's z), so the resulting invariant is still polynomial in the
        program variables (geo1: x*z - x - y + 1 = 0).
        """
        # discover exponential bases: Pow nodes whose exponent involves n
        base_to_T: dict[sympy.Expr, sympy.Symbol] = {}
        rewrites: dict[sympy.Expr, sympy.Expr] = {}
        for v in updated:
            for p in sympy.preorder_traversal(closed[v]):
                if not (p.is_Pow and p.exp.has(n)):
                    continue
                base, exp = p.base, p.exp
                if base.has(n):
                    raise ValueError("nested exponential (base depends on n)")
                a, b = self._linear_in(exp, n)
                if a is None or a <= 0:
                    raise ValueError(f"non-affine/decreasing exponent {exp}")
                T = base_to_T.get(base)
                if T is None:
                    T = sympy.Symbol(f"_T{len(base_to_T)}")
                    base_to_T[base] = T
                rewrites[p] = base ** b * T ** a

        T_syms = list(base_to_T.values())
        closed_r = {v: (closed[v].xreplace(rewrites) if rewrites else closed[v])
                    for v in updated}

        elim = [n] + T_syms                       # variables to project out
        # numerators of {v - closed_v}: clears both rational-function
        # denominators (e.g. 1/(z-1)) and any T**-a from negative shifts
        allsyms = set(elim) | {S[v] for v in updated}
        for v in updated:
            allsyms |= closed_r[v].free_symbols
        gens = elim + sorted(allsyms - set(elim), key=str)

        # numerator of {v - closed_v}: clears rational-number coefficients
        # (ps: n**2/2) *and* rational-function denominators (geo: 1/(z-1)) in
        # one step, leaving an integer/coefficient polynomial equation
        eqs = [sympy.fraction(sympy.together(S[v] - closed_r[v]))[0]
               for v in updated]
        eqs = [sympy.expand(e) for e in eqs]
        eqs += self._base_relations(base_to_T)

        basis = sympy.groebner(eqs, *gens, order="lex")
        elim_set = set(elim)
        cands = [sympy.expand(g) for g in basis.exprs
                 if not (g.free_symbols & elim_set)]   # n and all T eliminated
        return cands

    @staticmethod
    def _linear_in(exp: sympy.Expr, n: sympy.Symbol):
        """(a, b) for exp == a*n + b with integer a, b; (None, None) otherwise."""
        poly = sympy.Poly(exp, n)
        if poly.degree() > 1:
            return None, None
        a = poly.nth(1)
        b = poly.nth(0)
        if not (a.is_Integer and b.is_Integer):
            return None, None
        return int(a), int(b)

    @staticmethod
    def _base_relations(base_to_T: dict) -> list:
        """Multiplicative relations among numeric exponential bases.

        If numeric bases b_i satisfy prod b_i**e_i = 1 for integers e_i, then
        their auxiliaries satisfy prod T_i**e_i = 1 (e.g. bases 2 and 4 give
        T_4 = T_2**2). Found via the integer left-null space of the
        prime-exponent matrix. Symbolic bases (geo's z) are assumed
        multiplicatively independent, so contribute no relation.
        """
        numeric = [(sympy.Rational(b), T) for b, T in base_to_T.items()
                   if b.is_number]
        if len(numeric) < 2:
            return []
        primes: list = []
        for b, _T in numeric:
            for p in sympy.factorint(b):
                if p not in primes:
                    primes.append(p)
        M = sympy.zeros(len(numeric), len(primes))
        for i, (b, _T) in enumerate(numeric):
            for p, e in sympy.factorint(b).items():
                M[i, primes.index(p)] = e
        rels = []
        for vec in M.T.nullspace():                 # e with e^T M = 0
            denom = sympy.ilcm(*[c.q for c in vec]) or 1
            e = [int(c * denom) for c in vec]
            pos = sympy.Mul(*[numeric[i][1] ** e[i]
                              for i in range(len(e)) if e[i] > 0])
            neg = sympy.Mul(*[numeric[i][1] ** (-e[i])
                              for i in range(len(e)) if e[i] < 0])
            rels.append(sympy.expand(pos - neg))
        return rels

    # ───────────────────────────────────────────── full pipeline ──

    def gen(self, loop: int = 0):
        variables, init, update = self.extract(loop)
        n, S, updated, closed = self.solve(variables, init, update)
        cands = []
        for p in self.eliminate(n, S, updated, closed):
            if p == 0:
                continue
            # groebner may return rational coefficients (esp. with symbolic
            # exponential bases); clear to an integer polynomial for z3
            cands.append(_clear_denoms(p, sorted(p.free_symbols, key=str)))

        # Verify the whole set jointly with houdini: these equalities are
        # typically mutually (not individually) inductive -- e.g. 2x = c^2+c
        # holds only given y = c -- so proving them one at a time by
        # 1-induction spuriously rejects the interdependent ones.
        invs = [_sympy_to_z3(p) == 0 for p in cands]
        kept = self.engine.houdini(invs, loop=loop)
        kept_strs = {str(z3.simplify(e)) for e in kept}
        results = [(p, "valid" if str(z3.simplify(inv)) in kept_strs
                    else "not-inductive")
                   for p, inv in zip(cands, invs)]
        return closed, results

    def gen_multipath(self, loop: int = 0):
        """Multi-path pipeline for branching loops (the CRA-style extension).

        For each continue path, solve its update as a standalone recurrence and
        eliminate the counter to candidate equalities (declining paths that
        aren't solvable). Pool the candidates across all paths, de-duplicate,
        then keep the subset that is *jointly* inductive over the real
        multi-path loop with houdini (k-induction). Because verification uses
        the true loop (all paths, real guards), the result is sound even though
        candidate generation pretends each path runs in isolation.

        Returns a list of (poly, status) like gen()'s second element; poly == 0
        entries are dropped. Raises if there is no usable continue path.
        """
        variables, init, updates = self.extract_paths(loop)

        cands, seen = [], set()
        for update in updates:
            try:
                n, S, updated, closed = self.solve(variables, init, update)
                polys = self.eliminate(n, S, updated, closed)
            except (ValueError, NotImplementedError):
                continue        # this path is not a solvable recurrence
            for p in polys:
                if p == 0:
                    continue
                p = _clear_denoms(p, sorted(p.free_symbols, key=str))
                key = str(sympy.expand(p))
                if key not in seen:
                    seen.add(key)
                    cands.append(p)

        if not cands:
            return []

        invs = [_sympy_to_z3(p) == 0 for p in cands]
        kept = self.engine.houdini(invs, loop=loop)
        kept_strs = {str(z3.simplify(e)) for e in kept}
        return [(p, "valid" if str(z3.simplify(inv)) in kept_strs
                 else "not-inductive")
                for p, inv in zip(cands, invs)]


# ────────────────────────────────── DIG integration entry point ──

def _loop_head_vtrace(node: c_ast.Node) -> str | None:
    """The vtrace loc observed at this loop's head: the first vtraceN call in
    the loop body, not descending into nested loops (whose vtrace belongs to
    them). Returns None if the loop has no observation point."""
    body = node.stmt
    found: list[str] = []

    class _V(c_ast.NodeVisitor):
        def visit_FuncCall(self, n):
            if (not found and isinstance(n.name, c_ast.ID)
                    and n.name.name.startswith("vtrace")):
                found.append(n.name.name)

        def visit_While(self, n):
            pass                       # a nested loop's vtrace is not ours

        def visit_For(self, n):
            pass

    _V().visit(body)
    return found[0] if found else None


def gen_all(filename: Path, depth: int = 5, multipath: bool | None = None):
    """Proved equality invariants per loop-head vtrace location, as DIG Eqt
    objects: {loc: [Eqt, ...]}.

    This is the entry point DIG's pipeline (alg.py) calls. Each loop is tried
    independently; loops that are not solvable single-path recurrences (or
    whose closed forms yield no polynomial relation) are skipped silently, so
    the dynamic engine remains responsible for them. Every returned Eqt has
    already been proved by unbounded k-induction (houdini), so it is marked
    PROVED and needs no trace checking.

    When ``multipath`` is on (defaults to settings.DO_RECURRENCE_MP), loops the
    single-path engine declines (branching bodies: egcd/fermat/prodbin) are
    retried with the multi-path pipeline before falling back to the dynamic
    engine.
    """
    import infer.eqt
    import infer.inv

    if multipath is None:
        multipath = settings.DO_RECURRENCE_MP

    probe = CSymEx(filename, depth)
    probe._parse()
    loops = _find_loops(probe.func_bodies["mainQ"])

    out: dict[str, list] = {}
    for i, node in enumerate(loops):
        loc = _loop_head_vtrace(node)
        if loc is None:
            continue
        results = None
        try:
            _closed, results = RecurrenceInfer(filename, depth).gen(i)
        except Exception:
            results = None             # decline: not a solvable single loop
        if results is None and multipath:
            try:
                results = RecurrenceInfer(filename, depth).gen_multipath(i)
            except Exception:
                results = None         # decline: no usable multi-path either
        if not results:
            continue
        eqts = []
        for poly, status in results:
            if status != "valid":
                continue
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
    ap.add_argument("--multipath", action="store_true",
                    help="use the multi-path pipeline (branching loop bodies)")
    args = ap.parse_args()

    infer = RecurrenceInfer(args.file, args.depth)
    closed = {}
    try:
        if args.multipath:
            results = infer.gen_multipath(args.loop)
        else:
            closed, results = infer.gen(args.loop)
    except (ValueError, NotImplementedError) as ex:
        print(f"declined: {ex}")
        sys.exit(2)

    if closed:
        print("closed forms (n = iteration count at the loop head):")
        for v, g in closed.items():
            print(f"    {v}(n) = {g}")

    print("candidate equalities (verified by unbounded k-induction):")
    if not results:
        print("    (none)")
    for p, status in results:
        mark = "PROVED" if status == "valid" else status
        print(f"    {p} == 0    [{mark}]")


if __name__ == "__main__":
    main()

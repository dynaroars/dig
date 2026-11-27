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


import sys
from pathlib import Path

import sympy
import z3

from pycparser import c_ast

import settings
import helpers.vcommon as CM

from data.symex_c import (
    CSymEx,
    Exit,
    SymState,
    _as_bool,
    _find_loops,
    _loop_cond_body,
)

mlog = CM.getLogger(__name__, settings.LOGGER_LEVEL)


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
    mult = sympy.ilcm(*denoms, 1)                # ilcm needs >= 2 args
    return sympy.expand(e * mult)


def _canon_radicals(expr: sympy.Expr) -> sympy.Expr:
    """Expand bases of fractional powers so sqrt((t-1)*(t+1)) == sqrt(t**2-1)."""
    return expr.replace(
        lambda e: e.is_Pow and e.exp.is_Rational and not e.exp.is_Integer,
        lambda e: sympy.Pow(sympy.expand(e.base), e.exp),
    )


def _tarjan_sccs(nodes: list[str], deps: dict[str, set[str]]) -> list[list[str]]:
    """Strongly connected components of `nodes` in dependency-first order."""
    index = 0
    indices: dict[str, int] = {}
    lowlink: dict[str, int] = {}
    stack: list[str] = []
    on_stack: set[str] = set()
    sccs: list[list[str]] = []

    def strongconnect(v: str) -> None:
        nonlocal index
        indices[v] = lowlink[v] = index
        index += 1
        stack.append(v)
        on_stack.add(v)
        for w in sorted(deps.get(v, ())):
            if w not in indices:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], indices[w])
        if lowlink[v] == indices[v]:
            comp = []
            while True:
                w = stack.pop()
                on_stack.remove(w)
                comp.append(w)
                if w == v:
                    break
            sccs.append(comp)

    for v in nodes:
        if v not in indices:
            strongconnect(v)
    return sccs


def _expand_candidates(polys: list[sympy.Expr],
                       updated_syms: set[sympy.Symbol]) -> list[sympy.Expr]:
    """Clear denominators and split out irreducible factors involving updated vars.

    Clearing symbolic radical denominators (e.g. sqrt(t**2 - 1) in Chebyshev)
    can multiply the true invariant by a parameter-only factor like (t**2 - 1).
    Proposing both irreducible factors and the square-free polynomial lets
    houdini prove the cleanest factor while preserving composite invariants
    like Cassini's (a**2 + a*b - b**2)**2 - 1 == 0.
    """
    out: list[sympy.Expr] = []
    seen: set[str] = set()

    def _add(expr: sympy.Expr) -> None:
        if expr == 0 or not expr.free_symbols:
            return
        expr = _clear_denoms(expr, sorted(expr.free_symbols, key=str))
        terms = expr.as_ordered_terms()
        if terms and terms[0].as_coeff_Mul()[0] < 0:
            expr = sympy.expand(-expr)
        key = str(expr)
        if key not in seen:
            seen.add(key)
            out.append(expr)

    for p in polys:
        if p == 0 or not p.free_symbols:
            continue
        p = _clear_denoms(p, sorted(p.free_symbols, key=str))
        try:
            _coeff, factors = sympy.factor_list(p)
        except Exception:
            _add(p)
            continue
        if len(factors) > 1 or any(exp > 1 for _, exp in factors):
            sqf = sympy.Integer(1)
            for f, _exp in factors:
                sqf = sympy.expand(sqf * f)
                if f.free_symbols & updated_syms:
                    _add(f)
            _add(sqf)
        else:
            _add(p)
    return out


def _prune_divisible(results: list[tuple[sympy.Expr, str]]
                     ) -> list[tuple[sympy.Expr, str]]:
    """Drop any proved polynomial that is a strict multiple of another proved one."""
    valid = [p for p, st in results if st == "valid"]
    if len(valid) < 2:
        return results
    drop: set[str] = set()
    for p in valid:
        for q in valid:
            if p == q:
                continue
            if not (q.free_symbols <= p.free_symbols):
                continue
            try:
                _quo, rem = sympy.div(p, q, domain="QQ")
                if rem == 0:
                    drop.add(str(p))
                    break
            except Exception:
                continue
    return [(p, st) for p, st in results if not (st == "valid" and str(p) in drop)]


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

        init, update, dropped = self._extract_poly_maps(variables, env0, post_env)
        if not update:
            raise ValueError(f"loop #{loop}: no polynomial variable updates")
        kept_vars = [v for v in variables if v not in dropped]
        return kept_vars, init, update

    @staticmethod
    def _extract_poly_maps(variables: list[str], env0: dict, post_env: dict):
        """Translate init/update maps for variables whose updates are polynomial.

        Auxiliary variables with non-polynomial updates (e.g. `path = path / 3`
        used only to select branches) are dropped; solve() drops any variable
        that depends on them, and houdini verifies all results on the full loop.
        """
        init, update, dropped = {}, {}, set()
        for v in variables:
            try:
                iv = _z3_to_sympy(env0[v])
                uv = _z3_to_sympy(post_env[v])
            except NotImplementedError:
                dropped.add(v)
                continue
            init[v] = iv
            update[v] = uv
        return init, update, dropped

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

        paths = []
        for s in loops_back:
            init, upd, dropped = self._extract_poly_maps(variables, env0, s.env)
            kept_vars = [v for v in variables if v not in dropped]
            if upd:
                paths.append((kept_vars, init, upd))
        if not paths:
            raise ValueError(f"loop #{loop}: no polynomial continue path")
        return paths

    # ───────────────────────────────────── solve the recurrences ──

    def solve(self, variables, init, update):
        """Closed forms {v: g_v(n)} by topological rsolve, plus the fresh
        initial-value symbols introduced (to be eliminated alongside the
        counter). Variables whose update equals themselves are loop constants
        (parameters); they get no recurrence and appear as free sympy symbols.
        """
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

        # An updated variable's symbol in an init value denotes its *initial*
        # value, not the loop-head value (a loop that updates its own input,
        # e.g. `while (n > 0) { s += n; n--; }`, hits this). Give those a
        # fresh symbol so the recurrence doesn't alias v(0) with v(n); the
        # caller eliminates them like the counter.
        initsyms = {S[w]: sympy.Symbol(f"_init_{w}") for w in updated
                    if any(S[w] in init[v].free_symbols for v in variables)}
        init = {v: init[v].xreplace(initsyms) for v in variables}

        # dependency edges v <- w (w != v, w updated) if S[w] occurs in update[v]
        # Drop any updated variable whose update mentions a symbol outside S
        # (i.e. a non-polynomial auxiliary variable dropped during extraction).
        known_syms = set(S.values())
        unsolvable = {v for v in updated
                      if not (update[v].free_symbols <= known_syms)}
        changed = True
        while changed:
            changed = False
            for v in updated:
                if v in unsolvable:
                    continue
                if any(S[w] in update[v].free_symbols for w in unsolvable):
                    unsolvable.add(v)
                    changed = True

        solvable = [v for v in updated if v not in unsolvable]
        if not solvable:
            raise ValueError("no solvable polynomial recurrence variables")
        solv_set = set(solvable)

        deps = {v: {w for w in solv_set if w != v
                    and S[w] in update[v].free_symbols}
                for v in solvable}

        sccs = _tarjan_sccs(solvable, deps)
        closed: dict[str, sympy.Expr] = {}
        for comp in sccs:
            if len(comp) == 1:
                v = comp[0]
                f = sympy.Function(f"_f_{v}")
                subs = {}
                for w in solv_set:
                    if w == v:
                        subs[S[w]] = f(n - 1)
                    elif w in closed:
                        subs[S[w]] = closed[w].subs(n, n - 1)
                rhs = update[v].subs(subs, simultaneous=True)
                sol = sympy.rsolve(f(n) - rhs, f(n), {f(0): init[v]})
                if sol is None:
                    raise ValueError(f"rsolve failed for {v}")
                closed[v] = sympy.expand(sol)
            else:
                scc_closed = self._solve_linear_scc(
                    comp, init, update, S, closed, n)
                closed.update(scc_closed)
        return n, S, solvable, closed, list(initsyms.values())

    @staticmethod
    def _solve_linear_scc(comp: list[str], init: dict, update: dict,
                          S: dict[str, sympy.Symbol], closed: dict,
                          n: sympy.Symbol) -> dict[str, sympy.Expr]:
        """Solve a coupled affine recurrence SCC v(n+1) = A*v(n) + b via Jordan form.

        Supports numeric and symbolic loop-constant matrices (e.g. Pell,
        Fibonacci, Chebyshev, Berggren), both diagonalizable and Jordan-block
        systems. Nonlinear coupled updates (e.g. Nagata, Markov) are declined.
        """
        k = len(comp)
        if k > 4:
            raise ValueError(f"coupled recurrence SCC too large ({k} vars)")
        comp_syms = [S[v] for v in comp]
        comp_sym_set = set(comp_syms)

        # Substitute already-solved upstream variables
        upstream_subs = {S[w]: closed[w].subs(n, n - 1) for w in closed}

        A = sympy.zeros(k, k)
        b = sympy.zeros(k, 1)
        for i, v in enumerate(comp):
            rhs = sympy.expand(update[v].subs(upstream_subs, simultaneous=True))
            try:
                poly = sympy.Poly(rhs, *comp_syms)
            except sympy.PolynomialError as ex:
                raise ValueError(f"non-polynomial coupled recurrence in {v}") from ex
            if poly.total_degree() > 1:
                raise ValueError(
                    f"nonlinear coupled recurrence in {v} (degree {poly.total_degree()})")
            rem = rhs
            for j, sym in enumerate(comp_syms):
                coeff = sympy.expand(poly.coeff_monomial(sym))
                if coeff.has(n) or (coeff.free_symbols & comp_sym_set):
                    raise ValueError(f"non-constant matrix entry for {v}")
                A[i, j] = coeff
                rem = sympy.expand(rem - coeff * sym)
            if rem.has(n):
                raise ValueError(f"n-dependent inhomogeneous term in coupled SCC ({v})")
            b[i, 0] = rem

        has_b = any(b[i, 0] != 0 for i in range(k))
        if has_b:
            M = sympy.zeros(k + 1, k + 1)
            M[:k, :k] = A
            M[:k, k] = b
            M[k, k] = sympy.Integer(1)
            v0 = sympy.Matrix([init[v] for v in comp] + [sympy.Integer(1)])
        else:
            M = A
            v0 = sympy.Matrix([init[v] for v in comp])

        try:
            P, J = M.jordan_form()
            P_inv = P.inv()
        except Exception as ex:
            raise ValueError(f"jordan_form failed on coupled SCC {comp}: {ex}") from ex

        P = P.applyfunc(lambda e: _canon_radicals(sympy.simplify(e)))
        J = J.applyfunc(lambda e: _canon_radicals(sympy.expand(e)))
        c = (P_inv * v0).applyfunc(lambda e: _canon_radicals(sympy.simplify(e)))

        # Build J^n per Jordan block without letting simplify mangle lam**n
        m = J.rows
        Jn = sympy.zeros(m, m)
        i = 0
        while i < m:
            j = i
            while j + 1 < m and J[j, j + 1] == 1:
                j += 1
            lam = J[i, i]
            if lam == 0:
                raise ValueError(f"singular coupled recurrence (zero eigenvalue) in {comp}")
            for r in range(i, j + 1):
                for col in range(r, j + 1):
                    d = col - r
                    if d == 0:
                        Jn[r, col] = lam ** n
                    else:
                        binom_poly = sympy.Mul(*(n - t for t in range(d))) / sympy.factorial(d)
                        Jn[r, col] = binom_poly * lam ** (n - d)
            i = j + 1

        out: dict[str, sympy.Expr] = {}
        for idx, v in enumerate(comp):
            acc = sympy.Integer(0)
            for col in range(m):
                for col2 in range(m):
                    if Jn[col, col2] == 0:
                        continue
                    coeff = _canon_radicals(sympy.simplify(P[idx, col] * c[col2]))
                    if coeff != 0:
                        acc += coeff * Jn[col, col2]
            out[v] = acc
        return out

    # ───────────────────────────────────── eliminate the counter ──

    def eliminate(self, n, S, updated, closed, initsyms=()):
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
                base, exp = _canon_radicals(sympy.expand(p.base)), p.exp
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

        # Replace algebraic radicals (e.g. sqrt(2), sqrt(5), sqrt(t**2 - 1))
        # with fresh symbols _R_i and polynomial defining equations _R_i**q - D = 0
        # so sympy.groebner works over a pure polynomial ring.
        rad_to_R: dict[tuple[sympy.Expr, int], sympy.Symbol] = {}
        rad_rewrites: dict[sympy.Expr, sympy.Expr] = {}
        for v in updated:
            for p in sympy.preorder_traversal(closed_r[v]):
                if p.is_Pow and p.exp.is_Rational and not p.exp.is_Integer:
                    base = sympy.expand(p.base)
                    q = int(p.exp.q)
                    key = (base, q)
                    R = rad_to_R.get(key)
                    if R is None:
                        R = sympy.Symbol(f"_R{len(rad_to_R)}")
                        rad_to_R[key] = R
                    rad_rewrites[p] = R ** int(p.exp.p)
        if rad_rewrites:
            closed_r = {v: closed_r[v].xreplace(rad_rewrites) for v in updated}

        R_syms = list(rad_to_R.values())
        rad_eqs = [sympy.expand(R ** q - base)
                   for (base, q), R in rad_to_R.items()]

        elim = [n] + T_syms + R_syms + list(initsyms)  # variables to project out
        # numerators of {v - closed_v}: clears both rational-function
        # denominators (e.g. 1/(z-1), 1/_R0) and any T**-a from negative shifts
        allsyms = set(elim) | {S[v] for v in updated}
        for v in updated:
            allsyms |= closed_r[v].free_symbols
        for re in rad_eqs:
            allsyms |= re.free_symbols
        gens = elim + sorted(allsyms - set(elim), key=str)

        # numerator of {v - closed_v}: clears rational-number coefficients
        # (ps: n**2/2) *and* rational-function denominators (geo: 1/(z-1)) in
        # one step, leaving an integer/coefficient polynomial equation
        eqs = [sympy.fraction(sympy.together(S[v] - closed_r[v]))[0]
               for v in updated]
        eqs = [sympy.expand(e) for e in eqs]
        eqs += self._base_relations(base_to_T)
        eqs += rad_eqs

        basis = sympy.groebner(eqs, *gens, order="lex")
        elim_set = set(elim)
        cands = [sympy.expand(g) for g in basis.exprs
                 if not (g.free_symbols & elim_set)]   # n, T, R, init eliminated
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
        """Multiplicative relations among exponential bases (numeric, algebraic,
        and conjugate symbolic eigenvalues).

        Handles:
        - `b == -1`  -> `T**2 - 1 = 0`
        - Pairwise products `b_i * b_j == 1`  -> `T_i * T_j - 1 = 0`
          (Pell, Chebyshev, Berggren)
        - Pairwise products `b_i * b_j == -1` -> `T_i * T_j - T_{-1} = 0`
          (if `-1` is also a base, e.g. fibonacci_sign) and `(T_i * T_j)**2 - 1 = 0`
          (e.g. fibonacci)
        - Pairwise `b_i * b_j == b_k` or `b_i == -b_j`
        - General integer left-null space of prime exponents for positive
          rational bases (e.g. bases 2 and 4 -> T_4 = T_2**2).
        """
        rels: list[sympy.Expr] = []
        items = list(base_to_T.items())
        neg_T = None
        for b, T in items:
            if b == -1:
                neg_T = T
                rels.append(sympy.expand(T ** 2 - 1))

        for i in range(len(items)):
            bi, Ti = items[i]
            for j in range(i + 1, len(items)):
                bj, Tj = items[j]
                if sympy.simplify(bi + bj) == 0:
                    if neg_T is not None:
                        rels.append(sympy.expand(Ti - neg_T * Tj))
                    rels.append(sympy.expand(Ti ** 2 - Tj ** 2))
                prod = sympy.simplify(sympy.expand(bi * bj))
                if prod == 1:
                    rels.append(sympy.expand(Ti * Tj - 1))
                elif prod == -1:
                    if neg_T is not None:
                        rels.append(sympy.expand(Ti * Tj - neg_T))
                    else:
                        rels.append(sympy.expand((Ti * Tj) ** 2 - 1))
                else:
                    for k_idx, (bk, Tk) in enumerate(items):
                        if k_idx not in (i, j) and sympy.simplify(prod - bk) == 0:
                            rels.append(sympy.expand(Ti * Tj - Tk))

        numeric = [(sympy.Rational(b), T) for b, T in items
                   if b.is_Rational and b > 0]
        if len(numeric) >= 2:
            primes: list = []
            for b, _T in numeric:
                for p in sympy.factorint(b):
                    if p not in primes:
                        primes.append(p)
            M = sympy.zeros(len(numeric), len(primes))
            for i, (b, _T) in enumerate(numeric):
                for p, e in sympy.factorint(b).items():
                    M[i, primes.index(p)] = e
            for vec in M.T.nullspace():             # e with e^T M = 0
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
        n, S, updated, closed, initsyms = self.solve(variables, init, update)
        raw_polys = self.eliminate(n, S, updated, closed, initsyms)
        cands = _expand_candidates(raw_polys, {S[v] for v in updated})

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
        return closed, _prune_divisible(results)

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
        paths = self.extract_paths(loop)

        cands, seen = [], set()
        for variables, init, update in paths:
            try:
                n, S, updated, closed, initsyms = self.solve(
                    variables, init, update)
                polys = self.eliminate(n, S, updated, closed, initsyms)
            except (ValueError, NotImplementedError):
                continue        # this path is not a solvable recurrence
            for p in _expand_candidates(polys, {S[v] for v in updated}):
                key = str(sympy.expand(p))
                if key not in seen:
                    seen.add(key)
                    cands.append(p)

        if not cands:
            return []

        invs = [_sympy_to_z3(p) == 0 for p in cands]
        kept = self.engine.houdini(invs, loop=loop)
        kept_strs = {str(z3.simplify(e)) for e in kept}
        results = [(p, "valid" if str(z3.simplify(inv)) in kept_strs
                    else "not-inductive")
                   for p, inv in zip(cands, invs)]
        return _prune_divisible(results)


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


def gen_all(filename: Path, depth: int = 5, multipath: bool = True):
    """Proved equality invariants per loop-head vtrace location, as DIG Eqt
    objects: {loc: [Eqt, ...]}.

    This is the entry point DIG's pipeline (alg.py) calls. Each loop is tried
    independently; loops that are not solvable single-path recurrences (or
    whose closed forms yield no polynomial relation) are skipped silently, so
    the dynamic engine remains responsible for them. Every returned Eqt has
    already been proved by unbounded k-induction (houdini), so it is marked
    PROVED and needs no trace checking.

    When ``multipath`` is on (default True), loops the single-path engine
    declines (branching bodies: egcd/fermat/prodbin) are retried with the
    multi-path pipeline before falling back to the dynamic engine.
    """
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
        results = None
        try:
            _closed, results = RecurrenceInfer(filename, depth).gen(i)
        except Exception as ex:
            mlog.debug(f"recurrence declined loop {i} ({loc}): {ex}")
            results = None             # decline: not a solvable single loop
        if results is None and multipath:
            try:
                results = RecurrenceInfer(filename, depth).gen_multipath(i)
            except Exception as ex:
                mlog.debug(f"recurrence-mp declined loop {i} ({loc}): {ex}")
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

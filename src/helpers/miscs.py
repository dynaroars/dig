"""
To run doctest
$ ~/miniconda3/bin/python3 -m doctest -v helpers/miscs.py 
"""

from __future__ import annotations
from collections.abc import Iterable, Callable
from collections import defaultdict
import ast
import os
import pdb
import random
import sys
import itertools
import functools
import multiprocessing
import queue
import signal
import threading
import traceback
import math
import numpy as np
import sympy
from sympy.solvers.solveset import linsolve
import helpers.vcommon as CM
import settings

from beartype import beartype
from beartype.typing import Any
                             
DBG = pdb.set_trace

mlog = CM.getLogger(__name__, settings.LOGGER_LEVEL)


class _GroebnerTimeout(Exception):
    """Raised when sympy.groebner exceeds its time budget (see reduce_eqts)."""


class Miscs:

    @beartype
    @staticmethod
    def is_expr(x: Any) -> bool:
        return isinstance(x, sympy.Expr)

    @beartype
    @classmethod
    def get_vars(cls, props) -> list[sympy.Symbol]:
        """
        Returns a list of uniq variables from a list of properties

        >>> a,b,c,x = sympy.symbols('a b c x')
        >>> assert [a, b, c, x] == Miscs.get_vars([x**(a*b) + a**2+b+2, sympy.Eq(c**2-b,100), sympy.Gt(b**2 + c**2 + a**3,1)])
        >>> assert Miscs.get_vars(a**2+b+5*c+2) == [a, b, c]
        >>> assert Miscs.get_vars(x+x**2) == [x]
        >>> assert Miscs.get_vars([3]) == []
        >>> assert Miscs.get_vars((3,'x + c',x+b)) == [b, x]
        """

        props = props if isinstance(props, Iterable) else [props]
        props = (p for p in props if isinstance(p, (sympy.Expr, sympy.Rel)))
        vs = (v for p in props for v in p.free_symbols)
        return [v for v in sorted(set(vs), key=str) if isinstance(v, sympy.Symbol)]

    @beartype
    @staticmethod
    def str2list(s: str) -> tuple:
        # Trace values are literals (e.g. "[1, 2, 3]"); literal_eval parses
        # them without the arbitrary-code-execution exposure of bare eval().
        rs = tuple(ast.literal_eval(s))
        return rs


    @staticmethod
    @functools.cache
    def str2rat(s: str) -> sympy.Rational:
        """
        Convert the input 's' to a rational number if possible.

        Examples:
        >>> print(Miscs.str2rat('.3333333'))
        3333333/10000000
        >>> print(Miscs.str2rat('3/7'))
        3/7
        >>> print(Miscs.str2rat('1.'))
        1
        >>> print(Miscs.str2rat('1.2'))
        6/5
        >>> print(Miscs.str2rat('.333'))
        333/1000
        >>> print(Miscs.str2rat('-.333'))
        -333/1000
        >>> print(Miscs.str2rat('-12.13'))
        -1213/100
        """
        return sympy.Rational(s)

    @beartype    
    @staticmethod
    def create_uks(ts: list[Any], prefix: str = "uk") -> list[sympy.Symbol]:
        uks = [sympy.Symbol(f"{prefix}_{i}") for i in range(len(ts))]
        assert not set(ts).intersection(set(uks)), "name conflict"
        return uks

    @beartype
    @classmethod
    def init_terms(cls, vs: tuple[str,...], deg: int, 
                   rate: float) -> tuple[list[Any], list[sympy.Symbol], int]:
        assert vs, vs
        assert deg >= 1, deg
        assert rate >= 0.1, rate

        symbols = [sympy.Symbol(v) for v in vs]
        terms = cls.get_terms(symbols, deg)
        uks = cls.create_uks(terms)
        assert not set(terms).intersection(set(uks)), "name conflict"
        n_eqts_needed = int(rate * len(uks))
        return terms, uks, n_eqts_needed

    @beartype    
    @staticmethod
    def get_terms(symbols: list[sympy.Symbol], deg: int) -> list:
        """
        get a list of terms from the given list of vars and deg
        the number of terms is len(rs) == binomial(len(symbols)+d, d)

        >>> a,b,c,d,e,f = sympy.symbols('a b c d e f')
        >>> ts = Miscs.get_terms([a, b], 3)
        >>> assert ts == [1, a, b, a**2, a*b, b**2, a**3, a**2*b, a*b**2, b**3]
        >>> Miscs.get_terms([a,b,c,d,e,f], 3)
        [1, a, b, c, d, e, f, a**2, a*b, a*c, a*d, a*e, a*f, b**2, b*c, b*d, b*e, b*f, c**2, c*d, c*e, c*f, d**2, d*e, d*f, e**2, e*f, f**2, a**3, a**2*b, a**2*c, a**2*d, a**2*e, a**2*f, a*b**2, a*b*c, a*b*d, a*b*e, a*b*f, a*c**2, a*c*d, a*c*e, a*c*f, a*d**2, a*d*e, a*d*f, a*e**2, a*e*f, a*f**2, b**3, b**2*c, b**2*d, b**2*e, b**2*f, b*c**2, b*c*d, b*c*e, b*c*f, b*d**2, b*d*e, b*d*f, b*e**2, b*e*f, b*f**2, c**3, c**2*d, c**2*e, c**2*f, c*d**2, c*d*e, c*d*f, c*e**2, c*e*f, c*f**2, d**3, d**2*e, d**2*f, d*e**2, d*e*f, d*f**2, e**3, e**2*f, e*f**2, f**3]
        """

        assert deg >= 0, deg
        assert symbols, symbols

        # ss_ = ([1] if ss else (1,)) + ss
        symbols_ = [1] + symbols
        combs = itertools.combinations_with_replacement(symbols_, deg)
        terms = [sympy.prod(c) for c in combs]
        return terms

    @beartype
    @classmethod
    def get_max_deg(cls, p: int | sympy.Expr) -> int:
        """
        get the max degree of a polynomial

        >>> x, y, z = sympy.symbols('x y z')
        >>> p = 3*x**2*y + x*y**4 + z*x
        >>> assert(Miscs.get_max_deg(p) == 5)
        >>> assert(Miscs.get_max_deg(x) == 1)
        >>> assert(Miscs.get_max_deg(x**3) == 3)
        >>> assert(Miscs.get_max_deg(-100) == 0)
        >>> assert(Miscs.get_max_deg(x*y-100) == 2)
        >>> assert(Miscs.get_max_deg(x*y**2 + 3*y) == 3)
        """

        match p:
            case int() | sympy.Integer():
                return 0
            case sympy.Expr() if p.is_Symbol or p.is_Mul or p.is_Pow:  # x, x*y, x**3
                return int(sum(sympy.degree_list(p)))
            case sympy.Add():
                return max(cls.get_max_deg(a) for a in p.args)
            case _:
                mlog.warning(f"cannot handle {p} of type {type(p)}")
                return 0

    @beartype    
    @classmethod
    def get_deg(cls, nvs: int, nts: int, max_deg: int = 7) -> int:
        """
        Guess a max degree wrt to a (maximum) number of terms (nss)

        >>> assert(Miscs.get_deg(3, 4, 5) == 1)
        >>> Miscs.get_deg(3, 1, 5)
        Traceback (most recent call last):
        ...
        AssertionError: (1, 3)
        """

        assert nvs >= 1, nvs
        assert nts >= nvs, (nts, nvs)
        assert max_deg >= 1, max_deg

        for d in range(1, max_deg + 1):
            if d == max_deg:
                return d

            # look ahead
            nterms: int = math.comb(nvs + d + 1, d + 1)
            if nterms > nts:
                return d
        return max_deg

    @beartype
    @classmethod
    def get_auto_deg(cls, maxdeg: None | int, nvars: int, maxterm: int) -> int:
        if maxdeg:
            deg = maxdeg
            mlog.debug(f"using deg {deg}")
        else:
            deg = cls.get_deg(nvars, maxterm)
            mlog.debug(f"autodeg {deg}")

        return deg

    @staticmethod
    def seq_degree(values: list[int], max_deg: int = 8) -> int | None:
        """
        Degree of the polynomial underlying an equally-spaced sequence, via the
        method of finite differences: a sequence is degree d iff its d-th
        difference is constant (and the (d+1)-th vanishes). Returns None if it
        doesn't stabilize within max_deg, i.e. the values aren't polynomial in
        the loop index (e.g. subtractive/gcd-style or bit/mod updates).

        Needs >= d+2 points to confirm degree d.

        >>> Miscs.seq_degree([0, 1, 8, 27, 64])   # cubes
        3
        >>> Miscs.seq_degree([2, 2, 2, 2])         # constant
        0
        >>> Miscs.seq_degree([0, 1, 3, 6, 10])     # triangular -> quadratic
        2
        >>> Miscs.seq_degree([1, 2, 4, 8, 16]) is None  # exponential, not poly
        True
        """
        seq = list(values)
        d = 0
        while d <= max_deg:
            if len(seq) < 2:
                return None             # not enough points to decide
            if len(set(seq)) == 1:
                return d                # d-th difference is constant
            seq = [b - a for a, b in zip(seq, seq[1:])]
            d += 1
        return None                     # not polynomial within max_deg

    @classmethod
    def estimate_degree(cls, exec_rows: list[list[dict]],
                        max_deg: int = 8) -> tuple[dict[str, int], int | None]:
        """
        Estimate each variable's polynomial degree (growth order vs the loop
        index) from ordered traces, as a *clue* to the invariant degree.

        exec_rows: one entry per execution, each an ordered list of {var: value}
        rows observed at a single location (in iteration order).

        Returns (per_var, max_seen): per_var maps var -> max detected degree
        across executions (vars that never stabilize are omitted); max_seen is
        the overall max (None if nothing stabilized). Note this is a heuristic
        clue, not a sound upper bound: products of low-order vars can still
        cancel into a higher-degree relation (e.g. egcd's p*s - q*r).
        """
        per_var: dict[str, int] = {}
        for rows in exec_rows:
            if len(rows) < 3:
                continue
            for v in rows[0]:
                try:
                    seq = [int(r[v]) for r in rows]
                except (KeyError, ValueError, TypeError):
                    continue
                d = cls.seq_degree(seq, max_deg)
                if d is not None:
                    per_var[v] = max(per_var.get(v, 0), d)
        mx = max(per_var.values()) if per_var else None
        return per_var, mx

    @beartype
    @staticmethod
    def get_terms_fixed_coefs(ss, subset_siz: int, icoef: int,
                              do_create_terms:bool=True) -> set:
        """
        if do_create_terms = True, then return x*y,  otherwise, return (x,y)

        >>> x, y, z, t, s, u = sympy.symbols('x y z t s u')
        >>> sorted(Miscs.get_terms_fixed_coefs([x,y], 2, 1), key=lambda x: str(x))
        [-x, -x + y, -x - y, -y, x, x + y, x - y, y]
        >>> sorted(Miscs.get_terms_fixed_coefs([x,y**2], 2, 1), key=lambda x: str(x))
        [-x, -x + y**2, -x - y**2, -y**2, x, x + y**2, x - y**2, y**2]
        >>> assert len(Miscs.get_terms_fixed_coefs([x,y,z], 2, 1)) == 18
        >>> assert len(Miscs.get_terms_fixed_coefs([x,y,z], 3, 1)) == 26
        >>> assert len(Miscs.get_terms_fixed_coefs([x,y,z], 2, 3)) == 126
        """
        assert icoef >= 1, icoef
        if len(ss) < subset_siz:
            subset_siz = len(ss)

        coefs = list(range(-icoef, icoef + 1))
        rs = []
        for ssSubset in itertools.combinations(ss, subset_siz):
            css = itertools.product(*([coefs] * len(ssSubset)))
            rs_ = [
                tuple((t, c) for t, c in zip(ssSubset, cs) if c != 0)
                for cs in css
                if not all(c_ == 0 for c_ in cs)
            ]
            if do_create_terms:
                rs_ = [sum(t * c for t, c in tc) for tc in rs_]
            rs.extend(rs_)

        return set(rs)


    @beartype
    @classmethod
    def reduce_eqts(cls, ps: list[sympy.Expr | sympy.Rel]) -> list[sympy.Expr | sympy.Rel]:
        """
        Return the basis (e.g., a min subset of ps that implies ps)
        of the set of polynomial eqts using Groebner basis.
        Warning 1: Grobner basis sometimes results in a larger set of eqts,
        in which case we return the original set of eqts.
        Warning 2: seems to get stuck often.  So had to give it "nice" polynomials

        >>> a, y, b, q, k = sympy.symbols('a y b q k')


        # >>> rs = Miscs.reduce_eqts([a*y-b==0,q*y+k-x==0,a*x-a*k-b*q==0])
        __main__:DEBUG:Grobner basis: got 2 ps from 3 ps
        # >>> assert set(rs) == set([a*y - b == 0, q*y + k - x == 0])

        # >>> rs =  Miscs.reduce_eqts([x*y==6,y==2,x==3])
        __main__:DEBUG:Grobner basis: got 2 ps from 3 ps
        # >>> assert set(rs) == set([x - 3 == 0, y - 2 == 0])

        # Attribute error occurs when only 1 var, thus return as is
        # >>> rs =  Miscs.reduce_eqts([x*x==4,x==2])
        __main__:ERROR:'Ideal_1poly_field' object has no attribute 'radical'
        # >>> assert set(rs) == set([x == 2, x**2 == 4])
        """

        if len(ps) <= 1:
            return ps

        try:
            ps_ = cls._groebner_timed(ps, cls.get_vars(ps),
                                      settings.GROEBNER_TIMEOUT)
        except _GroebnerTimeout:
            mlog.warning(
                f"groebner timed out (>{settings.GROEBNER_TIMEOUT}s) on "
                f"{len(ps)} ps; keeping unreduced eqts")
            return ps
        ps_ = [x for x in ps_]
        mlog.debug(f"Grobner basis: from {len(ps)} to {len(ps_)} ps")
        return ps_ if len(ps_) < len(ps) else ps

    @staticmethod
    def _groebner_timed(ps: list, vs: list, timeout_s: int):
        """
        sympy.groebner with a wall-clock bound via SIGALRM. Groebner basis is
        worst-case doubly-exponential and is known to hang on some inputs; on
        timeout we raise _GroebnerTimeout so the caller can fall back.

        SIGALRM only works on the main thread; off-thread (shouldn't happen in
        the fork-based MP workers, which run tasks on their main thread) we just
        run without a timer.
        """
        if (timeout_s <= 0
                or threading.current_thread() is not threading.main_thread()):
            return sympy.groebner(ps, *vs)

        def _handler(signum, frame):
            raise _GroebnerTimeout()

        old = signal.signal(signal.SIGALRM, _handler)
        signal.setitimer(signal.ITIMER_REAL, timeout_s)
        try:
            return sympy.groebner(ps, *vs)
        finally:
            signal.setitimer(signal.ITIMER_REAL, 0)
            signal.signal(signal.SIGALRM, old)

    @beartype
    @staticmethod
    def elim_denom(p: sympy.Expr | sympy.Rel) -> sympy.Expr | sympy.Rel:
        """
        Eliminate (Integer) denominators in expression operands.
        Will not eliminate if denominators is a var (e.g.,  (3*x)/(y+2)).

        >>> x,y,z = sympy.symbols('x y z')

        >>> Miscs.elim_denom(sympy.Rational(3, 4)*x**2 + sympy.Rational(7, 5)*y**3)
        15*x**2 + 28*y**3

        >>> Miscs.elim_denom(x + y)
        x + y

        >>> Miscs.elim_denom(-sympy.Rational(3,2)*x**2 - sympy.Rational(1,24)*z**2)
        -36*x**2 - z**2

        >>> Miscs.elim_denom(15*x**2 - 12*z**2)
        15*x**2 - 12*z**2

        """
        denoms = [sympy.fraction(a)[1] for a in p.args]
        if all(denom == 1 for denom in denoms):  # no denominator like 1/2
            return p
        return p * sympy.lcm(denoms)

    @beartype
    @classmethod
    def get_coefs(cls, p: sympy.Expr | sympy.Rel) -> list[sympy.core.numbers.Integer]:
        """
        Return coefficients of an expression

        >>> x,y,z = sympy.symbols('x y z')
        >>> Miscs.get_coefs(3*x+5*x*y**2)
        [3, 5]
        """

        p = p.lhs if p.is_Equality else p
        return list(p.as_coefficients_dict().values())

    @beartype
    @classmethod
    def remove_ugly(cls, ps: list[sympy.Expr | sympy.Rel]) -> list[sympy.Expr |  sympy.Rel]:

        @functools.cache
        def is_nice_coef(c: int | float) -> bool:
            return abs(c) <= settings.UGLY_FACTOR or c % 10 == 0 or c % 5 == 0

        @functools.cache
        def is_nice_eqt(eqt: sympy.Expr | sympy.Rel) -> bool:
            return (len(eqt.args) <= settings.UGLY_FACTOR
                    and all(is_nice_coef(c) for c in cls.get_coefs(eqt)))

        ps_ = []
        for p in ps:
            if is_nice_eqt(p):
                ps_.append(p)
            else:
                mlog.debug(f"ignoring large coefs {str(p)[:50]} ..")

        return ps_

    @beartype
    @classmethod
    def refine(cls, eqts: list[sympy.Expr | sympy.Rel],
               do_reduce: bool = True) -> list[sympy.Expr | sympy.Rel]:

        if not eqts:
            return eqts

        eqts = [cls.elim_denom(s) for s in eqts]
        eqts = cls.remove_ugly(eqts)
        if do_reduce:
            eqts = cls.reduce_eqts(eqts)
        eqts = [cls.elim_denom(s) for s in eqts]
        eqts = cls.remove_ugly(eqts)

        return eqts

    @classmethod
    def coef_matrix_rank(cls, eqts: list, uks: list) -> int:
        """
        Fast numpy rank of the template coefficient matrix.
        Returns -1 on any failure so callers can treat it as unknown.
        """
        try:
            M = np.array(
                [[int(e.coeff(uk)) for uk in uks] for e in eqts],
                dtype=np.float64,
            )
            return int(np.linalg.matrix_rank(M)) if M.size > 0 else 0
        except Exception:
            return -1

    @classmethod
    def _null_space_fast(cls, eqts: list, uks: list) -> list | None:
        """
        Compute null space of the template coefficient matrix using two passes:
        1. NumPy SVD (float64) to quickly detect full rank — if the matrix has no
           null space, return [] immediately without calling sympy at all.
        2. sympy.Matrix.nullspace() for exact rational null vectors when the rank
           check indicates a non-trivial null space exists.

        Avoids the overhead of linsolve's FiniteSet / parametric-solution machinery.
        Returns a list of sympy column vectors, or None to fall back to linsolve.

        The eqts are linear in uks (trace values are integers, so each expression
        is sum(coef_j * uk_j)). Coefficients may be rationals (e.g. real-valued
        traces like x = 95/2), so keep them exact for the sympy null space and
        only float-cast for the numpy rank check.
        """
        try:
            rows = [[expr.coeff(uk) for uk in uks] for expr in eqts]
            # float-cast for the numpy rank check; a non-numeric coefficient
            # (template not fully reduced on some trace) means we can't use the
            # fast path, so fall back to the exact solver.
            M_np = np.array([[float(c) for c in row] for row in rows],
                            dtype=np.float64)
        except (TypeError, AttributeError, ValueError):
            return None

        if M_np.size == 0:
            return None
        n = len(uks)
        _, s, Vh = np.linalg.svd(M_np, full_matrices=True)
        tol = max(M_np.shape) * np.finfo(np.float64).eps * (s[0] if len(s) else 1.0)
        rank = int(np.sum(s > tol))
        if rank >= n:
            return []  # full column rank → trivial null space, skip sympy entirely

        # Trace-guided term reduction: rows of Vh past the rank span the numeric
        # null space (the invariant coefficient space). A term (column) whose
        # entry is ~0 in *every* null-space basis vector has coefficient 0 in
        # every invariant, so drop it. The exact (sound) solve then runs on the
        # relevant subset only — smaller for high-degree / many-var templates
        # where invariants use few of the C(n+deg, deg) monomials.
        null_basis = Vh[rank:]                       # (n - rank) x n
        support = np.abs(null_basis).max(axis=0)     # per-term max |coef|
        relevant = [j for j in range(n) if support[j] > 1e-7]
        if not relevant:
            return None  # numeric degeneracy; let caller fall back

        if len(relevant) < n:
            mlog.debug(f"term reduction: {n} -> {len(relevant)} terms")

        # Exact null space via sympy on the reduced columns, then map back to
        # the full uk space (0 for the dropped, provably-uninvolved terms).
        M_sym = sympy.Matrix([[row[j] for j in relevant] for row in rows])
        try:
            reduced = M_sym.nullspace()
        except Exception:
            return None
        full_vecs = []
        for rv in reduced:
            full = sympy.zeros(n, 1)
            for i, j in enumerate(relevant):
                full[j] = rv[i]
            full_vecs.append(full)
        return full_vecs

    @beartype
    @classmethod
    def solve_eqts(cls, eqts: list[sympy.Expr | sympy.Rel],
                   terms: list[Any], uks: list[sympy.Symbol],
                   do_reduce: bool = True) -> list[sympy.Eq]:

        assert eqts, eqts
        assert terms, terms
        assert uks, uks
        assert len(terms) == len(uks), (terms, uks)
        # assert len(eqts) >= len(uks), (len(eqts), len(uks))

        mlog.debug(f"solving {len(uks)} uks using {len(eqts)} eqts")

        null_vecs = cls._null_space_fast(eqts, uks)
        if null_vecs is not None:
            if not null_vecs:
                return []
            # each null_vec is a sympy column Matrix; zip with terms directly
            eqts_ = [
                sum(c * t for c, t in zip(nvec, terms) if c != 0)
                for nvec in null_vecs
            ]
            eqts_ = [e for e in eqts_ if e != 0]
        else:
            # fall back to sympy linsolve
            sol = linsolve(eqts, uks)
            #print(eqts)
            #print(uks)
            #print(sol)
            sol_list = list(sol)
            if not sol_list:
                return []
            vals = list(sol_list[0])
            if all(v == 0 for v in vals):
                return []
            eqts_ = cls.instantiate_template(terms, uks, vals)
            if not isinstance(eqts_, list):
                eqts_ = [eqts_]

        if not eqts_:
            return []

        mlog.debug(f"got {len(eqts_)} eqts after solving")
        eqts_ = cls.refine(eqts_, do_reduce=do_reduce)
        mlog.debug(f"got {len(eqts_)} eqts after refinement")
        return [sympy.Eq(eqt, 0) for eqt in eqts_]

    @beartype
    @classmethod
    def instantiate_template(cls, terms:list, uks:list, vs:list) -> list:
        """
        Instantiate a template with solved coefficient values

        # sage:var('uk_0,uk_1,uk_2,uk_3,uk_4,r14,r15,a,b,y')
        (uk_0, uk_1, uk_2, uk_3, uk_4, r14, r15, a, b, y)

        # sage:sols = [{uk_0: -2*r14 + 7/3*r15, uk_1: - \
            1/3*r15, uk_4: r14, uk_2: r15, uk_3: -2*r14}]
        # sage:Miscs.instantiate_template(uk_1*a + uk_2*b + uk_3*x + uk_4*y + uk_0 == 0, sols)
        [-2*x + y - 2 == 0, -1/3*a + b + 7/3 == 0]

        # sage:Miscs.instantiate_template(uk_1*a + uk_2*b + uk_3*x + uk_4*y + uk_0 == 0, [])
        []
        """
        assert terms, terms
        assert uks, uks

        cs = [(t, u, v) for t, u, v in zip(terms, uks, vs, strict=True) if v != 0]
        terms_, uks_, vs_ = zip(*cs)

        eqt = sum(t*v for t, v in zip(terms_, vs_))

        uk_vs = cls.get_vars(vs_)

        if not uk_vs:
            return eqt

        sols = [eqt.xreplace({uk: (1 if j == i else 0) for j, uk in enumerate(uk_vs)})
                for i, uk in enumerate(uk_vs)]
        return sols

    @beartype
    @staticmethod
    def show_removed(s: str, orig_siz: int, new_siz: int, 
                     elapsed_time: float) -> None:
        assert orig_siz >= new_siz, (orig_siz, new_siz)
        n_removed = orig_siz - new_siz
        mlog.debug(
            f"{s}: removed {n_removed} invs "
            f"in {elapsed_time:.2f}s (orig {orig_siz}, new {new_siz})"
        )

    @beartype
    @staticmethod
    def simplify_idxs(ordered_idxs: list[int], 
                      imply_f: Callable[[set[int], int], bool]) -> list[int]:
        """
        attempt to remove i in idxs if imply_f returns true
        Note: the order of idxs determine what to get checked (and removed)
        """
        assert isinstance(ordered_idxs, list), ordered_idxs
        assert ordered_idxs == list(range(len(ordered_idxs))), ordered_idxs

        results = set(ordered_idxs)

        for i in reversed(ordered_idxs):
            if i not in results:
                continue
            others = results - {i}
            if others and imply_f(others, i):
                results = others

        return sorted(results)

    @staticmethod
    def create_dict(l: list[tuple[Any, Any]]) -> dict[Any, Any]:
        """
        given a list of set of type [(k1,v1),..,(kn,vn)]
        generates a dict where keys are k's and values are [v's]
        e.g.,

        >>> Miscs.create_dict([('a',1),['b',2],('a',3),('c',4),('b',10)])
        {'a': [1, 3], 'b': [2, 10], 'c': [4]}
        """
        d: defaultdict = defaultdict(list)
        for k, v in l:
            d[k].append(v)
        return dict(d)

    @beartype
    @staticmethod
    def merge_dict(l: list[dict[Any, Any]]) -> dict[Any, Any]:
        result: dict = {}
        for d in l:
            result |= d
        return result


# Module-level state for fork-based workers.
# Pickling the callable and args fails for closures that capture z3 ctypes.
# Workaround: store both in globals before the workers fork; workers inherit
# them via fork. Only the batch index and the (picklable) results cross the
# IPC boundary.
_MP_FN: Any = None
_MP_WLOADS: list = []
_MP_SEED: int | None = None


def _mp_run_worker(idx: int, out_q) -> None:
    """
    Run one batch in a freshly forked process and send back (idx, ok, payload).
    """
    _worker_init()
    # Python (3.12+) reseeds the random module nondeterministically on fork, so
    # any RNG use inside a worker (e.g. eqt's gen_rand_inps) would vary run to
    # run. Reseed deterministically from the parent's RNG state + the batch
    # index to restore reproducibility under multiprocessing.
    random.seed(_MP_SEED + idx)
    try:
        rs = _MP_FN(_MP_WLOADS[idx])
        out_q.put((idx, True, rs))
    except Exception:
        out_q.put((idx, False, traceback.format_exc()))


def _worker_init():
    """
    Make each forked worker die with its parent so an interrupted or killed
    DIG run can't leave workers busy-looping (e.g. mid z3 solve). Uses Linux
    PR_SET_PDEATHSIG; a no-op elsewhere. run_mp's cleanup only runs on normal/
    exception exit — this covers the uncatchable cases (SIGKILL, parent crash).
    """
    if sys.platform != "linux":
        return
    try:
        import ctypes
        PR_SET_PDEATHSIG = 1
        ctypes.CDLL("libc.so.6", use_errno=True).prctl(
            PR_SET_PDEATHSIG, signal.SIGKILL)
        # race: parent may have died between fork and prctl above
        if os.getppid() == 1:
            os._exit(1)
    except Exception:
        pass


class MP:
    # Fixed number of task batches (and hence per-batch RNG seeds). Must NOT
    # depend on cpu_count: batch boundaries and seeds determine results, so
    # deriving them from the machine would make results differ across machines.
    # Machines with fewer cores run the same batches on fewer processes; z3's
    # rlimit budget keeps solver results independent of CPU contention.
    N_BATCHES = 12

    @beartype
    @staticmethod
    def get_workload(tasks: list[Any], n_batches: int) -> list[list[Any]]:
        """
        Split tasks into at most n_batches round-robin batches, smallest
        batches first. This layout (and hence the concatenated result order,
        which downstream order-sensitive steps like trace sampling and
        simplification observe) is the historical one the golden results were
        recorded with — keep it; only n_batches was decoupled from cpu_count.

        >>> wls = MP.get_workload(list(range(12)),7); [len(wl) for wl in wls]
        [1, 1, 2, 2, 2, 2, 2]

        >>> wls = MP.get_workload(list(range(12)),5); [len(wl) for wl in wls]
        [2, 2, 2, 3, 3]

        >>> wls = MP.get_workload(list(range(20)),7); [len(wl) for wl in wls]
        [2, 3, 3, 3, 3, 3, 3]

        >>> MP.get_workload(list(range(3)), 7)
        [[0], [1], [2]]

        >>> wls = MP.get_workload(list(range(146)), 12); [len(wl) for wl in wls]
        [12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 13, 13]
        """
        assert len(tasks) >= 1, tasks
        assert n_batches >= 1, n_batches

        wloads = defaultdict(list)
        for i, task in enumerate(tasks):
            wloads[i % n_batches].append(task)

        return sorted(wloads.values(), key=len)

    @classmethod
    def run_mp(cls, taskname: str, tasks: list[Any], f: Callable[[list[Any]], Any], DO_MP: bool) -> list[Any]:
        """
        Run f over `tasks` split into at most N_BATCHES batches, each batch
        in a fresh forked process when DO_MP (else in-process).

        Determinism contract for the parallel (default) path: results do not
        depend on cpu_count or on scheduling, so they are reproducible across
        machines. Batch layout, result order, and per-batch RNG seeds derive
        only from len(tasks) and the parent's RNG state; each batch runs in
        its own pristine fork of the parent — one Process per batch, so no
        z3/caching state leaks between batches through a reused worker, and a
        1-core machine forks (and gets) exactly the same batches as a 64-core
        one; results are concatenated in batch order (deterministic, see
        get_workload, but not the original task order).

        The serial path (DO_MP off, nested inside a worker, or a single
        batch) is a plain in-process f(tasks). It is equally deterministic
        but -nomp results may legitimately differ from mp results: forked
        batches consume per-batch RNG streams (serial consumes the parent's
        one stream), and fork isolation discards each batch's in-place side
        effects (caches, inv stats) that a serial run keeps. Faithful
        in-process emulation of fork semantics is not possible, so -nomp is a
        debugging fallback, not a result-identical mode; golden results are
        defined by the default mp mode.

        Uses fork (not spawn/Pool/ProcessPoolExecutor) so f can capture
        non-picklable state such as z3 ctypes, and so every fork happens from
        the main thread before any helper thread exists (forking a threaded
        parent, as Pool worker-respawn does, can deadlock the child). Only the
        batch index and the results cross the IPC boundary; the callable and
        workload are inherited through the module-level globals set before the
        forks.
        """
        global _MP_FN, _MP_WLOADS, _MP_SEED

        if not tasks:
            return []

        wloads = cls.get_workload(tasks, cls.N_BATCHES)
        if (not DO_MP or len(wloads) < 2
                or multiprocessing.current_process().daemon):
            return f(tasks)

        # per-batch seeds derive from the parent's (seeded) RNG state;
        # reading the state doesn't perturb the parent's stream
        seed = hash(random.getstate())

        mlog.debug(
            f"{taskname}: running {len(tasks)} jobs "
            f"using {len(wloads)} batches: {list(map(len, wloads))}"
        )
        _MP_FN, _MP_WLOADS, _MP_SEED = f, wloads, seed
        procs = []
        try:
            # Use fork so workers inherit _MP_FN/_MP_WLOADS globals (3.14+
            # defaults to forkserver). daemon=True so nested run_mp calls
            # inside a worker take the serial path.
            ctx = multiprocessing.get_context("fork")
            out_q = ctx.Queue()
            for idx in range(len(wloads)):
                p = ctx.Process(target=_mp_run_worker, args=(idx, out_q),
                                daemon=True)
                p.start()
                procs.append(p)

            by_idx: dict[int, Any] = {}
            grace = 0
            while len(by_idx) < len(wloads):
                try:
                    idx, ok, payload = out_q.get(timeout=1)
                except queue.Empty:
                    dead = [i for i, p in enumerate(procs)
                            if not p.is_alive() and i not in by_idx]
                    # a few extra polls so a just-exited worker's queued
                    # result can still drain through the pipe
                    grace = grace + 1 if dead else 0
                    if dead and grace >= 3:
                        raise RuntimeError(
                            f"{taskname}: worker(s) {dead} died without "
                            f"returning a result (exitcodes "
                            f"{[procs[i].exitcode for i in dead]})")
                    continue
                grace = 0
                if not ok:
                    raise RuntimeError(
                        f"{taskname}: worker {idx} failed:\n{payload}")
                by_idx[idx] = payload
            for p in procs:
                p.join()
        finally:
            for p in procs:
                if p.is_alive():
                    p.terminate()
            _MP_FN, _MP_WLOADS, _MP_SEED = None, [], None

        return [r for idx in range(len(wloads)) for r in by_idx[idx]]


if __name__ == "__main__":
    import doctest
    doctest.testmod()

from functools import reduce
import pdb
import itertools
import operator
import ast
from collections import Iterable

import sage.all
from sage.all import cached_function, fork

import z3
import helpers.vcommon as CM
import settings

DBG = pdb.set_trace

mlog = CM.getLogger(__name__, settings.logger_level)


class Miscs(object):
    @staticmethod
    def msage_eval(s, d):
        assert all(isinstance(k, str) and
                   Miscs.is_expr(v) for k, v in d.items()), d
        while True:
            try:
                return sage.all.sage_eval(s, d)
            except NameError as e:  # name 'yy' is not defined
                symb = str(e).split("'")[1]
                mlog.debug("create new symbol {}".format(symb))
                d[symb] = sage.all.var(symb)

    @staticmethod
    def is_real(x): return isinstance(x, sage.rings.real_mpfr.RealLiteral)

    @staticmethod
    def is_int(x): return isinstance(x, sage.rings.integer.Integer)

    @classmethod
    def is_num(cls, x): return cls.is_real(x) or cls.is_int(x)

    @staticmethod
    def is_rel(f, rel=None):
        """
        sage: from helpers.miscs import Miscs
        sage: assert not Miscs.is_rel(7.2)
        sage: assert not Miscs.is_rel(x)
        sage: assert not Miscs.is_rel(x+7)
        sage: assert Miscs.is_rel(x==3,operator.eq)

        sage: assert Miscs.is_rel(x<=3,operator.le)
        sage: assert not Miscs.is_rel(x<=3,operator.lt)
        sage: assert not Miscs.is_rel(x+3,operator.lt)

        sage: y = var('y')
        sage: assert Miscs.is_rel(x+y<=3)
        """

        try:
            if not f.is_relational():
                return False

            if rel is None:
                return True
            else:
                return f.operator() == rel

        except AttributeError:
            return False

    @classmethod
    def is_eq(cls, f):
        return cls.is_rel(f, operator.eq)

    @staticmethod
    def is_expr(x):
        return isinstance(x, sage.symbolic.expression.Expression)

    @classmethod
    def get_vars(cls, ps):
        """
        Returns a list of uniq variables from a list of properties

        Examples:

        sage: var('a b c x')
        (a, b, c, x)

        sage: from helpers.miscs import Miscs
        sage: assert [a, b, c, x] == Miscs.get_vars([x^(a*b) + a**2+b+2==0, c**2-b==100, b**2 + c**2 + a**3>= 1])
        sage: assert Miscs.get_vars(a**2+b+5*c+2==0) == [a, b, c]
        sage: assert Miscs.get_vars(x+x^2) == [x]
        sage: assert Miscs.get_vars([3]) == []
        sage: assert Miscs.get_vars((3,'x + c',x+b)) == [b, x]
        """

        ps = ps if isinstance(ps, Iterable) else [ps]
        ps = [p for p in ps if cls.is_expr(p)]
        vs = [v for p in ps for v in p.variables()]
        return sorted(set(vs), key=str)

    @staticmethod
    @cached_function
    def rat2str(s):
        """
        Convert the input 's' to a rational number if possible.

        Examples:

        sage: from helpers.miscs import Miscs
        sage: assert Miscs.rat2str('.3333333') == 3333333/10000000
        sage: assert Miscs.rat2str('3/7') == 3/7
        sage: assert Miscs.rat2str('1.') == 1
        sage: assert Miscs.rat2str('1.2') == 6/5
        sage: assert Miscs.rat2str('.333') == 333/1000
        sage: assert Miscs.rat2str('-.333') == -333/1000
        sage: assert Miscs.rat2str('-12.13') == -1213/100

        # Returns None because cannot convert this str
        sage: Miscs.rat2str('333333333333333s')
        Traceback (most recent call last):
        ...
        TypeError: unable to convert '333333333333333s' to a real number


        Note: this version seems to be the *fastest*
        among several ones I've tried
        %timeit rat2str('322')
        """
        try:
            return sage.all.QQ(s)
        except TypeError:
            pass

        return sage.all.QQ(sage.all.RR(s))

    @classmethod
    def init_terms(cls, vs, deg, rate):
        assert vs, vs
        assert deg >= 1, deg
        assert rate >= 0.1, rate

        terms = cls.get_terms([sage.all.var(v) for v in vs], deg)

        template, uks = cls.mk_template(terms, 0, retCoefVars=True)
        n_eqts_needed = int(rate * len(uks))
        return terms, template, uks, n_eqts_needed

    @staticmethod
    def get_terms(ss, deg):
        """
        get a list of terms from the given list of vars and deg
        the number of terms is len(rs) == binomial(len(ss)+d, d)

        Note: itertools is faster than Sage's MultichooseNK(len(ss)+1,deg)

        sage: from helpers.miscs import Miscs

        sage: ts = Miscs.get_terms(list(var('a b')), 3)
        sage: assert ts == [1, a, b, a^2, a*b, b^2, a^3, a^2*b, a*b^2, b^3]

        sage: ts = Miscs.get_terms(list(var('a b c d e f')), 3)
        sage: ts
        [1, a, b, c, d, e, f,
        a^2, a*b, a*c, a*d, a*e, a*f,
        b^2, b*c, b*d, b*e, b*f, c^2, c*d, c*e, c*f,
        d^2, d*e, d*f, e^2, e*f, f^2, a^3, a^2*b, a^2*c, a^2*d, a^2*e,
        a^2*f, a*b^2, a*b*c, a*b*d, a*b*e, a*b*f, a*c^2, a*c*d, a*c*e,
        a*c*f, a*d^2, a*d*e, a*d*f, a*e^2, a*e*f, a*f^2,
        b^3, b^2*c, b^2*d, b^2*e, b^2*f, b*c^2, b*c*d, b*c*e, b*c*f, b*d^2,
        b*d*e, b*d*f, b*e^2, b*e*f, b*f^2, c^3, c^2*d, c^2*e, c^2*f, c*d^2,
        c*d*e, c*d*f, c*e^2, c*e*f, c*f^2, d^3, d^2*e, d^2*f, d*e^2, d*e*f,
        d*f^2, e^3, e^2*f, e*f^2, f^3]

        """
        assert deg >= 0, deg
        assert ss and all(s.is_symbol() for s in ss), ss
        ss_ = ([sage.all.SR(1)] if ss else (sage.all.SR(1),)) + ss
        combs = itertools.combinations_with_replacement(ss_, deg)
        terms = [sage.all.prod(c) for c in combs]
        return terms

    @classmethod
    def get_deg(cls, nvs, nts, max_deg=7):
        """
        Generates a degree wrt to a (maximum) number of terms (nss)

        sage: from helpers.miscs import Miscs

        sage: assert Miscs.get_deg(3, 4, 5) == 1
        sage: Miscs.get_deg(3, 1, 5)
        Traceback (most recent call last):
        ...
        AssertionError: (1, 3)
        """
        assert nvs >= 1, nvs
        assert nts >= nvs, (nts, nvs)
        assert max_deg >= 1, max_deg

        for d in range(1, max_deg+1):
            if d == max_deg:
                return d

            # look ahead
            nterms = sage.all.binomial(nvs + d+1, d+1)
            if nterms > nts:
                return d

    @classmethod
    def get_auto_deg(cls, maxdeg, nvars, maxterm):
        if maxdeg:
            deg = maxdeg
            mlog.debug("using deg {}".format(deg))
        else:
            deg = cls.get_deg(nvars, maxterm)
            mlog.debug("autodeg {}".format(deg))

        return deg

    @staticmethod
    def get_terms_fixed_coefs(ss, subset_siz):
        """
        sage: from helpers.miscs import Miscs

        sage: var('x y z t s u')
        (x, y, z, t, s, u)

        sage: sorted(Miscs.get_terms_fixed_coefs([x,y], 2), key=lambda x: str(x))
        [-x, -x + y, -x - y, -y, x, x + y, x - y, y]

        sage: sorted(Miscs.get_terms_fixed_coefs([x,y^2], 2), key=lambda x: str(x))
        [-x, -y^2, -y^2 + x, -y^2 - x, x, y^2, y^2 + x, y^2 - x]

        sage: assert len(Miscs.get_terms_fixed_coefs([x,y,z], 2)) == 18
        sage: assert len(Miscs.get_terms_fixed_coefs([x,y,z], 3)) == 26
        """
        if len(ss) < subset_siz:
            subset_siz = len(ss)
        rs = []
        for ssSubset in itertools.combinations(ss, subset_siz):
            css = itertools.product(*([[0, -1, 1]] * len(ssSubset)))
            r = (sum(c*t for c, t in zip(ssSubset, cs))
                 for cs in css if not all(c == 0 for c in cs))
            rs.extend(r)

        return set(rs)

    @staticmethod
    def reduce_eqts(ps):
        """
        Return the basis (e.g., a min subset of ps that implies ps)
        of the set of eqts input ps using Groebner basis

        sage: from helpers.miscs import Miscs

        sage: var('a y b q k')
        (a, y, b, q, k)

        sage: rs =  Miscs.reduce_eqts([a*y-b==0,q*y+k-x==0,a*x-a*k-b*q==0])
        sage: assert set(rs) == set([a*y - b == 0, q*y + k - x == 0])

        sage: rs =  Miscs.reduce_eqts([x*y==6,y==2,x==3])
        sage: assert set(rs) == set([x - 3 == 0, y - 2 == 0])

        # Attribute error occurs when only 1 var, thus return as is
        sage: rs =  Miscs.reduce_eqts([x*x==4,x==2])
        sage: assert set(rs) == set([x == 2, x^2 == 4])
        """
        if len(ps) <= 1:
            return ps

        assert (p.operator() == sage.all.operator.eq for p in ps), ps
        try:
            Q = sage.all.PolynomialRing(sage.all.QQ, Miscs.get_vars(ps))
            myIdeal = Q*ps
            ps = myIdeal.radical().interreduced_basis()
            ps = [(sage.all.SR(p) == 0) for p in ps]
        except AttributeError:
            pass

        return ps

    @staticmethod
    def elim_denom(p):
        """
        Eliminate (Integer) denominators in expression operands.
        Will not eliminate if denominators is a var (e.g.,  (3*x)/(y+2)).

        Examples:
        sage: from helpers.miscs import Miscs
        sage: var('x y z')
        (x, y, z)

        sage: Miscs.elim_denom(3/4*x^2 + 7/5*y^3)
        28*y^3 + 15*x^2

        sage: Miscs.elim_denom(-3/2*x^2 - 1/24*z^2 >= (y + 1/7))
        -252*x^2 - 7*z^2 >= 168*y + 24

        sage: Miscs.elim_denom(-3/(y+2)*x^2 - 1/24*z^2 >= (y + 1/7))
        -1/24*z^2 - 3*x^2/(y + 2) >= y + 1/7

        sage: Miscs.elim_denom(x + y == 0)
        x + y == 0

        """
        try:
            def f(g): return [sage.all.Integer(o.denominator())
                              for o in g.operands()]
            denoms = f(p.lhs()) + f(p.rhs()) if p.is_relational() else f(p)
            return p * sage.all.lcm(denoms)
        except TypeError:
            return p

    @classmethod
    def get_coefs(cls, p):
        """
        Return coefficients of an expression

        sage: from helpers.miscs import Miscs
        sage: var('y')
        y
        sage: Miscs.get_coefs(3*x+5*y^2 == 9)
        [5, 3]
        """
        Q = sage.all.PolynomialRing(sage.all.QQ, cls.get_vars(p))
        rs = Q(p.lhs()).coefficients()
        return rs

    @staticmethod
    def is_repeating_rational(x):
        "check if x is a repating rational"
        assert isinstance(x, sage.rings.rational.Rational) \
            and not x.is_integer(), x

        x1 = x.n(digits=50).str(skip_zeroes=True)
        x2 = x.n(digits=100).str(skip_zeroes=True)
        return x1 != x2

    @classmethod
    def refine(cls, sols, ignoreLargeCoefs=True):
        if not sols:
            return sols
        sols = cls.reduce_eqts(sols)
        sols = [cls.elim_denom(s) for s in sols]

        def okCoefs(s): return all(
            abs(c) <= settings.MAX_LARGE_COEF or
            sage.all.mod(c, 10) == 0 or
            sage.all.mod(c, 5) == 0
            for c in cls.get_coefs(s))

        if ignoreLargeCoefs:  # don't allow large coefs
            sols_ = []
            for s in sols:
                if okCoefs(s):
                    sols_.append(s)
                else:
                    mlog.debug("large coefs: ignore {} ..".format(
                        str(s)[:settings.MAX_LARGE_COEF]))
            sols = sols_
        return sols

    @classmethod
    def solve_eqts(cls, eqts, uks, template):
        assert isinstance(eqts, list) and eqts, eqts
        assert isinstance(uks, list)and uks, uks
        assert len(eqts) >= len(uks), (len(eqts), len(uks))

        mlog.debug("solve {} uks using {} eqts".format(len(uks), len(eqts)))

        @fork(timeout=settings.EQT_SOLVER_TIMEOUT, verbose=False)
        def mysolve(eqts, uks, solution_dict):
            return sage.all.solve(eqts, *uks, solution_dict=True)

        # rs = sage.all.solve(eqts, *uks, solution_dict=True)
        rs = mysolve(eqts, uks, solution_dict=True)
        assert isinstance(rs, list), rs
        assert all(isinstance(s, dict) for s in rs), rs

        # filter sols with all uks = 0, e.g., {uk_0: 0, uk_1: 0, uk_2: 0}
        rs = [d for d in rs if not all(x == 0 for x in d.values())]

        reqts = cls.instantiate_template(template, rs)
        reqts = cls.refine(reqts)
        # print '\n'.join(map(str, eqts))
        # print uks
        # print reqts
        # CM.pause()

        return reqts

    @classmethod
    def mk_template(cls, terms, rhsVal,
                    op=sage.all.operator.eq,
                    prefix=None, retCoefVars=False):
        """
        get a template from terms.

        Examples:

        sage: from helpers.miscs import Miscs
        sage: var('a,b,x,y')
        (a, b, x, y)

        sage: Miscs.mk_template([1, a, b, x, y],0,prefix=None)
        (a*uk_1 + b*uk_2 + uk_3*x + uk_4*y + uk_0 == 0,
        a*uk_1 + b*uk_2 + uk_3*x + uk_4*y + uk_0 == 0)

        sage: Miscs.mk_template([1, x, y],0,\
        op=operator.gt,prefix=None,retCoefVars=True)
        (uk_1*x + uk_2*y + uk_0 > 0, [uk_0, uk_1, uk_2])

        sage: Miscs.mk_template([1, a, b, x, y],None,prefix=None)
        (a*uk_1 + b*uk_2 + uk_3*x + uk_4*y + uk_0,
        a*uk_1 + b*uk_2 + uk_3*x + uk_4*y + uk_0)

        sage: Miscs.mk_template([1, a, b, x, y],0,prefix='hi')
        (a*hi1 + b*hi2 + hi3*x + hi4*y + hi0 == 0,
        a*hi1 + b*hi2 + hi3*x + hi4*y + hi0 == 0)

        sage: var('x1')
        x1
        sage: Miscs.mk_template([1, a, b, x1, y],0,prefix='x')
        Traceback (most recent call last):
        ...
        AssertionError: name conflict
        """

        if not prefix:
            prefix = "uk_"
        uks = [sage.all.var(prefix + str(i)) for i in range(len(terms))]

        assert not set(terms).intersection(set(uks)), 'name conflict'

        template = sum(map(sage.all.prod, zip(uks, terms)))

        if rhsVal is not None:  # note, not None because rhsVal can be 0
            template = op(template, rhsVal)

        return template, uks if retCoefVars else template

    @classmethod
    def instantiate_template(cls, template, sols):
        """
        Instantiate a template with solved coefficient values

        sage: from helpers.miscs import Miscs
        sage: var('uk_0,uk_1,uk_2,uk_3,uk_4,r14,r15,a,b,y')
        (uk_0, uk_1, uk_2, uk_3, uk_4, r14, r15, a, b, y)

        sage: sols = [{uk_0: -2*r14 + 7/3*r15, uk_1: -1/3*r15, uk_4: r14, uk_2: r15, uk_3: -2*r14}]
        sage: Miscs.instantiate_template(uk_1*a + uk_2*b + uk_3*x + uk_4*y + uk_0 == 0, sols)
        [-2*x + y - 2 == 0, -1/3*a + b + 7/3 == 0]


        sage: Miscs.instantiate_template(uk_1*a + uk_2*b + uk_3*x + uk_4*y + uk_0 == 0, [])
        []
        """
        assert cls.is_expr(template), template

        if not sols:
            return []
        if len(sols) > 1:
            mlog.warning('instantiate_templateWithSols: len(sols) = {}'
                         .format(len(sols)))
            mlog.warning(str(sols))

        def fEq(d):
            f_ = template(d)
            uk_vars = cls.get_vars(d.values())  # e.g., r15,r16 ...

            if not uk_vars:
                return f_

            iM = sage.all.identity_matrix(len(uk_vars))  # standard basis
            rs = [dict(zip(uk_vars, l)) for l in iM.rows()]
            rs = [f_(r) for r in rs]
            return rs

        sols = [y for x in sols for y in fEq(x)]

        # remove trivial (tautology) str(x) <=> str(x)
        sols = [s for s in sols
                if not (s.is_relational() and str(s.lhs()) == str(s.rhs()))]

        return sols

    @staticmethod
    def show_removed(s, orig_siz, new_siz, elapsed_time):
        assert orig_siz >= new_siz, (orig_siz, new_siz)
        n_removed = orig_siz - new_siz
        if not n_removed:
            return
        mlog.debug("{}: removed {} invs ({:.2f}s, orig {}, new {})"
                   .format(s, n_removed, elapsed_time, orig_siz, new_siz))

    @classmethod
    def get_workload(cls, tasks, n_cpus):
        """
        sage: from helpers.miscs import Miscs

        >>> wls = Miscs.get_workload(range(12),7); [len(wl) for wl in wls]
        [1, 1, 2, 2, 2, 2, 2]

        >>> wls = Miscs.get_workload(range(12),5); [len(wl) for wl in wls]
        [2, 2, 2, 3, 3]

        >>> wls = Miscs.get_workload(range(20),7); [len(wl) for wl in wls]
        [2, 3, 3, 3, 3, 3, 3]

        >>> wls = Miscs.get_workload(range(20),20); [len(wl) for wl in wls]
        [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

        >>> wls = Miscs.get_workload(range(12),7); [len(wl) for wl in wls]
        [1, 1, 2, 2, 2, 2, 2]

        >>> wls = Miscs.get_workload(range(146), 20); [len(wl) for wl in wls]
            [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8]
        """
        assert len(tasks) >= 1, tasks
        assert n_cpus >= 1, n_cpus

        wloads = {}
        for i, task in enumerate(tasks):
            cpu_id = i % n_cpus
            wloads.setdefault(cpu_id, []).append(task)

        wloads = [wl for wl in sorted(
            wloads.values(), key=lambda wl: len(wl))]
        return wloads

    @classmethod
    def run_mp(cls, taskname, tasks, f):
        """
        Run wprocess on tasks in parallel
        """
        def wprocess(mytasks, myQ):
            rs = f(mytasks)
            if myQ is None:
                return rs
            else:
                myQ.put(rs)

        if settings.DO_MP and len(tasks) >= 2:
            from multiprocessing import (Process, Queue, cpu_count)
            Q = Queue()
            n_cpus = cpu_count()
            wloads = cls.get_workload(tasks, n_cpus=n_cpus)
            mlog.debug("{}:running {} jobs using {} threads: {}".format(
                taskname, len(tasks), len(wloads), list(map(len, wloads))))

            workers = [Process(target=wprocess, args=(wl, Q)) for wl in wloads]

            for w in workers:
                w.start()

            wrs = [x for _ in workers for x in Q.get()]
        else:
            wrs = wprocess(tasks, myQ=None)

        return wrs

    @staticmethod
    def simplify_idxs(ordered_idxs, imply_f):
        """
        attempt to remove i in idxs if imply_f returns true
        Note: the order of idxs determine what to get checked (and removed) 
        """
        assert ordered_idxs == list(range(len(ordered_idxs))), ordered_idxs

        results = set(ordered_idxs)

        for i in reversed(ordered_idxs):
            if i not in results:
                continue
            others = results - {i}
            if others and imply_f(others, i):
                results = others

        return sorted(results)


class Z3(object):
    @classmethod
    def is_var(cls, v):
        return z3.is_const(v) and v.decl().kind() == z3.Z3_OP_UNINTERPRETED

    @classmethod
    def _get_vars(cls, f, rs):
        """
        Helper method to obtain variables from a formula f recursively.
        Results are stored in the list rs.
        """
        assert z3.is_expr(f) or z3.is_const(f), f
        if z3.is_const(f):
            if cls.is_var(f):
                rs.add(f)
        else:
            for c in f.children():
                cls._get_vars(c, rs)

    @classmethod
    @cached_function
    def get_vars(cls, f):
        """
        sage: from helpers.miscs import Z3
        sage: import z3
        sage: x,y,z = z3.Ints("x y z")
        sage: assert(Z3.get_vars(z3.And(x + y == z , y + z == z)) == {z, y, x})
        """
        assert z3.is_expr(f), f

        rs = set()
        cls._get_vars(f, rs)
        return frozenset(rs)

    @classmethod
    def create_solver(cls):
        solver = z3.Solver()
        solver.set(timeout=settings.SOLVER_TIMEOUT)
        return solver

    @classmethod
    def extract(self, models):
        assert models is None or models is False \
            or (isinstance(models, list) and
                all(isinstance(m, z3.ModelRef) for m in models)
                and models), models

        cexs = set()
        isSucc = models is not None
        if isSucc and models:  # disproved
            cexs = [{str(s): sage.all.sage_eval(str(model[s])) for s in model}
                    for model in models]
        return cexs, isSucc

    @classmethod
    def get_models(cls, f, k):
        """
        Returns the first k models satisfiying f.
        If f is not satisfiable, returns False.
        If f cannot be solved, returns None
        If f is satisfiable, returns the first k models
        Note that if f is a tautology, i.e., True, then the result is []
        """
        assert z3.is_expr(f), f
        assert k >= 1, k

        solver = cls.create_solver()
        solver.add(f)

        models = []
        i = 0
        while solver.check() == z3.sat and i < k:
            i = i + 1
            m = solver.model()
            if not m:  # if m == []
                break
            models.append(m)
            # create new constraint to block the current model
            block = z3.Not(z3.And([v() == m[v] for v in m]))
            solver.add(block)

        stat = solver.check()

        if stat == z3.unknown:
            rs = None
        elif stat == z3.unsat and i == 0:
            rs = False
        else:
            rs = models

        assert not (isinstance(rs, list) and not rs), rs
        return rs, stat

    @classmethod
    def imply(cls, fs, g, use_reals):
        """
        sage: from helpers.miscs import Z3

        sage: var('x y')
        (x, y)
        sage: assert Z3.imply([x-6==0],x*x-36==0,use_reals=False)
        sage: assert Z3.imply([x-6==0,x+6==0],x*x-36==0,use_reals=False)
        sage: assert not Z3.imply([x*x-36==0],x-6==0,use_reals=False)
        sage: assert not Z3.imply([x-6==0],x-36==0,use_reals=False)
        sage: assert Z3.imply([x-7>=0], x>=6,use_reals=False)
        sage: assert not Z3.imply([x-7>=0], x>=8,use_reals=False)
        sage: assert not Z3.imply([x-6>=0], x-7>=0,use_reals=False)
        sage: assert not Z3.imply([x-7>=0,y+5>=0],x+y-3>=0,use_reals=False)
        sage: assert Z3.imply([x-7>=0,y+5>=0],x+y-2>=0,use_reals=False)
        sage: assert Z3.imply([x-2*y>=0,y-1>=0],x-2>=0,use_reals=False)
        sage: assert not Z3.imply([],x-2>=0,use_reals=False)
        sage: assert Z3.imply([x-7>=0,y+5>=0],x+y-2>=0,use_reals=False)
        sage: assert Z3.imply([x^2-9>=0,x>=0],x-3>=0,use_reals=False)
        sage: assert not Z3.imply([1/2*x**2 - 3/28*x + 1 >= 0],1/20*x**2 - 9/20*x + 1 >= 0,use_reals=True)
        sage: assert Z3.imply([1/20*x**2 - 9/20*x + 1 >= 0],1/2*x**2 - 3/28*x + 1 >= 0,use_reals=True)
        sage: assert Z3.imply([x-6==0],x*x-36==0,use_reals=False)
        sage: assert not Z3.imply([x+7>=0,y+5>=0],x*y+36>=0,use_reals=False)
        sage: assert not Z3.imply([x+7>=0,y+5>=0],x*y+35>=0,use_reals=False)
        sage: assert not Z3.imply([x+7>=0,y+5>=0],x*y-35>=0,use_reals=False)
        sage: assert not Z3.imply([x+7>=0],x-8>=0,use_reals=False)
        sage: assert Z3.imply([x+7>=0],x+8>=0,use_reals=False)
        sage: assert Z3.imply([x+7>=0],x+8.9>=0,use_reals=True)
        sage: assert Z3.imply([x>=7,y>=5],x*y>=35,use_reals=False)
        sage: assert not Z3.imply([x>=-7,y>=-5],x*y>=35,use_reals=False)
        """

        assert all(Miscs.is_expr(f) for f in fs), fs
        assert Miscs.is_expr(g), g
        assert isinstance(use_reals, bool), use_reals

        if not fs:
            return False  # conservative approach
        fs = [cls.toZ3(f, use_reals, use_mod=False) for f in fs]
        g = cls.toZ3(g, use_reals, use_mod=False)
        return cls._imply(fs, g)

    @classmethod
    def _imply(cls, fs, g, is_conj=True):
        assert fs
        if is_conj:  # And(fs) => g
            claim = z3.Implies(z3.And(fs), g)
        else:  # g => Or(fs)
            claim = z3.Implies(g, z3.Or(fs))

        models, _ = cls.get_models(z3.Not(claim), k=1)
        return models is False

    @classmethod
    def _mycmp_(cls, f, g):
        """
        sage: from helpers.miscs import Z3
        sage: import z3

        sage: x,y = z3.Ints('x y')
        sage: sorted([x>=z3.IntVal('0'), x>= z3.IntVal('3') ,  x>= z3.IntVal('3'), x>= z3.IntVal('1'), x>= z3.IntVal('10'), y - x >= z3.IntVal('20')], cmp=Z3._mycmp_)
        [y - x >= 20, x >= 0, x >= 1, x >= 3, x >= 3, x >= 10]

        """
        claim = f == g
        models, _ = cls.get_models(z3.Not(claim), k=1)
        if models is False:
            return 0  # ==
        claim = z3.Implies(f, g)
        models, _ = cls.get_models(z3.Not(claim), k=1)
        if models is False:
            return 1  # f > g
        else:
            return -1

    @classmethod
    @cached_function
    def toZ3(cls, p, use_reals, use_mod):
        """
        Convert a Sage expression to a Z3 expression

        Initially implements with a dictionary containing variables
        e.g. {x:Real('x')} but the code is longer and more complicated.
        This implemention does not require a dictionary pass in.

        sage: from helpers.miscs import Z3
        sage: Z3.toZ3(x*x*x, False, use_mod=False)
        x*x*x
        """
        assert (Miscs.is_expr(p) or Miscs.is_int(p) or
                isinstance(p, int)), (p, type(p))
        assert isinstance(use_reals, bool), use_reals
        assert isinstance(use_mod, bool), use_mod

        def retval(p):
            if p.is_symbol():
                _f = z3.Real if use_reals else z3.Int
            else:
                _f = z3.RealVal if use_reals else z3.IntVal

            try:
                return _f(str(p))
            except Exception:
                assert False, "cannot parse {}".format(p)

        if isinstance(p, int) or Miscs.is_int(p):
            _f = z3.RealVal if use_reals else z3.IntVal
            res = _f(str(p))

        else:
            oprs = p.operands()
            if oprs:
                op = p.operator()

                # z3 has problem w/ t^c , so use t*t*t..
                if op == operator.pow:
                    assert len(oprs) == 2, oprs
                    t, c = oprs
                    t = cls.toZ3(t, use_reals, use_mod)
                    if use_mod:
                        c = cls.toZ3(c, use_reals, use_mod)
                        res = reduce(operator.mod, [t, c])
                    else:
                        if c == -1:  # 1/x
                            res = 1/t
                        else:
                            assert c >= 0
                            vs = [t] * c
                            res = reduce(operator.mul, vs)
                else:
                    oprs = [cls.toZ3(o, use_reals, use_mod) for o in oprs]
                    res = reduce(op, oprs)

            else:
                res = retval(p)

        assert z3.is_expr(res), res
        if use_mod:
            mlog.debug("mod hack: {} => {}".format(p, res))
        return res

    @classmethod
    def parse(cls, node, use_reals):

        # print(ast.dump(node))

        if isinstance(node, str):
            tnode = ast.parse(node)
            tnode = tnode.body[0].value
            try:
                expr = cls.parse(tnode, use_reals)
                expr = z3.simplify(expr)
                return expr
            except NotImplementedError:
                mlog.error("cannot parse: '{}'\n{}".format(
                    node, ast.dump(tnode)))
                raise

        elif isinstance(node, ast.BoolOp):
            vals = [cls.parse(v, use_reals) for v in node.values]
            op = cls.parse(node.op, use_reals)
            return op(vals)

        elif isinstance(node, ast.And):
            return z3.And

        elif isinstance(node, ast.Or):
            return z3.Or

        elif isinstance(node, ast.BinOp):
            left = cls.parse(node.left, use_reals)
            right = cls.parse(node.right, use_reals)
            op = cls.parse(node.op, use_reals)
            return op(left, right)

        elif isinstance(node, ast.UnaryOp):
            operand = cls.parse(node.operand, use_reals)
            op = cls.parse(node.op, use_reals)
            return op(operand)

        elif isinstance(node, ast.Compare):
            assert len(node.ops) == 1 and len(
                node.comparators) == 1, ast.dump(node)
            left = cls.parse(node.left, use_reals)
            right = cls.parse(node.comparators[0], use_reals)
            op = cls.parse(node.ops[0], use_reals)
            return op(left, right)

        elif isinstance(node, ast.Name):
            f = z3.Real if use_reals else z3.Int
            return f(str(node.id))

        elif isinstance(node, ast.Num):
            f = z3.RealVal if use_reals else z3.IntVal
            return f(str(node.n))

        elif isinstance(node, ast.Add):
            return operator.add
        elif isinstance(node, ast.Mult):
            return operator.mul
        elif isinstance(node, ast.Div):
            return operator.truediv  # tvn:  WARNING: might not be accurate
        elif isinstance(node, ast.FloorDiv):
            return operator.truediv  # tvn:  WARNING: might not be accurate
        elif isinstance(node, ast.Mod):
            return operator.mod
        elif isinstance(node, ast.Pow):
            return operator.pow
        elif isinstance(node, ast.Sub):
            return operator.sub
        elif isinstance(node, ast.USub):
            return operator.neg
        elif isinstance(node, ast.Eq):
            return operator.eq
        elif isinstance(node, ast.NotEq):
            return operator.ne
        elif isinstance(node, ast.Lt):
            return operator.lt
        elif isinstance(node, ast.LtE):
            return operator.le
        elif isinstance(node, ast.Gt):
            return operator.gt
        elif isinstance(node, ast.GtE):
            return operator.ge

        else:
            raise NotImplementedError(ast.dump(node))

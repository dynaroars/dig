from collections.abc import Iterable
from collections import defaultdict, OrderedDict
from time import time

import pdb
import itertools
import functools
import operator

import multiprocessing
import queue


import sympy
from sympy.solvers.solveset import linsolve

import helpers.vcommon as CM
import settings

DBG = pdb.set_trace

mlog = CM.getLogger(__name__, settings.logger_level)


class Miscs:
    @staticmethod
    def msage_eval(s, d):
        assert all(isinstance(k, str) and Miscs.is_expr(v)
                   for k, v in d.items()), d
        while True:
            try:
                return sage.all.sage_eval(s, d)
            except NameError as e:  # name 'yy' is not defined
                symb = str(e).split("'")[1]
                mlog.debug(f"create new symbol {symb}")
                d[symb] = sage.all.var(symb)

    # @staticmethod
    # def is_real(x):
    #     return isinstance(x, sage.rings.real_mpfr.RealLiteral)

    # @staticmethod
    # def is_int(x):
    #     return isinstance(x, sage.rings.integer.Integer)

    # @classmethod
    # def is_num(cls, x):
    #     return cls.is_real(x) or cls.is_int(x)

    # @staticmethod
    # def is_rel(f, rel=None):
    #     """
    #     # >>> assert not Miscs.is_rel(7.2)
    #     # >>> assert not Miscs.is_rel(x)
    #     # >>> assert not Miscs.is_rel(x+7)
    #     # >>> assert Miscs.is_rel(x==3,operator.eq)

    #     # >>> assert Miscs.is_rel(x<=3,operator.le)
    #     # >>> assert not Miscs.is_rel(x<=3,operator.lt)
    #     # >>> assert not Miscs.is_rel(x+3,operator.lt)

    #     # >>> y = var('y')
    #     # >>> assert Miscs.is_rel(x+y<=3)
    #     """
    #     try:
    #         if not f.is_relational():
    #             return False

    #         if rel is None:
    #             return True
    #         else:
    #             return f.operator() == rel

    #     except AttributeError:
    #         return False

    @classmethod
    def is_eq(cls, f):
        return cls.is_rel(f, operator.eq)

    @staticmethod
    def is_expr(x):
        return isinstance(x, sympy.Expr)

    @classmethod
    def get_vars(cls, ps):
        """
        Returns a list of uniq variables from a list of properties

        Examples:

        # >>> var('a b c x')
        (a, b, c, x)

        # >>> assert [a, b, c, x] == Miscs.get_vars([x**(a*b) + a**2+b+2==0, c**2-b==100, b**2 + c**2 + a**3>= 1])
        # >>> assert Miscs.get_vars(a**2+b+5*c+2==0) == [a, b, c]
        # >>> assert Miscs.get_vars(x+x**2) == [x]
        # >>> assert Miscs.get_vars([3]) == []
        # >>> assert Miscs.get_vars((3,'x + c',x+b)) == [b, x]
        """

        ps = ps if isinstance(ps, Iterable) else [ps]
        ps = [p for p in ps if cls.is_expr(p)]
        vs = [v for p in ps for v in p.free_symbols]
        return sorted(set(vs), key=str)

    # @cached_function
    @staticmethod
    def str2rat(s):
        """
        Convert the input 's' to a rational number if possible.

        Examples:

        # >>> assert Miscs.str2rat('.3333333') == 3333333/10000000
        # >>> assert Miscs.str2rat('3/7') == 3/7
        # >>> assert Miscs.str2rat('1.') == 1
        # >>> assert Miscs.str2rat('1.2') == 6/5
        # >>> assert Miscs.str2rat('.333') == 333/1000
        # >>> assert Miscs.str2rat('-.333') == -333/1000
        # >>> assert Miscs.str2rat('-12.13') == -1213/100

        # Returns None because cannot convert this str
        # >>> Miscs.str2rat('333333333333333s')
        Traceback (most recent call last):
        ...
        TypeError: unable to convert '333333333333333s' to a real number


        Note: this version seems to be the *fastest*
        among several ones I've tried
        %timeit str2rat('322')
        """
        try:
            return sympy.Rational(s)
        except TypeError:
            pass

        return sage.all.QQ(sage.all.RR(s))

    @staticmethod
    def str2list(s):
        assert isinstance(s, str), s
        return tuple(sage.all.sage_eval(s))

    @classmethod
    def init_terms(cls, vs, deg, rate):
        assert vs, vs
        assert deg >= 1, deg
        assert rate >= 0.1, rate

        symbols = [sympy.Symbol(v) for v in vs]
        terms = cls.get_terms(symbols, deg)
        uks = [sympy.Symbol(f"uk_{i}") for i in range(len(terms))]
        assert not set(terms).intersection(set(uks)), "name conflict"
        n_eqts_needed = int(rate * len(uks))
        return terms, uks, n_eqts_needed

    @staticmethod
    def get_terms(ss, deg):
        """
        get a list of terms from the given list of vars and deg
        the number of terms is len(rs) == binomial(len(ss)+d, d)

        Note: itertools is faster than Sage's MultichooseNK(len(ss)+1,deg)

        # >>> ts = Miscs.get_terms(list(var('a b')), 3)
        # >>> assert ts == [1, a, b, a**2, a*b, b**2, a**3, a**2*b, a*b**2, b**3]

        # >>> Miscs.get_terms(list(var('a b c d e f')), 3)
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
        assert ss and all(isinstance(s, sympy.Symbol) for s in ss), ss
        ss_ = ([1] if ss else (1,)) + ss
        combs = itertools.combinations_with_replacement(ss_, deg)
        terms = [sympy.prod(c) for c in combs]
        return terms

    @classmethod
    def get_deg(cls, nvs, nts, max_deg=7):
        """
        Generates a degree wrt to a (maximum) number of terms (nss)

        # >>> assert Miscs.get_deg(3, 4, 5) == 1
        # >>> Miscs.get_deg(3, 1, 5)
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
            nterms = sympy.binomial(nvs + d + 1, d + 1)
            if nterms > nts:
                return d

    @classmethod
    def get_auto_deg(cls, maxdeg, nvars, maxterm):
        if maxdeg:
            deg = maxdeg
            mlog.debug(f"using deg {deg}")
        else:
            deg = cls.get_deg(nvars, maxterm)
            mlog.debug(f"autodeg {deg}")

        return deg

    @staticmethod
    def get_terms_fixed_coefs(ss, subset_siz, icoef, do_create_terms=True):
        """
        if do_create_terms = True, then return x*y,  otherwise, return (x,y)

        # >>> var('x y z t s u')
        (x, y, z, t, s, u)
        # >>> sorted(Miscs.get_terms_fixed_coefs([x,y], 2, 1), key=lambda x: str(x))
        [-x, -x + y, -x - y, -y, x, x + y, x - y, y]
        # >>> sorted(Miscs.get_terms_fixed_coefs([x,y**2], 2, 1), key=lambda x: str(x))
        [-x, -y^2, -y^2 + x, -y^2 - x, x, y^2, y^2 + x, y^2 - x]
        # >>> assert len(Miscs.get_terms_fixed_coefs([x,y,z], 2, 1)) == 18
        # >>> assert len(Miscs.get_terms_fixed_coefs([x,y,z], 3, 1)) == 26
        # >>> assert len(Miscs.get_terms_fixed_coefs([x,y,z], 2, 3)) == 126
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

    @classmethod
    def reduce_eqts(cls, ps):
        """
        Return the basis (e.g., a min subset of ps that implies ps)
        of the set of polynomial eqts using Groebner basis.
        Warning 1: Grobner basis sometimes results in a larger set of eqts,
        in which case we return the original set of eqts.
        Warning 2: seems to get stuck often.  So had to give it "nice" polynomials

        # >>> var('a y b q k')
        (a, y, b, q, k)

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

        ps_ = sympy.groebner(ps, *cls.get_vars(ps))
        ps_ = [x for x in ps_]
        mlog.debug(f"Grobner basis: got {len(ps_)} ps from {len(ps)} ps")
        if len(ps_) <= len(ps):
            return ps_
        else:
            return ps

    @staticmethod
    def elim_denom(p):
        """
        Eliminate (Integer) denominators in expression operands.
        Will not eliminate if denominators is a var (e.g.,  (3*x)/(y+2)).

        Examples:
        # >>> (Python) doesn't show fractions well
        for these doctests, use sage, because

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

    @classmethod
    def get_coefs(cls, p):
        """
        Return coefficients of an expression

        >>> x,y,z = sympy.symbols('x y z')
        >>> Miscs.get_coefs(3*x+5*x*y**2)
        [3, 5]
        """
        return list(p.as_coefficients_dict().values())

    @staticmethod
    def is_repeating_rational(x):
        """check if x is a repating rational"""

        assert isinstance(
            x, sage.rings.rational.Rational) and not x.is_integer(), x

        x1 = x.n(digits=50).str(skip_zeroes=True)
        x2 = x.n(digits=100).str(skip_zeroes=True)
        return x1 != x2

    @classmethod
    def reduce_with_timeout(cls, ps, timeout=settings.EQT_REDUCE_TIMEOUT):
        Q = multiprocessing.Queue()

        def wprocess(ps, myQ):
            rs = cls.reduce_eqts(ps)
            myQ.put(rs)

        w = multiprocessing.Process(
            target=wprocess,
            args=(
                ps,
                Q,
            ),
        )
        w.start()
        # mlog.debug(f"start reduce_eqts for {len(ps)} eqts")
        try:
            newps = Q.get(timeout=timeout)
            mlog.debug(
                f"done reduce_eqts, got {len(newps)} ps from  {len(ps)} ps")
            ps = newps
        except queue.Empty:
            mlog.warning(
                f"timeout reduce_eqts for {len(ps)} eqts, terminate worker")
            w.terminate()

        w.join()
        w.close()
        return ps

    @classmethod
    def is_nice_coef(cls, c, lim):
        return abs(c) <= lim or c % 10 == 0 or c % 5 == 0

    @classmethod
    def is_nice_eqt(cls, eqt, lim):
        return all(cls.is_nice_coef(c, lim) for c in cls.get_coefs(eqt))

    @classmethod
    def remove_ugly(cls, ps, lim=settings.MAX_LARGE_COEF_INTERMEDIATE):
        ps_ = []
        for p in ps:
            if cls.is_nice_eqt(p, lim):
                # print(f"append {p}")
                ps_.append(p)
            else:
                mlog.debug(f"ignore large coefs {str(p)[:50]} ..")

        return ps_

    @classmethod
    def refine(cls, eqts):

        if not eqts:
            return eqts

        nice_eqts = [cls.elim_denom(s) for s in eqts]
        nice_eqts = cls.remove_ugly(nice_eqts)

        eqts = cls.reduce_with_timeout(eqts)
        eqts = [cls.elim_denom(s) for s in eqts]
        eqts = cls.remove_ugly(eqts)

        eqts = cls.reduce_with_timeout(list(set(eqts + nice_eqts)))
        eqts = [cls.elim_denom(s) for s in eqts]
        eqts = cls.remove_ugly(eqts)

        return eqts

    @classmethod
    def solve_eqts(cls, eqts, terms, uks):
        assert isinstance(eqts, list) and eqts, eqts
        assert isinstance(terms, list) and terms, terms
        assert isinstance(uks, list) and uks, uks
        assert len(terms) == len(uks), (terms, uks)
        assert len(eqts) >= len(uks), (len(eqts), len(uks))

        mlog.debug(f"solving {len(uks)} uks using {len(eqts)} eqts")
        sol = linsolve(eqts, uks)
        vals = list(list(sol)[0])
        # filter sol with all uks = 0, e.g., {uk_0: 0, uk_1: 0, uk_2: 0}
        if all(v == 0 for v in vals):
            return []

        eqts_ = cls.instantiate_template(terms, uks, vals)
        eqts_ = cls.refine(eqts_)
        return [sympy.Eq(eqt, 0) for eqt in eqts_]

    @classmethod
    def mk_template_NOTUSED(cls, terms, rv, prefix=None, ret_coef_vs=False):
        """
        get a template from terms.

        Examples:

        # >>> var('a,b,x,y')
        (a, b, x, y)

        # >>> Miscs.mk_template([1, a, b, x, y],0,prefix=None)
        (a*uk_1 + b*uk_2 + uk_3*x + uk_4*y + uk_0 == 0,
         a*uk_1 + b*uk_2 + uk_3*x + uk_4*y + uk_0 == 0)

        # >>> Miscs.mk_template([1, x, y],0, op=operator.gt,prefix=None,ret_coef_vs=True)
        (uk_1*x + uk_2*y + uk_0 > 0, [uk_0, uk_1, uk_2])

        # >>> Miscs.mk_template([1, a, b, x, y],None,prefix=None)
        (a*uk_1 + b*uk_2 + uk_3*x + uk_4*y + uk_0,
         a*uk_1 + b*uk_2 + uk_3*x + uk_4*y + uk_0)

        # >>> Miscs.mk_template([1, a, b, x, y],0,prefix='hi')
        (a*hi1 + b*hi2 + hi3*x + hi4*y + hi0 == 0,
         a*hi1 + b*hi2 + hi3*x + hi4*y + hi0 == 0)

        # >>> var('x1')
        x1
        # >>> Miscs.mk_template([1, a, b, x1, y],0,prefix='x')
        Traceback (most recent call last):
        ...
        AssertionError: name conflict
        """

        assert rv is not None and isinstance(rv, int), rv

        if not prefix:
            prefix = "uk_"
        uks = [sympy.Symbol(prefix + str(i)) for i in range(len(terms))]

        assert not set(terms).intersection(set(uks)), "name conflict"

        template = sum(map(sympy.prod, zip(uks, terms)))

        if rv != 0:  #
            template = template - rv

        return template, uks if ret_coef_vs else template

    @classmethod
    def instantiate_template(cls, ts, uks, vs):
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
        assert isinstance(vs, list), vs
        assert isinstance(ts, list) and ts, ts
        assert isinstance(uks, list) and uks, uks
        assert len(ts) == len(uks) == len(vs), (ts, uks, vs)

        st = time()
        cs = [(t, u, v) for t, u, v in zip(ts, uks, vs) if v != 0]
        ts_, uks_, vs_ = zip(*cs)

        eqt = sum(t*v for t, v in zip(ts_, vs_))

        uk_vs = cls.get_vars(vs_)

        if not uk_vs:
            return eqt

        identity_m = [{uk: (1 if j == i else 0) for j, uk in enumerate(uk_vs)}
                      for i, uk in enumerate(uk_vs)]

        sols = [eqt.xreplace(d) for d in identity_m]
        print('instantiate mis', time() - st)
        return sols

    @staticmethod
    def show_removed(s, orig_siz, new_siz, elapsed_time):
        assert orig_siz >= new_siz, (orig_siz, new_siz)
        n_removed = orig_siz - new_siz
        mlog.debug(
            f"{s}: removed {n_removed} invs "
            f"in {elapsed_time:.2f}s (orig {orig_siz}, new {new_siz})"
        )

    @staticmethod
    def simplify_idxs(ordered_idxs, imply_f):
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
    def create_dict(l):
        """
        given a list of set of type [(k1,v1),..,(kn,vn)]
        generates a dict where keys are k's and values are [v's]
        e.g.,

        # >>> Miscs.create_dict([('a',1),['b',2],('a',3),('c',4),('b',10)]) 
        {'a': [1, 3], 'b': [2, 10], 'c': [4]}
        """
        return functools.reduce(lambda d, kv: d.setdefault(kv[0], []).append(kv[1]) or d, l, {})

    @staticmethod
    def merge_dict(l):
        return functools.reduce(lambda x, y: OrderedDict(list(x.items()) + list(y.items())), l, {})


class MP:
    @staticmethod
    def get_workload(tasks, n_cpus):
        """
        # >>> wls = MP.get_workload(range(12),7); [len(wl) for wl in wls]
        [1, 1, 2, 2, 2, 2, 2]

        # >>> wls = MP.get_workload(range(12),5); [len(wl) for wl in wls]
        [2, 2, 2, 3, 3]

        # >>> wls = MP.get_workload(range(20),7); [len(wl) for wl in wls]
        [2, 3, 3, 3, 3, 3, 3]

        # >>> wls = MP.get_workload(range(20),20); [len(wl) for wl in wls]
        [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

        # >>> wls = MP.get_workload(range(12),7); [len(wl) for wl in wls]
        [1, 1, 2, 2, 2, 2, 2]

        # >>> wls = MP.get_workload(range(146), 20); [len(wl) for wl in wls]
            [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8]
        """
        assert len(tasks) >= 1, tasks
        assert n_cpus >= 1, n_cpus

        wloads = defaultdict(list)
        for i, task in enumerate(tasks):
            cpu_id = i % n_cpus
            wloads[cpu_id].append(task)

        wloads = [wl for wl in sorted(wloads.values(), key=lambda wl: len(wl))]

        return wloads

    @staticmethod
    def run_mp(taskname, tasks, f, DO_MP):
        """
        Run wprocess on tasks in parallel
        """

        def wprocess(mytasks, myQ):
            rs = None
            try:
                rs = f(mytasks)
            except BaseException as ex:
                mlog.debug(f"Got exception in worker: {ex}")
                if myQ is None:
                    raise
                else:
                    rs = ex

            if myQ is None:
                return rs
            else:
                myQ.put(rs)

        n_cpus = multiprocessing.cpu_count()
        if DO_MP and len(tasks) >= 2 and n_cpus >= 2:
            Q = multiprocessing.Queue()
            wloads = MP.get_workload(tasks, n_cpus=n_cpus)
            mlog.debug(
                f"{taskname}:running {len(tasks)} jobs "
                f"using {len(wloads)} threads: {list(map(len, wloads))}"
            )

            workers = [
                multiprocessing.Process(target=wprocess, args=(wl, Q)) for wl in wloads
            ]

            for w in workers:
                w.start()

            wrs = []
            for _ in workers:
                rs = Q.get()
                if isinstance(rs, list):
                    wrs.extend(rs)
                else:
                    mlog.debug(f"Got exception from worker: {rs}")
                    raise rs

        else:
            wrs = wprocess(tasks, myQ=None)

        return wrs


if __name__ == "__main__":
    # import doctest
    # doctest.testmod()

    x, a, y, b, q, k = sympy.symbols('x, a, y, b, q, k')
    rs = sympy.groebner([a*y-b, q*y+k-x, a*x-a*k-b*q], x, a, y, b, q, k)
    # GroebnerBasis([-k - q*y + x, a*y - b], x, a, y, b, q, k, domain='ZZ', order='lex')
    print(rs)
    DBG()

    rs = sympy.groebner([x*y - 6, y - 2, x - 3], x, a, y, b, q, k)
    # GroebnerBasis([x - 3, y - 2], x, a, y, b, q, k, domain='ZZ', order='lex')
    print(rs)

    # print(Miscs.elim_denom(sympy.Rational(3, 4)*x**2 + sympy.Rational(7, 5)*y**3))

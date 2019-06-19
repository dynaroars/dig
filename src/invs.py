from abc import ABCMeta, abstractmethod
import itertools
from time import time
import pdb
import operator

import z3
import sage.all
from sage.all import cached_function

import vcommon as CM
import settings
from miscs import Miscs, Z3

from ds import Trace, Traces, DTraces
dbg = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


class Inv(object):
    __metaclass__ = ABCMeta

    PROVED = "p"
    DISPROVED = "d"
    UNKNOWN = "u"

    def __init__(self, inv, stat=None):
        """
        stat = None means never been checked
        """
        assert (inv == 0  # FalseInv
                or (isinstance(inv, tuple)
                    and (len(inv) == 2  # PrePost
                         or len(inv) == 4))  # Max/MinPlus
                or inv.is_relational()), inv

        assert stat in {None, Inv.PROVED, Inv.DISPROVED, Inv.UNKNOWN}

        self.inv = inv
        if stat is None:
            self.reset_stat()
        else:
            self.stat = stat

    def __hash__(self): return hash(self.inv)

    def __repr__(self): return repr(self.inv)

    def __eq__(self, o): return self.inv.__eq__(o.inv)

    def __ne__(self, o): return not self.inv.__eq__(o.inv)

    def get_stat(self):
        return self._stat

    def set_stat(self, stat):
        assert stat in {self.PROVED, self.DISPROVED, self.UNKNOWN}, stat
        self._stat = stat
    stat = property(get_stat, set_stat)

    def reset_stat(self):
        self._stat = None

    def test(self, traces):
        assert isinstance(traces, Traces), traces
        return all(self.test_single_trace(trace) for trace in traces)

    @property
    def is_proved(self): return self.stat == self.PROVED

    @property
    def is_disproved(self): return self.stat == self.DISPROVED

    @property
    def is_unknown(self): return self.stat == self.UNKNOWN


class FalseInv(Inv):
    def __init__(self, inv, stat=None):
        assert inv == 0, inv
        super(FalseInv, self).__init__(inv, stat)

    def __str__(self, print_stat=False):
        s = str(self.inv)
        if print_stat:
            s = "{} {}".format(s, self.stat)
        return s

    def expr(self, _):
        return z3.BoolVal(False)

    @classmethod
    def mk(cls):
        return FalseInv(0)


class RelInv(Inv):
    __metaclass__ = ABCMeta

    def __init__(self, rel, stat=None):
        assert (rel.operator() == operator.eq or
                rel.operator() == operator.le or
                rel.operator() == operator.lt), rel

        super(RelInv, self).__init__(rel, stat)

    def __str__(self, print_stat=False):
        s = self.strOfExp(self.inv)
        if print_stat:
            s = "{} {}".format(s, self.stat)
        return s

    @cached_function
    def strOfExp(p):
        """
        -p^3 => -(p*p*p)
        n*p^4 => n*(p*p*p*p)
        ab^3 => (ab*ab*ab)
        x*y*z^3 => x*y*(z*z*z)
        """
        assert Miscs.is_expr(p), p

        def getPow(p):
            try:
                oprs = p.operands()
            except Exception:
                return []

            if p.operator() == sage.all.operator.pow:
                x, y = oprs
                pow_s = '*'.join(
                    [str(x) if x.is_symbol() else "({})".format(x)] * int(y))
                return [(str(p), '({})'.format(pow_s))]

            else:
                return [xy for o in oprs for xy in getPow(o)]

        s = str(p)
        if '^' not in s:
            return s
        rs = getPow(p)
        for (x, y) in rs:
            s = s.replace(x, y)
        return s

    def test_single_trace(self, trace):
        assert isinstance(trace, Trace), trace

        # temp fix: disable traces that wih extreme large values
        # (see geo1 e.g., 435848050)
        if any(x > trace.maxVal for x in trace.vs):
            mlog.debug("skip trace with large val: {}".format(self))
            return True

        # temp fix: disable repeating rational when testing equality
        if (isinstance(self, EqtInv) and
            any(not x.is_integer() and Miscs.isRepeatingRational(x)
                for x in trace.vs)):
            mlog.debug("skip trace with repeating rational {}".format(self))
            return True

        try:
            bval = self.inv.subs(trace.mydict)
            bval = bool(bval)
            return bval
        except ValueError:
            mlog.debug("{}: failed test".format(self))
            return False

    def expr(self, use_reals):
        """
        cannot make this as property because z3 expr is ctype,
        not compat with multiprocessing Queue
        """
        return Z3.toZ3(self.inv, use_reals, use_mod=False)


class EqtInv(RelInv):
    def __init__(self, eqt, stat=None):
        assert eqt.operator() == operator.eq, eqt
        super(EqtInv, self).__init__(eqt, stat)


class IeqInv(RelInv):
    def __init__(self, ieq, stat=None):
        """
        For both <=  (normal OctInvs)  or < (Precond in PrePost)
        """
        assert (ieq.operator() == operator.le or
                ieq.operator() == operator.lt), ieq

        super(IeqInv, self).__init__(ieq, stat)


class MPInv(Inv):
    """
    sage: x, y, z = sage.all.var('x y z')
    sage: terms = MPInv.get_terms([x,y,z])
    sage: mps = [MPInv(lh, rh, is_maxplus=True, is_ieq=True) \
                 for lh, rh in terms]
    sage: print('\n'.join('***{}***\n{}\n{}\n{}'.format(t, m, m.term, m.ite) \
                for t, m in zip(terms,mps)))    
    ***(x, (0,))***
    lambda x: x <= 0
    lambda x: x
    x <= 0
    ***(x, (y, 0))***
    lambda x,y: x - max(y, 0) <= 0
    lambda x,y: x - max(y, 0)
    If(y >= 0, x <= y, x <= 0)
    ***(x, (y, z))***
    lambda x,y,z: x - max(y, z) <= 0
    lambda x,y,z: x - max(y, z)
    If(y >= z, x <= y, x <= z)
    ***(x, (y, z, 0))***
    lambda x,y,z: x - max(y, z, 0) <= 0
    lambda x,y,z: x - max(y, z, 0)
    If(And(y >= z, y >= 0), x <= y, If(And(z >= y, z >= 0), x <= z, x <= 0))
    ***(x, (y,))***
    lambda x,y: x - y <= 0
    lambda x,y: x - y
    x <= y
    ***(x, (z, 0))***
    lambda x,z: x - max(z, 0) <= 0
    lambda x,z: x - max(z, 0)
    If(z >= 0, x <= z, x <= 0)
    ***(x, (z,))***
    lambda x,z: x - z <= 0
    lambda x,z: x - z
    x <= z
    ***(y, (0,))***
    lambda y: y <= 0
    lambda y: y
    y <= 0
    ***(y, (x, 0))***
    lambda x,y: y - max(x, 0) <= 0
    lambda x,y: y - max(x, 0)
    If(x >= 0, y <= x, y <= 0)
    ***(y, (x, z))***
    lambda x,y,z: y - max(x, z) <= 0
    lambda x,y,z: y - max(x, z)
    If(x >= z, y <= x, y <= z)
    ***(y, (x, z, 0))***
    lambda x,y,z: y - max(x, z, 0) <= 0
    lambda x,y,z: y - max(x, z, 0)
    If(And(x >= z, x >= 0), y <= x, If(And(z >= x, z >= 0), y <= z, y <= 0))
    ***(y, (z, 0))***
    lambda y,z: y - max(z, 0) <= 0
    lambda y,z: y - max(z, 0)
    If(z >= 0, y <= z, y <= 0)
    ***(y, (z,))***
    lambda y,z: y - z <= 0
    lambda y,z: y - z
    y <= z
    ***(z, (0,))***
    lambda z: z <= 0
    lambda z: z
    z <= 0
    ***(z, (x, 0))***
    lambda x,z: z - max(x, 0) <= 0
    lambda x,z: z - max(x, 0)
    If(x >= 0, z <= x, z <= 0)
    ***(z, (x, y))***
    lambda x,y,z: z - max(x, y) <= 0
    lambda x,y,z: z - max(x, y)
    If(x >= y, z <= x, z <= y)
    ***(z, (x, y, 0))***
    lambda x,y,z: z - max(x, y, 0) <= 0
    lambda x,y,z: z - max(x, y, 0)
    If(And(x >= y, x >= 0), z <= x, If(And(y >= x, y >= 0), z <= y, z <= 0))
    ***(z, (y, 0))***
    lambda y,z: z - max(y, 0) <= 0
    lambda y,z: z - max(y, 0)
    If(y >= 0, z <= y, z <= 0)


    sage: mp = MPInv.mk_max_ieq((x-10, y-3), (y,5))
    sage: print(mp)
    lambda x,y: max(x - 10, y - 3) - max(y, 5) <= 0
    sage: print(mp.term)
    lambda x,y: max(x - 10, y - 3) - max(y, 5)
    sage: print(mp.ite)
    If(x - 10 >= y - 3, If(y >= 5, x - 10 <= y, x - 10 <= 5),
       If(y >= 5, y - 3 <= y, y - 3 <= 5))

    sage: mp = MPInv.mk_min_ieq((x-10, y-3), (y, 5))
    sage: print(mp)
    lambda x,y: min(x - 10, y - 3) - min(y, 5) <= 0
    sage: print(mp.ite)
    If(x - 10 <= y - 3, If(y <= 5, x - 10 <= y, x - 10 <= 5),
       If(y <= 5, y - 3 <= y, y - 3 <= 5))


    sage: mp = MPInv.mk_max_eq((x-10, y-3), (y,))
    sage: print(mp.term)
    lambda x,y: max(x - 10, y - 3) - y
    sage: print(mp)
    lambda x,y: max(x - 10, y - 3) - y == 0
    sage: print(mp.ite)
    If(x - 10 >= y - 3, x - 10 == y, y - 3 == y)

    sage: mp = MPInv.mk_min_eq((x-10, y-3), (y+12,))
    sage: print(mp.term)
    lambda x,y: min(x - 10, y - 3) - (y + 12)
    sage: print(mp)
    lambda x,y: min(x - 10, y - 3) - (y + 12) == 0
    sage: print(mp.ite)
    If(x - 10 <= y - 3, x - 10 == y + 12, y - 3 == y + 12)

    sage: print(MPInv.mk_max_eq((x-10, y-3), (y+12,)).ite)
    If(x - 10 >= y - 3, x - 10 == y + 12, y - 3 == y + 12)

    sage: print(MPInv.mk_max_ieq((x-10, y-3), (y+12,)).ite)
    If(x - 10 >= y - 3, x - 10 <= y + 12, y - 3 <= y + 12)

    sage: print(MPInv.mk_min_ieq((x-10, y-3), (y+12,)).ite)
    If(x - 10 <= y - 3, x - 10 <= y + 12, y - 3 <= y + 12)

    sage: print(MPInv.mk_min_ieq((x-10, y-3), (y+12,)).ite)
    If(x - 10 <= y - 3, x - 10 <= y + 12, y - 3 <= y + 12)

    sage: print(MPInv.mk_min_ieq((x-10, y-3), (y, 12)).ite)
    If(x - 10 <= y - 3, If(y <= 12, x - 10 <= y, x - 10 <= 12),
       If(y <= 12, y - 3 <= y, y - 3 <= 12))

    sage: print(MPInv.mk_min_eq((x-10, y-3),(y, 12)).ite)
    If(x - 10 <= y - 3, If(y <= 12, x - 10 == y, x - 10 == 12),
       If(y <= 12, y - 3 == y, y - 3 == 12))

    sage: mp = MPInv.mk_max_ieq((0,), (x - 15,))
    sage: print(mp.term)
    lambda x: 0 - (x - 15)
    sage: print(mp)
    lambda x: 0 - (x - 15) <= 0
    sage: print(mp.ite)
    0 <= x - 15

    """

    def __init__(self, lh, rh, is_maxplus=True, is_ieq=True, stat=None):
        if not isinstance(lh, tuple):
            lh = (lh, )
        if not isinstance(rh, tuple):
            rh = (rh, )
        super(MPInv, self).__init__((lh, rh), stat)

        self.lh = lh
        self.rh = rh
        self.is_maxplus = is_maxplus
        self.is_ieq = is_ieq

    def __str__(self, print_stat=False):
        s = "{} {} 0".format(self.term, '<=' if self.is_ieq else '==')
        if print_stat:
            s = "{} {}".format(s, self.stat)
        return s

    def expr(self, use_reals):
        """
        sage: x, y, z = sage.all.var('x y z')
        sage: mp = MPInv.mk_max_ieq((x-10, y-3), (y, 5))
        sage: mp.expr(use_reals=False)
        If(x + -10 >= y + -3, If(y >= 5, x + -10 <= y, x + -10 <= 5),
           If(y >= 5, y + -3 <= y, y + -3 <= 5))

        sage: MPInv.mk_max_ieq((x,), (y,z,0)).expr(use_reals=False)
        If(And(y >= z, y >= 0), x <= y, If(z >= 0, x <= z, x <= 0))
        """

        lh = tuple(Z3.toZ3(x, use_reals, use_mod=False) for x in self.lh)
        rh = tuple(Z3.toZ3(x, use_reals, use_mod=False) for x in self.rh)
        expr = self.mp2df_expr(lh, rh, 0, self.is_maxplus, self.is_ieq)

        if len(rh) >= 3:  # more simplification
            simpl = z3.Tactic('ctx-solver-simplify')
            simpl = z3.TryFor(simpl, settings.SOLVER_TIMEOUT*10)
            try:
                myexpr = simpl(expr)[0][0]
                assert z3.is_expr(myexpr), myexpr
                expr = myexpr
            except z3.Z3Exception:
                pass

        return expr

    @property
    def symbols(self):
        try:
            return self._symbols
        except AttributeError:
            self._symbols = Miscs.getVars(self.lh + self.rh)
            return self._symbols

    @property
    def term(self):
        """
        Return string representing a lambda function
        lambda x, y, ... = max(x, y...) - max(x, y...)
        """

        try:
            return self._term
        except AttributeError:
            myterm = self._term_f(self.lh, self.rh, self.is_maxplus)
            symbols_s = ','.join(map(str, self.symbols))
            self._term = "lambda {}: {}".format(symbols_s, myterm)
            return self._term

    @staticmethod
    def _term_f(lh, rh, is_maxplus):
        """
        sage: x, y, z = sage.all.var('x y z')
        sage: print(MPInv._term_f((x,), (0,), is_maxplus=True))
        x
        sage: print(MPInv._term_f((x,y), (z,7), is_maxplus=True))
        max(x, y) - max(z, 7)
        """
        def f(ls):
            assert ls
            if len(ls) >= 2:
                return '{}({})'.format(
                    'max' if is_maxplus else 'min',
                    ', '.join(map(str, ls)))
            else:
                term = ls[0]
                try:
                    if term.operands():  # x - 3
                        t = '({})'
                    else:
                        t = '{}'
                except AttributeError:  # 3
                    t = '{}'

                return t.format(term)
        lhs = f(lh)
        rhs = f(rh)
        if rhs == '0':
            return lhs
        else:
            return "{} - {}".format(lhs, rhs)

    def test_single_trace(self, trace):
        assert isinstance(trace, Trace), trace
        trace = trace.mydict_str
        bval = self._eval(str(self), trace)

        assert isinstance(bval, bool), bval
        return bval

    def term_upper(self, uv, is_ieq=None):
        """
        return term <= uv
        lh - rh <= uv ~> lh - uv <= rh
        """
        assert len(self.lh) == 1, self.lh
        return self.__class__(self.lh[0] - uv, self.rh, self.is_maxplus,
                              self.is_ieq if is_ieq is None else is_ieq,
                              stat=self.stat)

    def term_lower(self, lv, is_ieq=None):
        """
        return uv <= term
        lv <= lh - rh ~>   rh <= lh - lv
        """
        assert len(self.lh) == 1, self.lh
        return self.__class__(self.rh, self.lh[0] - lv, self.is_maxplus,
                              self.is_ieq if is_ieq is None else is_ieq,
                              stat=self.stat)

    @property
    def ite(self):
        """
        Return if-then-else format
        """
        try:
            return self._ite
        except AttributeError:
            # max(x,y) =>  if(x>=y)...
            # min(x,y) = > if (x<=y)...
            self._ite = self.mp2df(
                self.lh, self.rh, 0, self.is_maxplus, self.is_ieq)
            return self._ite

    @classmethod
    def mp2df(cls, lh, rh, idx, is_maxplus, is_ieq):
        """
        sage: x, y = sage.all.var('x  y')
        sage: MPInv.mp2df((x-10, y-3), (y+12,), 0, is_maxplus=True, is_ieq=True)
        'If(x - 10 >= y - 3, x - 10 <= y + 12, y - 3 <= y + 12)'
        """
        assert isinstance(lh, tuple) and lh

        elem = lh[idx]
        if isinstance(rh, tuple):
            ite = cls.mp2df(rh, elem, 0, is_maxplus, is_ieq)
        else:
            ite = "{} {} {}".format(rh, '<=' if is_ieq else '==', elem)
        rest = lh[idx + 1:]

        if not rest:  # t <= max(x,y,z)
            return ite
        else:
            rest_ite = cls.mp2df(lh, rh, idx + 1, is_maxplus, is_ieq)

            others = lh[:idx] + rest

            conds = ["{} {} {}".format(
                elem, '>=' if is_maxplus else '<=', t) for t in others]
            if len(conds) >= 2:
                cond = 'And({})'.format(', '.join(conds))
            else:
                cond = conds[0]

            return "If({}, {}, {})".format(cond, ite, rest_ite)

    @classmethod
    def mp2df_expr(cls, lh, rh, idx, is_maxplus, is_ieq):
        """
        sage: x, y = z3.Ints('x y')
        sage: MPInv.mp2df_expr((x-z3.IntVal('10'), y-z3.IntVal('3')), \
                               (y+z3.IntVal('12'),), 0, is_maxplus=True, is_ieq=True)
        If(x - 10 >= y - 3, x - 10 <= y + 12, y - 3 <= y + 12)
        """
        assert isinstance(lh, tuple) and lh

        elem = lh[idx]
        if isinstance(rh, tuple):
            ite = cls.mp2df_expr(rh, elem, 0, is_maxplus, is_ieq)
        else:
            if is_ieq:
                ite = rh <= elem
            else:
                ite = rh >= elem

            # ite = "{} {} {}".format(rh, '<=' if is_ieq else '==', elem)
        rest = lh[idx + 1:]

        if not rest:  # t <= max(x,y,z)
            return ite
        else:
            rest_ite = cls.mp2df_expr(lh, rh, idx + 1, is_maxplus, is_ieq)

            others = lh[:idx] + rest

            # conds = ["{} {} {}".format(
            #     elem, '>=' if is_maxplus else '<=', t) for t in others]

            conds = [elem >= t if is_maxplus else elem <= t for t in others]
            if len(conds) >= 2:
                cond = z3.And(*conds)
            else:
                cond = conds[0]

            return z3.If(cond, ite, rest_ite)

    def myeval(self, trace):
        return self._eval(self.term, trace)

    @classmethod
    def _eval(cls, lambda_str, trace):
        """
        Examples:
        sage: assert MPInv._eval('lambda x,y: x+y', {'x': 2,'y':3,'d':7}) == 5
        sage: assert MPInv._eval('lambda x,y: x+y == 5', {'x': 2,'y':3,'d':7})
        sage: assert MPInv._eval('lambda x,y: x+y == 10 or x + y == 5', {'x': 2,'y':3,'d':7})
        sage: assert MPInv._eval('lambda x,y: max(x - 13,-3)', {'x': 11,'y':100}) == -2
        sage: assert MPInv._eval('lambda x,y: max(x - 13,-3) >= y', {'x': 11,'y':-2}) == True
        sage: assert MPInv._eval('lambda x,y: max(x - 13,-3) <= y', {'x': 11,'y':100}) == True
        sage: assert MPInv._eval('lambda x,y: x+y == 6', {'x': 2,'y':3,'d':7}) == False
        sage: assert MPInv._eval('lambda x,y: x+y == 1 or x + y == 2', {'x': 2,'y':3,'d':7}) == False
        """
        assert isinstance(lambda_str, str) and 'lambda' in lambda_str
        assert trace, trace

        f = sage.all.sage_eval(lambda_str)
        symbols = f.func_code.co_varnames
        # if trace has more keys than variables in lambda str then remove them
        trace = dict([(s, trace[s]) for s in symbols])
        rs = f(**trace)
        return rs

    @classmethod
    def mk_from_symbols(cls, symbols):
        return [cls(lh, (rh,)) for lh, rh in cls.get_terms(symbols)]

    @classmethod
    def get_terms(cls, terms):
        """
        Generate (weak) mp terms of the form
        xi <= max(c1+x1, ... ,cn+xn, c0) and
        max(c1+x1, ... ,cn+xn, c0) <= xj
        where ci are in {0,-oo} for max plus

        sage: var('x y z t s w')
        (x, y, z, t, s, w)

        sage: ts = MPInv.get_terms([x,y])
        sage: assert len(ts) == 5
        sage: ts
        [(x, (0,)), (x, (y, 0)), (x, (y,)), (y, (0,)), (y, (x, 0))]

        sage: ts = MPInv.get_terms([x,y,z])
        sage: assert len(ts) == 18
        sage: ts
        [(x, (0,)),
        (x, (y, 0)),
        (x, (y, z)),
        (x, (y, z, 0)),
        (x, (y,)),
        (x, (z, 0)),
        (x, (z,)),
        (y, (0,)),
        (y, (x, 0)),
        (y, (x, z)),
        (y, (x, z, 0)),
        (y, (z, 0)),
        (y, (z,)),
        (z, (0,)),
        (z, (x, 0)),
        (z, (x, y)),
        (z, (x, y, 0)),
        (z, (y, 0))]

        sage: ts = MPInv.get_terms([x,y,z,w])
        sage: assert len(ts) == 54
        sage: ts
        [(w, (0,)),
        (w, (x, 0)),
        (w, (x, y)),
        (w, (x, y, 0)),
        (w, (x, y, z)),
        (w, (x, y, z, 0)),
        (w, (x, z)),
        (w, (x, z, 0)),
        (w, (x,)),
        (w, (y, 0)),
        (w, (y, z)),
        (w, (y, z, 0)),
        (w, (y,)),
        (w, (z, 0)),
        (w, (z,)),
        (x, (0,)),
        (x, (w, 0)),
        (x, (w, y)),
        (x, (w, y, 0)),
        (x, (w, y, z)),
        (x, (w, y, z, 0)),
        (x, (w, z)),
        (x, (w, z, 0)),
        (x, (y, 0)),
        (x, (y, z)),
        (x, (y, z, 0)),
        (x, (y,)),
        (x, (z, 0)),
        (x, (z,)),
        (y, (0,)),
        (y, (w, 0)),
        (y, (w, x)),
        (y, (w, x, 0)),
        (y, (w, x, z)),
        (y, (w, x, z, 0)),
        (y, (w, z)),
        (y, (w, z, 0)),
        (y, (x, 0)),
        (y, (x, z)),
        (y, (x, z, 0)),
        (y, (z, 0)),
        (y, (z,)),
        (z, (0,)),
        (z, (w, 0)),
        (z, (w, x)),
        (z, (w, x, 0)),
        (z, (w, x, y)),
        (z, (w, x, y, 0)),
        (z, (w, y)),
        (z, (w, y, 0)),
        (z, (x, 0)),
        (z, (x, y)),
        (z, (x, y, 0)),
        (z, (y, 0))]

        sage: assert len(MPInv.get_terms([x,y,z,t,s])) == 145

        """
        assert terms, terms

        terms = sorted(terms, key=lambda x: str(x))
        results = set((t, (0,)) for t in terms)
        for i, term in enumerate(terms):
            terms_ = terms[:i] + terms[i+1:]
            powerset = itertools.chain.from_iterable(
                itertools.combinations(terms_, r)
                for r in range(len(terms_)+1))
            powerset = [ps for ps in powerset if ps]
            for pset in powerset:
                results.add((term, tuple(list(pset) + [0])))
                # ignore [y], x if [x],y exists
                if not(len(pset) == 1 and (pset[0], (term,)) in results):
                    results.add((term, pset))

        return sorted(results, key=lambda x: str(x))
        return results

    @classmethod
    def mk_max_ieq(cls, lh, rh):
        return cls(lh, rh, is_maxplus=True, is_ieq=True)

    @classmethod
    def mk_max_eq(cls, lh, rh):
        return cls(lh, rh, is_maxplus=True, is_ieq=False)

    @classmethod
    def mk_min_ieq(cls, lh, rh):
        return cls(lh, rh, is_maxplus=False, is_ieq=True)

    @classmethod
    def mk_min_eq(cls, lh, rh):
        return cls(lh, rh, is_maxplus=False, is_ieq=False)

    @classmethod
    def mk_max_ieqs(cls, terms):
        return [cls.mk_max_ieq(lh, rh) for lh, rh in terms]

    @classmethod
    def infer(cls, terms, traces, is_maxplus=True, is_ieq=True):
        """
        sage: x, y, z = sage.all.var('x y z')
        sage: tcs = [{'x': 2, 'y': -8, 'z': -7}, \
            {'x': -1, 'y': -15, 'z': 88}, {'x': 15, 'y': 5, 'z': 0}]
        sage: mps = MPInv.infer([x, y], tcs)
        sage: assert len(mps) == 10
        sage: print('\n'.join(m.ite for m in mps))
        0 <= x + 1
        x - 15 <= 0
        If(y >= 0, y <= x + 1, 0 <= x + 1)
        If(y >= 0, x - 10 <= y, x - 10 <= 0)
        y <= x - 10
        x - 14 <= y
        0 <= y + 15
        y - 5 <= 0
        If(x >= 0, x <= y + 15, 0 <= y + 15)
        If(x >= 0, y + 10 <= x, y + 10 <= 0)

        sage: mps = MPInv.infer([x], tcs)
        sage: print('\n'.join(m.ite for m in mps))
        0 <= x + 1
        x - 15 <= 0

        sage: mps = MPInv.infer([x,y,z], tcs)
        sage: assert len(mps) == 36
        sage: mps = sorted(mps, key=lambda m: len(m.ite))

        # sage: print('\n'.join('{}\n{}'.format(m, m.ite) for m in mps))

        #sage: [MPInv.my_ite_test(m.expr(use_reals=False)) for m in mps]

        lambda x: 0 - (x + 1) <= 0
        0 <= x + 1
        lambda y: (y - 5) - 0 <= 0
        y - 5 <= 0
        lambda y,z: (y - 5) - z <= 0
        y - 5 <= z
        lambda z: 0 - (z + 7) <= 0
        0 <= z + 7
        lambda x: (x - 15) - 0 <= 0
        x - 15 <= 0
        lambda x,y: y - (x - 10) <= 0
        y <= x - 10
        lambda x,y: (x - 14) - y <= 0
        x - 14 <= y
        lambda x,z: z - (x + 89) <= 0
        z <= x + 89
        lambda x,z: (x - 15) - z <= 0
        x - 15 <= z
        lambda y: 0 - (y + 15) <= 0
        0 <= y + 15
        lambda z: (z - 88) - 0 <= 0
        z - 88 <= 0
        lambda y,z: z - (y + 103) <= 0
        z <= y + 103
        lambda x,y: max(y, 0) - (x + 1) <= 0
        If(y >= 0, y <= x + 1, 0 <= x + 1)
        lambda y,z: (y - 5) - max(z, 0) <= 0
        If(z >= 0, y - 5 <= z, y - 5 <= 0)
        lambda y,z: max(y, 0) - (z + 7) <= 0
        If(y >= 0, y <= z + 7, 0 <= z + 7)
        lambda x,y: (x - 10) - max(y, 0) <= 0
        If(y >= 0, x - 10 <= y, x - 10 <= 0)
        lambda x,y,z: max(y, z) - (x + 89) <= 0
        If(y >= z, y <= x + 89, z <= x + 89)
        lambda x,y,z: (x - 10) - max(y, z) <= 0
        If(y >= z, x - 10 <= y, x - 10 <= z)
        lambda x,z: max(z, 0) - (x + 89) <= 0
        If(z >= 0, z <= x + 89, 0 <= x + 89)
        lambda x,z: (x - 15) - max(z, 0) <= 0
        If(z >= 0, x - 15 <= z, x - 15 <= 0)
        lambda x,y: max(x, 0) - (y + 15) <= 0
        If(x >= 0, x <= y + 15, 0 <= y + 15)
        lambda x,y: (y + 10) - max(x, 0) <= 0
        If(x >= 0, y + 10 <= x, y + 10 <= 0)
        lambda x,y,z: (y + 10) - max(x, z) <= 0
        If(x >= z, y + 10 <= x, y + 10 <= z)
        lambda x,z: max(x, 0) - (z + 15) <= 0
        If(x >= 0, x <= z + 15, 0 <= z + 15)
        lambda x,z: (z - 88) - max(x, 0) <= 0
        If(x >= 0, z - 88 <= x, z - 88 <= 0)
        lambda x,y,z: max(x, y) - (z + 15) <= 0
        If(x >= y, x <= z + 15, y <= z + 15)
        lambda x,y,z: (z - 89) - max(x, y) <= 0
        If(x >= y, z - 89 <= x, z - 89 <= y)
        lambda y,z: (z - 88) - max(y, 0) <= 0
        If(y >= 0, z - 88 <= y, z - 88 <= 0)
        lambda x,y,z: max(x, z) - (y + 103) <= 0
        If(x >= z, x <= y + 103, z <= y + 103)
        lambda y,z: max(z, 0) - (y + 103) <= 0
        If(z >= 0, z <= y + 103, 0 <= y + 103)
        lambda x,y,z: max(y, z, 0) - (x + 89) <= 0
        If(And(y >= z, y >= 0), y <= x + 89,
           If(And(z >= y, z >= 0), z <= x + 89, 0 <= x + 89))
        lambda x,y,z: (x - 10) - max(y, z, 0) <= 0
        If(And(y >= z, y >= 0), x - 10 <= y,
           If(And(z >= y, z >= 0), x - 10 <= z, x - 10 <= 0))
        lambda x,y,z: (y + 10) - max(x, z, 0) <= 0
        If(And(x >= z, x >= 0), y + 10 <= x,
           If(And(z >= x, z >= 0), y + 10 <= z, y + 10 <= 0))
        lambda x,y,z: max(x, y, 0) - (z + 15) <= 0
        If(And(x >= y, x >= 0), x <= z + 15,
           If(And(y >= x, y >= 0), y <= z + 15, 0 <= z + 15))
        lambda x,y,z: (z - 88) - max(x, y, 0) <= 0
        If(And(x >= y, x >= 0), z - 88 <= x,
           If(And(y >= x, y >= 0), z - 88 <= y, z - 88 <= 0))
        lambda x,y,z: max(x, z, 0) - (y + 103) <= 0
        If(And(x >= z, x >= 0), x <= y + 103,
           If(And(z >= x, z >= 0), z <= y + 103, 0 <= y + 103))

        """

        def mk_lower(lh, rh, mymax):
            """
            lh - rh <= mymax ~> lh - mymax <= rh
            """
            return (lh - mymax, ), rh

        def mk_upper(lh, rh, mymin):
            """
            mymin <= lh - rh ~>   rh <= lh - mymin
            """
            return rh, (lh - mymin, )

        results = []
        for lh, rh in cls.get_terms(terms):
            mp = cls((lh,), rh, is_maxplus, is_ieq)
            myevals = [mp.myeval(trace) for trace in traces]
            mymin = min(myevals)
            mymax = max(myevals)

            if mymin == mymax:
                mp_eq = mp.term_upper(mymax, is_ieq=True)
                results.append(mp_eq)
            else:
                mp_lower = mp.term_lower(mymin)
                mp_upper = mp.term_upper(mymax)
                results.extend([mp_lower, mp_upper])
        return results


class PrePostInv(Inv):
    """
    Set of Preconds  -> PostInv
    """

    def __init__(self, preconds, postcond, stat=None):
        assert isinstance(preconds, Invs), preconds
        assert isinstance(postcond, EqtInv), postcond

        super(PrePostInv, self).__init__(
            (frozenset(preconds), postcond), stat)

        self.preconds = preconds
        self.postcond = postcond

    def expr(self, use_reals):
        """
        And(preconds) -> postcond
        """
        pre = z3.And([c.expr(use_reals) for c in self.preconds])
        post = c.expr(use_reals)
        return z3.Implies(pre, post)

    def __str__(self, print_stat=False):
        return "{} => {} {}".format(
            self.preconds.__str__(delim=" & "), self.postcond, self.stat)


class Invs(set):
    def __init__(self, invs=set()):
        assert all(isinstance(inv, Inv) for inv in invs), invs
        super(Invs, self).__init__(invs)

    def __str__(self, print_stat=False, delim='\n'):
        invs = sorted(self, reverse=True,
                      key=lambda inv: isinstance(inv, EqtInv))
        return delim.join(inv.__str__(print_stat) for inv in invs)

    @property
    def n_eqs(self):
        return len([inv for inv in self if isinstance(inv, EqtInv)])

    def __contains__(self, inv):
        assert isinstance(inv, Inv), inv
        return super(Invs, self).__contains__(inv)

    def add(self, inv):
        assert isinstance(inv, Inv), inv
        notIn = False
        if inv not in self:
            notIn = True
            super(Invs, self).add(inv)
        return notIn

    def test(self, traces):
        assert isinstance(traces, Traces)
        assert(self), self

        def f(tasks):
            return [(inv, inv.test(traces)) for inv in tasks]

        tasks = list(self)
        wrs = Miscs.run_mp_simple("test", tasks, f, doMP=settings.doMP)
        invs = self.__class__([inv for inv, passed in wrs if passed])
        return invs

    def uniqify(self, use_reals):
        assert isinstance(use_reals, bool), use_reals

        eqts, eqtsLargeCoefs, ieqs, mps, others = [], [], [], [], []
        for inv in self:
            if isinstance(inv, EqtInv):
                if len(Miscs.getCoefs(inv.inv)) > 10:
                    eqtsLargeCoefs.append(inv)
                else:
                    eqts.append(inv)
            elif isinstance(inv, IeqInv):
                ieqs.append(inv)
            elif isinstance(inv, MPInv):
                mps.append(inv)
            else:
                others.append(inv)

        rests = eqts + ieqs + others
        tasks = [mps, rests]

        def f(tasks):
            return [self.uniq(invs, use_reals) for invs in tasks]
        wrs = Miscs.run_mp_simple("uniqify", tasks, f, doMP=settings.doMP)

        rs_all = []
        for invs in wrs:
            rs_all.extend(invs)

        rs = self.uniq(rs_all, use_reals)
        return Invs(rs + eqtsLargeCoefs)

    @classmethod
    def uniq(cls, invs, use_reals):
        mlog.debug("uniq {} invs".format(len(invs)))

        def _imply(i, xclude):
            me = invs[i].expr(use_reals)
            others = [invs[j].expr(use_reals) for j in xclude]
            return Z3._imply(others, me)

        rs = set(range(len(invs)))
        for i in range(len(invs)):
            if i not in rs:
                continue
            xclude = rs - {i}
            if xclude and _imply(i, xclude):
                rs = xclude
        rs = [invs[i] for i in sorted(rs)]
        return rs


class DInvs(dict):
    """
    {loc -> Invs}  , Invs is a set
    """

    def __setitem__(self, loc, invs):
        assert isinstance(loc, str) and loc, loc
        assert isinstance(invs, Invs), invs

        super(DInvs, self).__setitem__(loc, invs)

    @property
    def invs(self):
        return (inv for invs in self.itervalues() for inv in invs)

    @property
    def siz(self): return sum(map(len, self.itervalues()))

    @property
    def n_eqs(self): return sum(invs.n_eqs for invs in self.itervalues())

    def __str__(self, print_stat=False):
        ss = []

        for loc in sorted(self):
            eqts, ieqs, mps, others = [], [], [], []
            for inv in self[loc]:
                if isinstance(inv, EqtInv):
                    eqts.append(inv)
                elif isinstance(inv, IeqInv):
                    ieqs.append(inv)
                elif isinstance(inv, MPInv):
                    mps.append(inv)
                else:
                    assert isinstance(inv, (FalseInv, PrePostInv)), inv

                    others.append(inv)

            ss.append("{} ({} invs):".format(loc, len(self[loc])))
            invs = sorted(eqts, reverse=True) + \
                sorted(ieqs, reverse=True) + \
                sorted(mps, reverse=True) + \
                sorted(others, reverse=True)
            ss.extend("{}. {}".format(i+1, inv.__str__(print_stat))
                      for i, inv in enumerate(invs))

        return '\n'.join(ss)

    def add(self, loc, inv):
        assert isinstance(loc, str) and loc, loc
        assert isinstance(inv, Inv), inv

        if loc not in self:
            self[loc] = Invs()
        return self[loc].add(inv)

    def merge(self, dinvs):
        assert isinstance(dinvs, DInvs), dinvs
        for loc in dinvs:
            for inv in dinvs[loc]:
                if not inv.is_disproved:
                    self.add(loc, inv)

    def remove_disproved(self):
        dinvs = self.__class__()
        for loc in self:
            for inv in self[loc]:
                if not inv.is_disproved:
                    dinvs.add(loc, inv)
        return dinvs

    def test(self, dtraces):
        assert isinstance(dtraces, DTraces)
        assert(self.siz), self

        st = time()
        tasks = [loc for loc in self if self[loc]]

        def f(tasks):
            return [(loc, self[loc].test(dtraces[loc])) for loc in tasks]

        wrs = Miscs.run_mp_simple("test_dinvs", tasks, f, doMP=settings.doMP)
        dinvs = DInvs([(loc, invs) for loc, invs in wrs if invs])
        show_removed(self.siz, dinvs.siz, st)
        return dinvs

    def update(self, dinvs):
        assert isinstance(dinvs, DInvs), dinvs
        deltas = self.__class__()
        for loc in self:
            if loc not in dinvs:
                dinvs[loc] = self[loc]
                deltas[loc] = self[loc]
            elif dinvs[loc] != self[loc]:
                new_invs = Invs()
                for inv in self[loc]:
                    if inv not in dinvs[loc]:
                        new_invs.add(inv)
                    else:
                        invs_l = list(dinvs[loc])
                        old_inv = invs_l[invs_l.index(inv)]
                        if inv.stat != old_inv.stat:
                            inv.stat = old_inv.stat
                dinvs[loc] = self[loc]
                deltas[loc] = new_invs

        return deltas

    def uniqify(self, use_reals):
        assert isinstance(use_reals, bool), use_reals
        assert(self.siz), self

        st = time()
        tasks = list(self.keys())

        def f(tasks):
            return [(loc, self[loc].uniqify(use_reals)) for loc in tasks]
        wrs = Miscs.run_mp_simple("uniqify", tasks, f, doMP=settings.doMP)

        dinvs = self.__class__((loc, invs) for loc, invs in wrs if invs)
        show_removed(self.siz, dinvs.siz, st)
        return dinvs

    @classmethod
    def mk_false_invs(cls, locs):
        dinvs = cls()
        for loc in locs:
            dinvs.add(loc, FalseInv.mk())
        return dinvs

    @classmethod
    def mk(cls, loc, invs):
        assert isinstance(invs, Invs), invs
        newInvs = cls()
        newInvs[loc] = invs
        return newInvs


def show_removed(orig_siz, new_siz, st):
    assert orig_siz >= new_siz, (orig_siz, new_siz)
    n_removed = orig_siz - new_siz
    if n_removed:
        mlog.debug("removed {} invs ({}s, orig {}, new {})"
                   .format(n_removed, time() - st, orig_siz, new_siz))

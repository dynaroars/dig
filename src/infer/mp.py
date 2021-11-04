import pdb
import itertools
import typing
import functools
import sympy
import z3

import helpers.vcommon as CM
from helpers.miscs import Miscs
from helpers.z3utils import Z3
import settings

import data.traces
import infer.inv
import infer.infer

DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.LOGGER_LEVEL)


class Term(typing.NamedTuple):
    a: tuple
    b: tuple
    is_max: bool

    @property
    def symbols(self) -> typing.Set[str]:
        return set(map(str, Miscs.get_vars(self.a + self.b)))

    def __str__(self, use_lambda: bool = False) -> str:
        """
        Return string representing a lambda function
        lambda x, y, ... = max(x, y...) - max(x, y...)
        """
        s = self._to_str(self.a, self.b, self.is_max)
        if use_lambda:
            s = f"lambda {','.join(self.symbols)}: {s}"
        return s

    @classmethod
    def mk(cls, a, b, is_max: bool = True):
        if not isinstance(a, tuple):
            a = (a,)
        if not isinstance(b, tuple):
            b = (b,)
        return cls(a, b, is_max)

    def mk_le(self, uv):
        """
        return term <= uv
        a - b <= uv ~> a - uv <= b
        b - a <= uv ~> b <= a + uv
        """

        if len(self.a) == 1:
            a = self.a[0] - uv
            b = self.b

        else:
            assert len(self.b) == 1, self.b
            a = self.a
            b = self.b[0] + uv

        return self.mk(a, b, self.is_max)

    def eval_traces(self, traces: data.traces.Traces, pred=None) -> bool:
        if pred is None:
            return [
                self._eval(self.__str__(use_lambda=True), t.mydict_str) for t in traces
            ]
        else:
            return any(
                pred(self._eval(self.__str__(use_lambda=True), t.mydict_str))
                for t in traces
            )

    @classmethod
    def get_terms(cls, terms):
        """
        Generate (weak) mp terms of the form
        xi <= max(c1+x1, ... ,cn+xn, c0) and
        max(c1+x1, ... ,cn+xn, c0) <= xj
        where ci are in {0,-oo} for max plus

        sage: from data.mps import Term

        sage: var('x y z t s w')
        (x, y, z, t, s, w)

        sage: ts = MTerm.get_terms([x,y])
        sage: ts
        [(x, (0,)), (x, (y, 0)), (x, (y,)), (y, (0,)), (y, (x, 0))]
        sage: assert len(ts) == 5

        sage: ts = MTerm.get_terms([x,y], ignore_oct=True)
        sage: ts
        [(x, (y, 0)), (y, (x, 0))]


        sage: ts = MTerm.get_terms([x,y,z])
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

        sage: ts = MTerm.get_terms([x,y,z], ignore_oct=True)
        sage: ts
        [(x, (y, 0)),
        (x, (y, z)),
        (x, (y, z, 0)),
        (x, (z, 0)),
        (y, (x, 0)),
        (y, (x, z)),
        (y, (x, z, 0)),
        (y, (z, 0)),
        (z, (x, 0)),
        (z, (x, y)),
        (z, (x, y, 0)),
        (z, (y, 0))]


        sage: ts = MTerm.get_terms([x,y,z,w])
        sage: assert len(ts) == 54

        sage: assert len(MTerm.get_terms([x,y,z,t,s])) == 145

        """
        assert terms, terms

        terms = sorted(terms, key=lambda x: str(x))
        results = set((t, (0,)) for t in terms)
        for i, term in enumerate(terms):
            terms_ = terms[:i] + terms[i + 1:]
            powerset = itertools.chain.from_iterable(
                itertools.combinations(terms_, r) for r in range(len(terms_) + 1)
            )
            powerset = [ps for ps in powerset if ps]
            for pset in powerset:
                results.add((term, tuple(list(pset) + [0])))
                # ignore [y], x if [x],y exists
                if not (len(pset) == 1 and (pset[0], (term,)) in results):
                    results.add((term, pset))

        return sorted(results, key=lambda x: str(x))

    @staticmethod
    @functools.cache
    def _to_str(a, b, is_max: bool) -> str:
        """
        # sage: x, y, z = sage.all.var('x y z')
        # sage: print(MMPInv._to_str((x,), (0,), is_max=True))
        # x
        # sage: print(MMPInv._to_str((x,y), (z,7), is_max=True))
        # max(x, y) - max(z, 7)
        """

        def f(ls):
            assert ls
            if len(ls) >= 2:
                return f"{'max' if is_max else 'min'}({', '.join(map(str, ls))})"
            else:
                term = ls[0]
                try:
                    if term.operands():  # x - 3
                        t = "({})"
                    else:
                        t = "{}"
                except AttributeError:  # 3
                    t = "{}"

                return t.format(term)

        a_ = f(a)
        b_ = f(b)
        if b_ == "0":
            return a_
        else:
            return f"{a_} - {b_}"

    @staticmethod
    def _eval(lambda_str: str, trace: data.traces.Trace) -> bool:
        """
        Examples:
        # sage: assert MMPInv._eval('lambda x,y: x+y', {'x': 2,'y':3,'d':7}) == 5
        # sage: assert MMPInv._eval('lambda x,y: x+y == 5', {'x': 2,'y':3,'d':7})
        # sage: assert MMPInv._eval('lambda x,y: x+y == 10 or x + y == 5', {'x': 2,'y':3,'d':7})
        # sage: assert MMPInv._eval('lambda x,y: max(x - 13,-3)', {'x': 11,'y':100}) == -2
        # sage: assert MMPInv._eval('lambda x,y: max(x - 13,-3) >= y', {'x': 11,'y':-2}) == True
        # sage: assert MMPInv._eval('lambda x,y: max(x - 13,-3) <= y', {'x': 11,'y':100}) == True
        # sage: assert MMPInv._eval('lambda x,y: x+y == 6', {'x': 2,'y':3,'d':7}) == False
        # sage: assert MMPInv._eval('lambda x,y: x+y == 1 or x + y == 2', {'x': 2,'y':3,'d':7}) == False
        """
        assert isinstance(lambda_str, str) and "lambda" in lambda_str
        assert isinstance(trace, dict), trace

        f = eval(lambda_str)
        symbols = f.__code__.co_varnames
        # if trace has more keys than variables in lambda str then remove them
        trace = dict([(s, trace[s]) for s in symbols])
        rs = f(**trace)
        return rs


class MMP(infer.inv.Inv):
    def __init__(self, term, is_ieq=True, stat=None):
        """
        term = max(x, y) - z

        is_ieq is None -> treat like a term, e.g.,  If(x>=y,x-z,y-z)
        is_ieq is True -> treat like  <= expr, e.g., If(x>=y,x<=z,y<=z)
        if_ieq is False -> treat like == expr, e.g., If(x>=y,x>=z,y>=z)
        """
        assert isinstance(term, Term), term
        assert is_ieq is None or isinstance(is_ieq, bool), is_ieq

        hash_contents = (term.a, term.b, term.is_max, is_ieq)
        super().__init__(hash_contents, stat)
        self.term = term
        self.is_ieq = is_ieq

    def lambdastr(self, use_lambda=False):
        s = self.term.__str__(use_lambda)
        if self.is_ieq is not None:
            s += f" {'<=' if self.is_ieq is True else '=='} 0"
        return s

    @property
    def mystr(self):
        return self.lambdastr(use_lambda=False)

    @property
    def is_eqt(self):
        return self.is_ieq is False

    @property
    def expr(self) -> z3.ExprRef:
        """
        # sage: x, y, z = sage.all.var('x y z')
        # sage: mp = MMPInv.mk_max_ieq((x-10, y-3), (y, 5))
        # sage: mp.expr(use_reals=False)
        # If(x + -10 >= y + -3, If(y >= 5, x + -10 <= y, x + -10 <= 5),
        #    If(y >= 5, y + -3 <= y, y + -3 <= 5))

        # sage: MMPInv.mk_max_ieq((x,), (y,z,0)).expr(use_reals=False)
        # If(And(y >= z, y >= 0), x <= y, If(z >= 0, x <= z, x <= 0))
        """

        a = tuple(Z3.parse(str(x)) for x in self.term.a)
        b = tuple(Z3.parse(str(x)) for x in self.term.b)

        expr = self.mp2df_expr(a, b, 0, self.term.is_max, self.is_ieq)

        return expr

    def test_single_trace(self, trace: data.traces.Traces) -> bool:
        assert isinstance(trace, data.traces.Trace), trace

        trace = trace.mydict_str
        bval = Term._eval(self.lambdastr(use_lambda=True), trace)
        assert isinstance(bval, (sympy.logic.boolalg.BooleanTrue,
                          sympy.logic.boolalg.BooleanFalse)), bval
        return bool(bval)

    @classmethod
    def mp2df_expr(cls, a, b, idx, is_max, is_ieq):
        """
        # sage: x, y = z3.Ints('x y')
        # sage: MMPInv.mp2df_expr((x-z3.IntVal('10'), y-z3.IntVal('3')), \
        #                        (y+z3.IntVal('12'),), 0, is_max=True, is_ieq=True)
        # If(x - 10 >= y - 3, x - 10 <= y + 12, y - 3 <= y + 12)
        """
        assert isinstance(a, tuple) and a

        elem = a[idx]
        if isinstance(b, tuple):
            ite = cls.mp2df_expr(b, elem, 0, is_max, is_ieq)
        else:
            if is_ieq is None:
                ite = b - elem
            elif is_ieq is True:
                ite = b <= elem
            else:
                ite = b == elem

            # ite = "{} {} {}".format(b, '<=' if is_ieq else '==', elem)
        rest = a[idx + 1:]

        if not rest:  # t <= max(x,y,z)
            return ite
        else:
            rest_ite = cls.mp2df_expr(a, b, idx + 1, is_max, is_ieq)
            others = a[:idx] + rest
            conds = [elem >= t if is_max else elem <= t for t in others]
            if len(conds) >= 2:
                cond = z3.And(*conds)
            else:
                cond = conds[0]

            return z3.If(cond, ite, rest_ite)

    @classmethod
    def simplify(cls, mps):
        """
        if have both ...  , then create ==
        """
        assert isinstance(mps, list), mps
        assert all(isinstance(mp, cls) for mp in mps)

        cached = {}
        for mp in mps:
            key = frozenset(
                [mp.term.a, mp.term.b, (mp.term.is_max, mp.is_ieq)])

            if key not in cached:
                cached[key] = mp
            else:
                assert cached[key].is_ieq is not False, cached[key]
                cached[key] = cls(mp.term, is_ieq=False, stat=None)

        return list(cached.values())


class Infer(infer.infer._Opt):
    """
    Min-max plus invariants
    """
    IUPPER = settings.IUPPER_MMP

    def __init__(self, symstates, prog):
        super().__init__(symstates, prog)

    @staticmethod
    def to_expr(term):
        return MMP(term, is_ieq=None).expr

    @staticmethod
    def inv_cls(term_ub):
        return MMP(term_ub)

    @classmethod
    def my_get_terms(cls, symbols):
        terms = Term.get_terms(symbols)
        terms = [(a, b) for a, b in terms if len(b) >= 2]  # ignore oct invs

        def _get_terms(terms, is_max):
            terms_ = [(b, a) for a, b in terms]
            return [Term.mk(a, b, is_max) for a, b in terms + terms_]

        terms_max = _get_terms(terms, is_max=True)
        terms_min = _get_terms(terms, is_max=False)
        return terms_min + terms_max

    @staticmethod
    def get_excludes(terms, inps):
        assert isinstance(terms, list)
        assert all(isinstance(t, Term) for t in terms), terms
        assert isinstance(inps, set), inps

        def is_pure(xs):
            # if it's small, then we won't be too strict and allow it
            return (
                len(xs) <= 2
                or all(x in inps for x in xs)
                or all(x not in inps for x in xs)
            )

        excludes = set()
        for term in terms:
            a_symbs = set(map(str, Miscs.get_vars(term.a)))
            b_symbs = set(map(str, Miscs.get_vars(term.b)))
            # print(term, a_symbs, b_symbs)

            if not is_pure(a_symbs) or not is_pure(b_symbs):
                excludes.add(term)
                # print('excluding, not pure', term)
                continue

            inp_in_a = any(s in inps for s in a_symbs)
            inp_in_b = any(s in inps for s in b_symbs)

            # exclude if (inp in both a and b) or inp not in a or b
            if (inp_in_a and inp_in_b) or (not inp_in_a and not inp_in_b):
                excludes.add(term)
                continue

            t_symbs = set.union(a_symbs, b_symbs)

            if len(t_symbs) <= 1:  # finding bound of single input val,
                continue

            if inps.issuperset(t_symbs) or all(s not in inps for s in t_symbs):
                excludes.add(term)

        return excludes


if __name__ == "__main__":
    import doctest
    doctest.testmod()

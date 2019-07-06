import itertools
import pdb

import sage.all
from sage.all import cached_function

import helpers.vcommon as CM
from helpers.miscs import Miscs
import settings

from data.poly.base import Poly

DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


class MP(Poly):
    def __init__(self, a, b, is_max=True):
        if not isinstance(a, tuple):
            a = (a, )
        if not isinstance(b, tuple):
            b = (b, )

        super(MP, self).__init__((a, b, is_max))
        self.a = a
        self.b = b
        self.is_max = is_max

    @property
    def symbols(self):
        try:
            return self._symbols
        except AttributeError:
            self._symbols = set(map(str, Miscs.getVars(self.a + self.b)))
            return self._symbols

    def __str__(self):
        """
        Return string representing a lambda function
        lambda x, y, ... = max(x, y...) - max(x, y...)
        """

        try:
            return self._str
        except AttributeError:
            s1 = ','.join(self.symbols)
            s2 = self._to_str(self.a, self.b, self.is_max)
            self._str = "lambda {}: {}".format(s1, s2)
            return self._str

    def mk_lt(self, uv):
        """
        return term <= uv
        a - b <= uv ~> a - uv <= b
        b - a <= uv ~> b <= a + uv
        """

        if len(self.a) == 1:
            a = self.a[0] - uv
            b = self.b

        else:
            assert len(self.b) == 1
            a = self.a
            b = self.b[0] + uv

        return self.__class__(a, b, is_max=self.is_max)

    def eval_traces(self, traces):
        return [_eval(str(self), t.mydict_str) for t in traces]

    @classmethod
    def get_terms(cls, terms, ignore_oct=False):
        """
        Generate (weak) mp terms of the form
        xi <= max(c1+x1, ... ,cn+xn, c0) and
        max(c1+x1, ... ,cn+xn, c0) <= xj
        where ci are in {0,-oo} for max plus

        sage: from data.mps import MPTerm

        sage: var('x y z t s w')
        (x, y, z, t, s, w)

        sage: ts = MPTerm.get_terms([x,y])
        sage: ts
        [(x, (0,)), (x, (y, 0)), (x, (y,)), (y, (0,)), (y, (x, 0))]
        sage: assert len(ts) == 5

        sage: ts = MPTerm.get_terms([x,y], ignore_oct=True)
        sage: ts
        [(x, (y, 0)), (y, (x, 0))]


        sage: ts = MPTerm.get_terms([x,y,z])
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

        sage: ts = MPTerm.get_terms([x,y,z], ignore_oct=True)
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


        sage: ts = MPTerm.get_terms([x,y,z,w])
        sage: assert len(ts) == 54

        sage: assert len(MPTerm.get_terms([x,y,z,t,s])) == 145

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

    @staticmethod
    def _to_str(a, b, is_max):
        """
        # sage: x, y, z = sage.all.var('x y z')
        # sage: print(MPInv._to_str((x,), (0,), is_max=True))
        # x
        # sage: print(MPInv._to_str((x,y), (z,7), is_max=True))
        # max(x, y) - max(z, 7)
        """
        def f(ls):
            assert ls
            if len(ls) >= 2:
                return '{}({})'.format(
                    'max' if is_max else 'min',
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
        a_ = f(a)
        b_ = f(b)
        if b_ == '0':
            return a_
        else:
            return "{} - {}".format(a_, b_)


def _eval(lambda_str, trace):
    """
    Examples:
    # sage: assert MPInv._eval('lambda x,y: x+y', {'x': 2,'y':3,'d':7}) == 5
    # sage: assert MPInv._eval('lambda x,y: x+y == 5', {'x': 2,'y':3,'d':7})
    # sage: assert MPInv._eval('lambda x,y: x+y == 10 or x + y == 5', {'x': 2,'y':3,'d':7})
    # sage: assert MPInv._eval('lambda x,y: max(x - 13,-3)', {'x': 11,'y':100}) == -2
    # sage: assert MPInv._eval('lambda x,y: max(x - 13,-3) >= y', {'x': 11,'y':-2}) == True
    # sage: assert MPInv._eval('lambda x,y: max(x - 13,-3) <= y', {'x': 11,'y':100}) == True
    # sage: assert MPInv._eval('lambda x,y: x+y == 6', {'x': 2,'y':3,'d':7}) == False
    # sage: assert MPInv._eval('lambda x,y: x+y == 1 or x + y == 2', {'x': 2,'y':3,'d':7}) == False
    """
    assert isinstance(lambda_str, str) and 'lambda' in lambda_str
    assert trace, trace

    f = sage.all.sage_eval(lambda_str)
    symbols = f.func_code.co_varnames
    # if trace has more keys than variables in lambda str then remove them
    trace = dict([(s, trace[s]) for s in symbols])
    rs = f(**trace)
    return rs

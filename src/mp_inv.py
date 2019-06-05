"""
Min/Max Plus invariants
"""
import itertools
import pdb

from miscs import Miscs

dbg = pdb.set_trace


class MPInv(object):

    def __init__(self, lh, rh):
        self.lh = lh
        self.rh = rh

    @property
    def symbols(self):
        return Miscs.getVars(self.lh + self.rh)

    def get_lambda_disj(self, is_eq, is_formula):
        """
        shortcut that creates lambda expr and disj formula
        """
        lambda_fun = self.get_lambda_fun(is_eq=is_eq, is_formula=True)
        disj_expr = self.get_disj_expr(is_eq)
        return (r_lambda, r_disj)

    def get_lambda_fun(self, is_eq=False, is_formula=False):
        """
        Return string representing a lambda function
        lambda x, y, ... = max(x, y...) >= max(x, y...)

        sage: var('x y z t s w')
        (x, y, z, t, s, w)

        sage: MaxPlusInv((x-10, y-3), (y,5)).get_lambda_fun(is_formula=True,is_eq=False)
        'lambda x,y: max(x - 10, y - 3) - max(y, 5) >= 0'

        sage: MaxPlusInv((x-10, y-3), (y, 5)).get_lambda_fun(is_formula=True,is_eq=False)
        'lambda x,y: max(x - 10, y - 3) - max(y, 5) >= 0'

        sage: MaxPlusInv((x-10, y-3), (y, 5)).get_lambda_fun(is_formula=False,is_eq=False)
        'lambda x,y: max(x - 10, y - 3) - max(y, 5)'

        sage: MaxPlusInv((x-10, y-3), (y,)).get_lambda_fun(is_formula=False,is_eq=False)
        'lambda x,y: max(x - 10, y - 3) - y'

        sage: MaxPlusInv((x-10, y-3), (y,)).get_lambda_fun(is_formula=False,is_eq=True)
        'lambda x,y: max(x - 10, y - 3) - y'

        sage: MaxPlusInv((x-10, y-3), (y,)).get_lambda_fun(is_formula=True,is_eq=True)
        'lambda x,y: max(x - 10, y - 3) - y == 0'

        sage: MinPlusInv((x-10, y-3), (y+12,)).get_lambda_fun(is_formula=True,is_eq=True)
        'lambda x,y: min(x - 10, y - 3) - (y + 12) == 0'

        sage: MinPlusInv((x-10, y-3), (y+12,)).get_lambda_fun(is_formula=True,is_eq=True)
        'lambda x,y: min(x - 10, y - 3) - (y + 12) == 0'
        """
        def f(ls):
            assert ls
            if len(ls) >= 2:
                return '{}({})'.format(self.MYOP, ', '.join(map(str, ls)))
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

        symbols_str = ','.join(map(str, self.symbols))
        expr_str = "{} - {}".format(f(self.lh), f(self.rh))
        if is_formula:
            rel = '==' if is_eq else '>='
            expr_str = "{} {} 0".format(expr_str, rel)
        return "lambda {}: {}".format(symbols_str, expr_str)

    def get_disj_expr(self, is_eq):
        """
        Return disjunctive format

        Examples:

        sage: var('y')
        y

        sage: MaxPlusInv((x-10, y-3), (y+12,)).get_disj_expr(is_eq=True)
        'If(x - 10 >= y - 3, x - 10 == y + 12, y - 3 == y + 12)'

        sage: MaxPlusInv((x-10, y-3), (y+12,)).get_disj_expr(is_eq=False)
        'If(x - 10 >= y - 3, x - 10 >= y + 12, y - 3 >= y + 12)'

        sage: MinPlusInv((x-10, y-3), (y+12,)).get_disj_expr(is_eq=False)
        'If(x - 10 <= y - 3, x - 10 >= y + 12, y - 3 >= y + 12)'

        sage: MinPlusInv((x-10, y-3), (y+12,)).get_disj_expr(is_eq=False)
        'If(x - 10 <= y - 3, x - 10 >= y + 12, y - 3 >= y + 12)'

        sage: MinPlusInv((x-10, y-3), (y, 12)).get_disj_expr(is_eq=False)
        'If(x - 10 <= y - 3, If(y <= 12, x - 10 >= y, x - 10 >= 12), If(y <= 12, y - 3 >= y, y - 3 >= 12))'

        sage: MinPlusInv((x-10, y-3),(y, 12)).get_disj_expr(is_eq=True)
        'If(x - 10 <= y - 3, If(y <= 12, x - 10 == y, x - 10 == 12), If(y <= 12, y - 3 == y, y - 3 == 12))'
        """
        return MPInv.mp2df(self.lh, self.rh, 0, isinstance(self, MaxPlusInv), is_eq)

    @staticmethod
    def mp2df(lh, rh, idx, is_maxplus, is_eq):
        assert lh, lh
        assert rh, rh

        elem = lh[idx]
        if isinstance(rh, tuple):
            disj = MPInv.mp2df(rh, elem, 0, is_maxplus, is_eq)
        else:
            disj = "{} {} {}".format(rh, '==' if is_eq else '>=', elem)
        rest = lh[idx + 1:]

        if not rest:  # t <= max(x,y,z)
            return disj
        else:
            rest_disj = MPInv.mp2df(lh, rh, idx + 1, is_maxplus, is_eq)

            op = '>=' if is_maxplus else '<='
            others = lh[:idx] + rest

            conds = ["{} {} {}".format(elem, op, t) for t in others]
            if len(conds) >= 2:
                cond = 'And({})'.format(', '.join(conds))
            else:
                cond = conds[0]

            return "If({}, {}, {})".format(cond, disj, rest_disj)

    @staticmethod
    def get_terms(terms):
        """
        Generate (weak) mp terms of the form
        max(c1+x1,...,cn+xn,c0) >= xi,
        where ci are in cs (e.g., 0,-oo for max plus)

        sage: var('x y z t s w')
        (x, y, z, t, s, w)

        sage: ts = MPInv.get_terms([x,y])
        sage: assert len(ts) == 5
        sage: sorted(ts, key=lambda x: str(x))
        [((0,), x), ((0,), y), ((x, 0), y), ((y, 0), x), ((y,), x)]

        sage: ts = MPInv.get_terms([x,y,z])
        sage: assert len(ts) == 18
        sage: sorted(ts, key=lambda x: str(x))
        [((0,), x),
        ((0,), y),
        ((0,), z),
        ((x, 0), y),
        ((x, 0), z),
        ((x, y), z),
        ((x, y, 0), z),
        ((x, z), y),
        ((x, z, 0), y),
        ((y, 0), x),
        ((y, 0), z),
        ((y, z), x),
        ((y, z, 0), x),
        ((y,), x),
        ((z, 0), x),
        ((z, 0), y),
        ((z,), x),
        ((z,), y)]

        sage: assert(len(MPInv.get_terms([x,y,z,w]))) == 54
        sage: assert len(MPInv.get_terms([x,y,z,t,s])) == 145

        """
        assert terms, terms

        results = set(((0,), t) for t in terms)

        terms = sorted(terms, key=lambda x: str(x))
        for i, term in enumerate(terms):
            terms_ = terms[:i] + terms[i+1:]
            powerset = itertools.chain.from_iterable(
                itertools.combinations(terms_, r) for r in range(len(terms_)+1))
            powerset = [ps for ps in powerset if ps]
            for pset in powerset:
                results.add((tuple(list(pset) + [0]), term))
                # ignore [y], x if [x],y exists
                if not(len(pset) == 1 and ((term,), pset[0]) in results):
                    results.add((pset, term))
        return results

    @staticmethod
    def test_trace(lambda_str, trace):
        """
        Examples:

        sage: assert bool(MPInv.test_trace('lambda x,y: x+y == 5', {'x': 2,'y':3,'d':7}))
        sage: assert MPInv.test_trace('lambda x,y: x+y == 10 or x + y == 5', {'x': 2,'y':3,'d':7})
        sage: assert bool(MPInv.test_trace('lambda x,y: max(x - 13,-3) >= y', {'x': 11,'y':100})) == False
        sage: assert MPInv.test_trace('lambda x,y: x+y == 6', {'x': 2,'y':3,'d':7}) == False
        sage: assert MPInv.test_trace('lambda x,y: x+y == 1 or x + y == 2', {'x': 2,'y':3,'d':7}) == False
        sage: assert MPInv.test_trace('lambda x,y: x+y', {'x': 2,'y':3,'d':7}) == 5

        """
        assert isinstance(lambda_str, str) and 'lambda' in lambda_str

        f = sage.all.sage_eval(lambda_str)
        symbols = f.func_code.co_varnames
        # if trace has more keys than variables in lambda str then remove tehm
        trace = dict([(s, trace[s]) for s in symbols])
        rs = f(**trace)
        return rs


class MaxPlusInv(MPInv):
    MYOP = 'max'
    pass


class MinPlusInv(MPInv):
    MYOP = 'min'
    pass


def infer(terms, traces, is_maxplus=True):
    mp_terms = MPInv.get_terms(terms)
    results = []
    for lh, rh in mp_terms:
        mpinv = MaxPlusInv(lh, (rh,))
        mylambda = mpinv.get_lambda_fun(is_eq=False, is_formula=False)
        myevals = [mpinv.test_trace(mylambda, trace) for trace in traces]
        mymin = min(myevals)  # lh >= rh + mymin
        mymax = max(myevals)  # rh + mymax >= lh
        print mymin, mymax
        if mymin == mymax:  # lh == rh + mymin
            mpinv = MaxPlusInv(lh, (rh + mymin, ))
            disj_eq = mpinv.get_lambda_disj(is_eq=True)
            results.append(disj_eq)
        else:
            mpinv_upper = MaxPlusInv(lh, (rh + mymin, ))
            print mpinv_upper.lh, mpinv_upper.rh
            disj_upper = mpinv_upper.get_lambda_disj(
                is_eq=False, is_formula=True)
            mpinv_lower = MaxPlusInv((rh + mymax, ), lh)
            disj_lower = mpinv_lower.get_lambda_disj(
                is_eq=False, is_formula=True)
            results.extend([disj_upper, disj_lower])
    return results

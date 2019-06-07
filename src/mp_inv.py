"""
Min/Max Plus invariants
"""
import itertools
import pdb
import sage.all
from miscs import Miscs

dbg = pdb.set_trace


class MPInv(object):
    """
    sage: var('x y z t s w')
    (x, y, z, t, s, w)

    sage: mp = MaxPlusIeq((x-10, y-3), (y,5))
    sage: mp.str_lambda_formula
    'lambda x,y: max(x - 10, y - 3) - max(y, 5) >= 0'
    sage: mp.str_lambda
    'lambda x,y: max(x - 10, y - 3) - max(y, 5)'
    sage: mp.str_disj
    'If(x - 10 >= y - 3, If(y >= 5, x - 10 >= y, x - 10 >= 5), If(y >= 5, y - 3 >= y, y - 3 >= 5))'

    sage: mp = MinPlusIeq((x-10, y-3), (y, 5))
    sage: mp.str_lambda_formula
    'lambda x,y: min(x - 10, y - 3) - min(y, 5) >= 0'
    sage: mp.str_disj
    'If(x - 10 <= y - 3, If(y <= 5, x - 10 >= y, x - 10 >= 5), If(y <= 5, y - 3 >= y, y - 3 >= 5))'

    sage: mp = MaxPlusInv((x-10, y-3), (y,))
    sage: mp.str_lambda
    'lambda x,y: max(x - 10, y - 3) - y'


    sage: mp = MaxPlusEq((x-10, y-3), (y,))
    sage: mp.str_lambda
    'lambda x,y: max(x - 10, y - 3) - y'
    sage: mp.str_lambda_formula
    'lambda x,y: max(x - 10, y - 3) - y == 0'
    sage: mp.str_disj
    'If(x - 10 >= y - 3, x - 10 == y, y - 3 == y)'

    sage: mp = MinPlusEq((x-10, y-3), (y+12,))
    sage: mp.str_lambda
    'lambda x,y: min(x - 10, y - 3) - (y + 12)'
    sage: mp.str_lambda_formula
    'lambda x,y: min(x - 10, y - 3) - (y + 12) == 0'
    sage: mp.str_disj
    'If(x - 10 <= y - 3, x - 10 == y + 12, y - 3 == y + 12)'

    sage: MaxPlusEq((x-10, y-3), (y+12,)).str_disj
    'If(x - 10 >= y - 3, x - 10 == y + 12, y - 3 == y + 12)'

    sage: MaxPlusIeq((x-10, y-3), (y+12,)).str_disj
    'If(x - 10 >= y - 3, x - 10 >= y + 12, y - 3 >= y + 12)'

    sage: MinPlusIeq((x-10, y-3), (y+12,)).str_disj
    'If(x - 10 <= y - 3, x - 10 >= y + 12, y - 3 >= y + 12)'

    sage: MinPlusIeq((x-10, y-3), (y+12,)).str_disj
    'If(x - 10 <= y - 3, x - 10 >= y + 12, y - 3 >= y + 12)'

    sage: MinPlusIeq((x-10, y-3), (y, 12)).str_disj
    'If(x - 10 <= y - 3, If(y <= 12, x - 10 >= y, x - 10 >= 12), If(y <= 12, y - 3 >= y, y - 3 >= 12))'

    sage: MinPlusEq((x-10, y-3),(y, 12)).str_disj
    'If(x - 10 <= y - 3, If(y <= 12, x - 10 == y, x - 10 == 12), If(y <= 12, y - 3 == y, y - 3 == 12))'

    sage: mp = MaxPlusIeq((0,), (x - 15,))
    sage: mp.str_lambda
    'lambda x: 0 - (x - 15)'
    sage: mp.str_lambda_formula
    'lambda x: 0 - (x - 15) >= 0'
    sage: mp.str_disj
    '0 >= x - 15'
    """

    def __init__(self, lh, rh):
        assert isinstance(lh, tuple) and lh, lh
        assert isinstance(rh, tuple) and rh, rh

        self.lh = lh
        self.rh = rh

    @property
    def symbols(self):
        try:
            return self._symbols
        except AttributeError:
            self._symbols = Miscs.getVars(self.lh + self.rh)
            return self._symbols

    # Lambda function
    @property
    def __str_lambda(self):
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

        return "lambda {}: {}".format(symbols_str, expr_str)

    @property
    def str_lambda(self):
        """
        Return string representing a lambda function
        lambda x, y, ... = max(x, y...) >= max(x, y...)

        """

        try:
            return self._str_lambda
        except AttributeError:
            self._str_lambda = self.__str_lambda
            return self._str_lambda

    @property
    def str_lambda_formula(self):
        try:
            return self._str_lambda_formula
        except AttributeError:
            self._str_lambda_formula = "{} {} 0".format(
                self.str_lambda, self.RELOP)
            return self._str_lambda_formula

    # Disj Formula
    @property
    def str_disj(self):
        """
        Return disjunctive format
        """
        try:
            return self._str_disj
        except AttributeError:
            self._str_disj = self.mp2df(
                self.lh, self.rh, 0, self.MYOP1, self.RELOP)
            return self._str_disj

    @classmethod
    def mp2df(cls, lh, rh, idx, myop, relop):
        assert isinstance(lh, tuple) and lh

        elem = lh[idx]
        if isinstance(rh, tuple):
            disj = cls.mp2df(rh, elem, 0, myop, relop)
        else:
            disj = "{} {} {}".format(rh, relop, elem)
        rest = lh[idx + 1:]

        if not rest:  # t <= max(x,y,z)
            return disj
        else:
            rest_disj = cls.mp2df(lh, rh, idx + 1, myop, relop)

            others = lh[:idx] + rest

            conds = ["{} {} {}".format(elem, myop, t) for t in others]
            if len(conds) >= 2:
                cond = 'And({})'.format(', '.join(conds))
            else:
                cond = conds[0]

            return "If({}, {}, {})".format(cond, disj, rest_disj)

    @classmethod
    def get_terms(cls, terms):
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
        terms = sorted(terms, key=lambda x: str(x))
        results = set(((0,), t) for t in terms)
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

        results = sorted(results, key=lambda x: str(x))
        return results

    @classmethod
    def test_trace(cls, lambda_str, trace):
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
        # if trace has more keys than variables in lambda str then remove them
        trace = dict([(s, trace[s]) for s in symbols])
        rs = f(**trace)
        return rs

    @classmethod
    def reformat_trace(cls, trace):
        return {str(x): trace[x] for x in trace}

    @classmethod
    def infer(cls, terms, traces):
        """
        sage: x, y, z = sage.all.var('x y z')
        sage: tcs = [{'x': 2, 'y': -8, 'z': -7}, {'x': -1, 'y': -15, 'z': 88}, {'x': 15, 'y': 5, 'z': 0}]
        sage: invs = MaxPlusIeq.infer([x, y], tcs)
        sage: assert len(invs) == 10
        sage: for inv in invs: print(inv.str_disj)
        0 >= x - 15
        x + 1 >= 0
        0 >= y - 5
        y + 15 >= 0
        If(x >= 0, x >= y + 10, 0 >= y + 10)
        If(x >= 0, y + 15 >= x, y + 15 >= 0)
        If(y >= 0, y >= x - 10, 0 >= x - 10)
        If(y >= 0, x + 1 >= y, x + 1 >= 0)
        y >= x - 14
        x - 10 >= y

        sage: invs = MaxPlusIeq.infer([x], tcs)
        sage: print('\n'.join(inv.str_disj for inv in invs))
        0 >= x - 15
        x + 1 >= 0

        sage: invs = MaxPlusIeq.infer([x,y,z], tcs)
        sage: assert len(invs) == 36

        """

        terms = cls.get_terms(terms)
        results = []
        for lhs, rhs in terms:
            mpinv = cls(lhs, (rhs,))
            myevals = [mpinv.test_trace(mpinv.str_lambda, trace)
                       for trace in traces]
            mymin = min(myevals)  # lh >= rh + mymin
            mymax = max(myevals)  # rh + mymax >= lh

            if mymin == mymax:  # lh == rh + mymin
                assert False
                if isinstance(cls, MaxPlusInv):
                    newcls = MaxPlusEq
                else:
                    assert isinstance(cls, MinPlusInv)
                    newcls = MinPlusEq
                mpinv_eq = newcls(lhs, (rhs + mymin, ))
                results.append(mpinv_eq)
            else:
                mpinv_upper = cls(lhs, (rhs + mymin, ))
                mpinv_lower = cls((rhs + mymax, ), lhs)
                results.extend([mpinv_upper, mpinv_lower])
        return results


class MaxPlusInv(MPInv):
    MYOP = 'max'
    MYOP1 = ">="
    pass


class MaxPlusEq(MaxPlusInv):
    RELOP = '=='
    pass


class MaxPlusIeq(MaxPlusInv):
    RELOP = '>='
    pass


class MinPlusInv(MPInv):
    MYOP = 'min'
    MYOP1 = "<="

    pass


class MinPlusEq(MinPlusInv):
    RELOP = '=='
    pass


class MinPlusIeq(MinPlusInv):
    RELOP = '>='
    pass


"""
# :: var('y z')
# (y, z)
# :: tcs = [{x:2,y:-8,z:-7},{x:-1,y:-15,z:88},{x:15,y:5,z:0}]
# :: ieq = IeqMPPFixed(terms=[x,y],tcs=tcs,xinfo={'Input':[],'Output':[]})
# dig:Info:*** IeqMPPFixed ***
# :: ieq.solve()
# dig_polynomials:Debug:Build (fixed max-plus) poly from 3 tcs (~ 10 facets)
# :: Inv.print_invs(ieq.sols)
# 0: -y + 5 >= 0, 0 >= y - 5
# 1: x + 1 >= 0, x + 1 >= 0
# 2: -x + 15 >= 0, 0 >= x - 15
# 3: x - y - 10 >= 0, x >= y + 10
# 4: -x + y + 14 >= 0, y + 14 >= x
# 5: y + 15 >= 0, y + 15 >= 0
# 6: max(x,0) - (y + 10) >= 0, If(x >= 0,x >= y + 10,0 >= y + 10)
# 7: x + 1 - max(y,0) >= 0, If(y >= 0, x + 1 >= y, x + 1 >= 0)
# 8: max(y,0) - (x - 10) >= 0, If(y >= 0,y >= x - 10,0 >= x - 10)
# 9: y + 15 - max(x,0) >= 0, If(x >= 0, y + 15 >= x, y + 15 >= 0)

# :: ieq = IeqMPPFixed(terms=[x,y,z],tcs=tcs,xinfo={'Input':[],'Output':[]})
# dig:Info:*** IeqMPPFixed ***
# :: ieq.solve()
# dig_polynomials:Debug:Build (fixed max-plus) poly from 3 tcs (~ 36 facets)
# :: Inv.print_invs(ieq.sols)
# 0: -y + 5 >= 0, 0 >= y - 5
# 1: x + 1 >= 0, x + 1 >= 0
# 2: -y + z + 5 >= 0, z + 5 >= y
# 3: z + 7 >= 0, z + 7 >= 0
# 4: -x + 15 >= 0, 0 >= x - 15
# 5: -z + 88 >= 0, 0 >= z - 88
# 6: x - y - 10 >= 0, x >= y + 10
# 7: x - z + 89 >= 0, x >= z - 89
# 8: -x + y + 14 >= 0, y + 14 >= x
# 9: y + 15 >= 0, y + 15 >= 0
# 10: -x + z + 15 >= 0, z + 15 >= x
# 11: y - z + 103 >= 0, y >= z - 103
# 12: max(z,0) - (y - 5) >= 0, If(z >= 0,z >= y - 5,0 >= y - 5)
# 13: max(x,0) - (y + 10) >= 0, If(x >= 0,x >= y + 10,0 >= y + 10)
# 14: max(x,0) - (z - 88) >= 0, If(x >= 0,x >= z - 88,0 >= z - 88)
# 15: max(x,y) - (z - 89) >= 0, If(x >= y,x >= z - 89,y >= z - 89)
# 16: max(x,z) - (y + 10) >= 0, If(x >= z,x >= y + 10,z >= y + 10)
# 17: x + 1 - max(y,0) >= 0, If(y >= 0, x + 1 >= y, x + 1 >= 0)
# 18: z + 7 - max(y,0) >= 0, If(y >= 0, z + 7 >= y, z + 7 >= 0)
# 19: max(y,0) - (x - 10) >= 0, If(y >= 0,y >= x - 10,0 >= x - 10)
# 20: max(y,0) - (z - 88) >= 0, If(y >= 0,y >= z - 88,0 >= z - 88)
# 21: max(y,z) - (x - 10) >= 0, If(y >= z,y >= x - 10,z >= x - 10)
# 22: max(z,0) - (x - 15) >= 0, If(z >= 0,z >= x - 15,0 >= x - 15)
# 23: y + 15 - max(x,0) >= 0, If(x >= 0, y + 15 >= x, y + 15 >= 0)
# 24: z + 15 - max(x,0) >= 0, If(x >= 0, z + 15 >= x, z + 15 >= 0)
# 25: z + 15 - max(x,y) >= 0, If(x >= y, z + 15 >= x, z + 15 >= y)
# 26: x + 89 - max(y,z) >= 0, If(y >= z, x + 89 >= y, x + 89 >= z)
# 27: x + 89 - max(z,0) >= 0, If(z >= 0, x + 89 >= z, x + 89 >= 0)
# 28: y + 103 - max(x,z) >= 0, If(x >= z, y + 103 >= x, y + 103 >= z)
# 29: y + 103 - max(z,0) >= 0, If(z >= 0, y + 103 >= z, y + 103 >= 0)
# 30: max(x,y,0) - (z - 88) >= 0, If(And(x >= y,x >= 0),x >= z - 88,If(And(y >= x,y >= 0),y >= z - 88,0 >= z - 88))
# 31: max(x,z,0) - (y + 10) >= 0, If(And(x >= z,x >= 0),x >= y + 10,If(And(z >= x,z >= 0),z >= y + 10,0 >= y + 10))
# 32: max(y,z,0) - (x - 10) >= 0, If(And(y >= z,y >= 0),y >= x - 10,If(And(z >= y,z >= 0),z >= x - 10,0 >= x - 10))
# 33: z + 15 - max(x,y,0) >= 0, If(And(x >= y,x >= 0), z + 15 >= x, If(And(y >= x,y >= 0), z + 15 >= y, z + 15 >= 0))
# 34: x + 89 - max(y,z,0) >= 0, If(And(y >= z,y >= 0), x + 89 >= y, If(And(z >= y,z >= 0), x + 89 >= z, x + 89 >= 0))
# 35: y + 103 - max(x,z,0) >= 0, If(And(x >= z,x >= 0), y + 103 >= x, If(And(z >= x,z >= 0), y + 103 >= z, y + 103 >= 0))


# :: ieq.subset_siz = 2
# :: ieq.solve()
# dig_polynomials:Debug:Build (fixed max-plus) poly from 3 tcs (~ 24 facets)
# :: Inv.print_invs(ieq.sols)
# 0: -y + 5 >= 0, 0 >= y - 5
# 1: x + 1 >= 0, x + 1 >= 0
# 2: -y + z + 5 >= 0, z + 5 >= y
# 3: z + 7 >= 0, z + 7 >= 0
# 4: -x + 15 >= 0, 0 >= x - 15
# 5: -z + 88 >= 0, 0 >= z - 88
# 6: x - y - 10 >= 0, x >= y + 10
# 7: x - z + 89 >= 0, x >= z - 89
# 8: -x + y + 14 >= 0, y + 14 >= x
# 9: y + 15 >= 0, y + 15 >= 0
# 10: -x + z + 15 >= 0, z + 15 >= x
# 11: y - z + 103 >= 0, y >= z - 103
# 12: max(z,0) - (y - 5) >= 0, If(z >= 0,z >= y - 5,0 >= y - 5)
# 13: max(x,0) - (y + 10) >= 0, If(x >= 0,x >= y + 10,0 >= y + 10)
# 14: max(x,0) - (z - 88) >= 0, If(x >= 0,x >= z - 88,0 >= z - 88)
# 15: x + 1 - max(y,0) >= 0, If(y >= 0, x + 1 >= y, x + 1 >= 0)
# 16: z + 7 - max(y,0) >= 0, If(y >= 0, z + 7 >= y, z + 7 >= 0)
# 17: max(y,0) - (x - 10) >= 0, If(y >= 0,y >= x - 10,0 >= x - 10)
# 18: max(y,0) - (z - 88) >= 0, If(y >= 0,y >= z - 88,0 >= z - 88)
# 19: max(z,0) - (x - 15) >= 0, If(z >= 0,z >= x - 15,0 >= x - 15)
# 20: y + 15 - max(x,0) >= 0, If(x >= 0, y + 15 >= x, y + 15 >= 0)
# 21: z + 15 - max(x,0) >= 0, If(x >= 0, z + 15 >= x, z + 15 >= 0)
# 22: x + 89 - max(z,0) >= 0, If(z >= 0, x + 89 >= z, x + 89 >= 0)
# 23: y + 103 - max(z,0) >= 0, If(z >= 0, y + 103 >= z, y + 103 >= 0)



# :: tcs=[{x:8,y:8},{x:0,y:-15},{x:0,y:0},{x:1,y:1}]
# :: ieq = IeqMPPFixed(terms=[x,y],tcs=tcs,xinfo={'Input':[],'Output':[]})
# dig:Info:*** IeqMPPFixed ***
# :: ieq.solve()
# dig_polynomials:Debug:Build (fixed max-plus) poly from 4 tcs (~ 10 facets)
# :: ieq.refine()
# :: Inv.print_invs(ieq.sols)
# 0: max(y,0) - (x) == 0, If(y >= 0,y == x,0 == x)
# 1: x >= 0, x >= 0
# 2: x - y >= 0, x >= y
# 3: -x + 8 >= 0, 0 >= x - 8
# 4: -y + 8 >= 0, 0 >= y - 8
# 5: y + 15 >= 0, y + 15 >= 0
# 6: -x + y + 15 >= 0, y + 15 >= x
# 7: max(x,0) - (y) >= 0, If(x >= 0,x >= y,0 >= y)
# 8: y + 15 - max(x,0) >= 0, If(x >= 0, y + 15 >= x, y + 15 >= 0)
# """


# def infer(terms, traces, is_maxplus=True):
#     mp_terms = MPInv.get_terms(terms)
#     results = []
#     for lh, rh in mp_terms:
#         mpinv = MaxPlusInv(lh, (rh,))
#         print 'processing', mpinv.lh, mpinv.rh
#         mylambda = mpinv.get_lambda_fun(is_eq=False, is_formula=False)
#         print 'mylambda', mylambda
#         myevals = [mpinv.test_trace(mylambda, trace) for trace in traces]
#         mymin = min(myevals)  # lh >= rh + mymin
#         mymax = max(myevals)  # rh + mymax >= lh

#         if mymin == mymax:  # lh == rh + mymin
#             mpinv = MaxPlusInv(lh, (rh + mymin, ))
#             disj_eq = mpinv.get_lambda_disj(is_eq=True)
#             results.append(disj_eq)
#         else:
#             mpinv_upper = MaxPlusInv(lh, (rh + mymin, ))
#             print mpinv_upper.lh, mpinv_upper.rh
#             disj_upper = mpinv_upper.get_lambda_disj(
#                 is_eq=False, is_formula=True)
#             mpinv_lower = MaxPlusInv((rh + mymax, ), lh)
#             disj_lower = mpinv_lower.get_lambda_disj(
#                 is_eq=False, is_formula=True)
#             results.extend([disj_upper, disj_lower])
#     return results

# def get_lambda_fun(self, is_eq, is_formula):
#     """
#     str_lambda = self.str_lambda
#     if is_formula:
#         str_lambda = "{} {} 0".format(str_lambda, '==' if is_eq else '>=')
#     return str_lambda

# def get_lambda_disj(self, is_eq, is_formula):
#     """
#     shortcut that creates lambda expr and disj formula
#     """
#     lambda_fun = self.get_lambda_fun(is_eq=is_eq, is_formula=True)
#     disj_expr = self.get_disj_expr(is_eq)
#     return (lambda_fun, disj_expr)

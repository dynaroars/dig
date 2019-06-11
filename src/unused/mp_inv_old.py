"""
Min/Max Plus invariants
"""
import itertools
import pdb

from miscs import Miscs

dbg = pdb.set_trace


class MP_Inv(object):

    def __init__(self, lh, rh):
        self.lh = lh
        self.rh = rh

    @staticmethod
    def get_terms(cls, terms):
        """
        Generate mp terms of the form
        max(c1+x1,...,cn+xn,c0) >= xi,
        where ci are in cs (e.g., 0,-oo for max plus)

        sage: var('x y z t s w')
        (x, y, z, t, s, w)

        sage: ts = _get_terms_mpp([x,y,z,t,s],[]); len(ts)
        145

        sage: ts = _get_terms_mpp([x,y,z],[]); ts; len(ts)
        [([x, y, 0], z),
        ([x, y], z),
        ([x, z, 0], y),
        ([x, z], y),
        ([x, 0], y),
        ([x, 0], z),
        ([x], y),
        ([x], z),
        ([y, z, 0], x),
        ([y, z], x),
        ([y, 0], x),
        ([y, 0], z),
        ([y], z),
        ([z, 0], x),
        ([z, 0], y),
        ([0], x),
        ([0], y),
        ([0], z)]
        18


        sage: ts = _get_terms_mpp([x,y,z],['z']); ts; len(ts)
        [([x, y, 0], z),
        ([x, y], z),
        ([x, 0], z),
        ([x], z),
        ([y, 0], z),
        ([y], z),
        ([z, 0], x),
        ([z, 0], y),
        ([0], x),
        ([0], y)]
        10

        sage: ts = _get_terms_mpp([x,y,z],['x','y']); ts; len(ts)
        [([x, y, 0], z),
        ([x, y], z),
        ([x, 0], z),
        ([x], z),
        ([y, 0], z),
        ([y], z),
        ([z, 0], x),
        ([z, 0], y),
        ([0], z)]
        9

        sage: ts = _get_terms_mpp([x,y,z],['x','y','z']); len(ts)
        0

        sage: ts = _get_terms_mpp([x,y,z,w],[]); ts; len(ts)
        [([x, y, z, 0], w),
        ([x, y, z], w),
        ([x, y, w, 0], z),
        ([x, y, w], z),
        ([x, y, 0], z),
        ([x, y, 0], w),
        ([x, y], z),
        ([x, y], w),
        ([x, z, w, 0], y),
        ([x, z, w], y),
        ([x, z, 0], y),
        ([x, z, 0], w),
        ([x, z], y),
        ([x, z], w),
        ([x, w, 0], y),
        ([x, w, 0], z),
        ([x, w], y),
        ([x, w], z),
        ([x, 0], y),
        ([x, 0], z),
        ([x, 0], w),
        ([x], y),
        ([x], z),
        ([x], w),
        ([y, z, w, 0], x),
        ([y, z, w], x),
        ([y, z, 0], x),
        ([y, z, 0], w),
        ([y, z], x),
        ([y, z], w),
        ([y, w, 0], x),
        ([y, w, 0], z),
        ([y, w], x),
        ([y, w], z),
        ([y, 0], x),
        ([y, 0], z),
        ([y, 0], w),
        ([y], z),
        ([y], w),
        ([z, w, 0], x),
        ([z, w, 0], y),
        ([z, w], x),
        ([z, w], y),
        ([z, 0], x),
        ([z, 0], y),
        ([z, 0], w),
        ([z], w),
        ([w, 0], x),
        ([w, 0], y),
        ([w, 0], z),
        ([0], x),
        ([0], y),
        ([0], z),
        ([0], w)]
        54


        sage: ts = _get_terms_mpp([x,y,z,w],['z','w']); ts; len(ts)
        [([x, y, 0], z),
        ([x, y, 0], w),
        ([x, y], z),
        ([x, y], w),
        ([x, 0], z),
        ([x, 0], w),
        ([x], z),
        ([x], w),
        ([y, 0], z),
        ([y, 0], w),
        ([y], z),
        ([y], w),
        ([z, w, 0], x),
        ([z, w, 0], y),
        ([z, w], x),
        ([z, w], y),
        ([z, 0], x),
        ([z, 0], y),
        ([w, 0], x),
        ([w, 0], y),
        ([0], x),
        ([0], y)]
        22

        sage: ts = _get_terms_mpp([x,y,z,w],['x','y','z']); ts; len(ts)
        [([x, y, z, 0], w),
        ([x, y, z], w),
        ([x, y, 0], w),
        ([x, y], w),
        ([x, z, 0], w),
        ([x, z], w),
        ([x, 0], w),
        ([x], w),
        ([y, z, 0], w),
        ([y, z], w),
        ([y, 0], w),
        ([y], w),
        ([z, 0], w),
        ([z], w),
        ([w, 0], x),
        ([w, 0], y),
        ([w, 0], z),
        ([0], w)]
        18


        sage: ts = _get_terms_mpp([x,y],[]); ts; len(ts)
        [([x, 0], y), ([x], y), ([y, 0], x), ([0], x), ([0], y)]
        5
        """
        assert terms, terms

        results = set(((0,), t) for t in terms)
        terms = sorted(terms, key=lambda x: str(x), reverse=True)
        for i, term in enumerate(terms):
            terms_ = terms[:i] + terms[i+1:]
            powerset = itertools.chain.from_iterable(
                itertools.combinations(terms_, r) for r in range(len(terms_)+1))
            powerset = [ps for ps in powerset if ps]
            # print powerset
            for pset in powerset:
                results.add((tuple(list(pset) + [0]), term))
                # ignore [y], x if [x],y exists
                if not(len(pset) == 1 and ((term,), pset[0]) in results):
                    results.add((pset, term))

        return results


class MaxPlus_Inv(Inv):
    pass


class MinPlusInv(Inv):
    pass


def solve(terms, traces, is_maxplus=True):
    mp_terms = get_terms_mp(terms)
    results = []
    for lh, rh in mp_terms:
        mylambda = get_lambda_str(
            lh, (rh,), is_maxplus, is_eq=False, is_formula=False)
        print(lh, rh)
        print(mylambda)
        myevals = [test_trace(mylambda, trace) for trace in traces]
        print myevals

        mymin = min(myevals)  # lh >= rh + mymin
        mymax = max(myevals)  # rh + mymax >= lh

        if mymin == mymax:  # lh == rh + mymin
            disj_eq = get_lambda_disj(
                lh, [rh + mymin], is_maxplus, is_eq=True)
            results.append(disj_eq)
        else:
            disj_upper = get_lambda_disj(
                lh, (rh + mymin,), is_maxplus, is_eq=False)
            disj_lower = get_lambda_disj(
                (rh + mymax,), lh, is_maxplus, is_eq=False)
            results.extend([disj_upper, disj_lower])
    return results


def get_lambda_disj(lh, rh, is_maxplus, is_eq):
    """
    shortcut that creates lambda expr and disj formula
    """
    r_lambda = get_lambda_str(lh, rh,
                              is_maxplus, is_formula=True,
                              is_eq=is_eq)
    r_disj = get_disj_exp(lh, rh, is_maxplus, is_eq)
    return (r_lambda, r_disj)


def get_disj_exp(lh, rh, is_maxplus, is_eq):
    """
    Return disjunctive format

    Examples:

    sage: var('y')
    y

    sage: IeqMPP.get_disj_exp([x-10,y-3],[y+12], is_maxplus=True,is_eq=True)
    'If(x - 10 >= y - 3,x - 10 == y + 12,y - 3 == y + 12)'

    sage: IeqMPP.get_disj_exp([x-10,y-3],[y+12], is_maxplus=True,is_eq=False)
    'If(x - 10 >= y - 3,x - 10 >= y + 12,y - 3 >= y + 12)'

    sage: IeqMPP.get_disj_exp([x-10,y-3],[y+12], is_maxplus=False,is_eq=False)
    'If(x - 10 <= y - 3,x - 10 >= y + 12,y - 3 >= y + 12)'

    sage: IeqMPP.get_disj_exp([x-10, y-3],[y+12], is_maxplus=False,is_eq=False)
    'If(x - 10 <= y - 3,x - 10 >= y + 12,y - 3 >= y + 12)'

    sage: IeqMPP.get_disj_exp(
        [x-10, y-3],[y, 12], is_maxplus=False,is_eq=False)
    'If(x - 10 <= y - 3,If(y <= 12, x - 10 >= y, x - 10 >= 12),If(y <= 12, y - 3 >= y, y - 3 >= 12))'

    sage: IeqMPP.get_disj_exp([x-10,y-3],[y,12], is_maxplus=False,is_eq=True)
    'If(x - 10 <= y - 3,If(y <= 12, x - 10 == y, x - 10 == 12),If(y <= 12, y - 3 == y, y - 3 == 12))'
    """
    assert isinstance(lh, tuple), lh
    assert isinstance(rh, tuple), rh
    return mp2df(lh, rh, 0, is_maxplus, is_eq)


def mp2df(lh, rh, idx, is_maxplus, is_eq):
    assert lh
    assert rh

    elem = lh[idx]
    if isinstance(rh, tuple):
        disj = mp2df(rh, elem, 0, is_maxplus, is_eq)
    else:
        disj = "{} {} {}".format(rh, '==' if is_eq else '>=', elem)
    rest = lh[idx + 1:]

    if not rest:  # t <= max(x,y,z)
        return disj
    else:
        rest_disj = mp2df(lh, rh, idx + 1, is_maxplus, is_eq)

        op = '>=' if is_maxplus else '<='
        others = lh[:idx] + rest

        conds = ["{} {} {}".format(elem, op, t) for t in others]
        if len(conds) >= 2:
            cond = 'And({})'.format(', '.join(conds))
        else:
            cond = conds[0]

        return "If({}, {}, {})".format(cond, disj, rest_disj)


# def mp2df_l(lh, rh, idx, is_maxplus, is_eq):
#     assert lh
#     assert rh

#     elem = lh[idx]
#     disj = mp2df_r(rh, elem, 0, is_maxplus, is_eq)
#     rest = lh[idx + 1:]

#     if not rest:  # t <= max(x,y,z)
#         return disj
#     else:
#         rest_disj = mp2df_l(lh, rh, idx + 1, is_maxplus, is_eq)

#         op = '>=' if is_maxplus else '<='
#         others = lh[:idx] + rest

#         conds = ["{} {} {}".format(elem, op, t) for t in others]
#         if len(conds) >= 2:
#             cond = 'And({})'.format(', '.join(conds))
#         else:
#             cond = conds[0]

#         return "If({}, {}, {})".format(cond, disj, rest_disj)


# def mp2df_r(terms, term, idx, is_maxplus, is_eq):
#     assert terms

#     elem = terms[idx]
#     disj = "{} {} {}".format(term, '==' if is_eq else '>=', elem)
#     rest = terms[idx + 1:]

#     if not rest:  # t <= x ==>  t <= x
#         return disj
#     else:  # t <= max(x,y,z) ==> If(x>=y and x >= z, t <= x, ...)
#         rest_disj = mp2df_r(terms, term, idx + 1, is_maxplus, is_eq)

#         op = '>=' if is_maxplus else '<='
#         others = terms[:idx] + rest

#         conds = ["{} {} {}".format(elem, op, t) for t in others]
#         if len(conds) >= 2:
#             cond = 'And({})'.format(', '.join(conds))
#         else:
#             cond = conds[0]

#         return "If({}, {}, {})".format(cond, disj, rest_disj)


def get_lambda_str(lh, rh, is_maxplus=True, is_eq=False, is_formula=False):
    """
       Return lambda expression string
            lambda x, y, ... = max(x, y...) >= max(x, y...)

        sage: IeqMPP.get_lambda_exp(
            [x-10, y-3],[y,5], is_maxplus=True,is_formula=True,is_eq=False)
        'lambda x,y: max(x - 10,y - 3) - max(y,5) >= 0'

        sage: IeqMPP.get_lambda_exp(
            [x-10, y-3],[y,5], is_maxplus=True,is_formula=True,is_eq=False)
        'lambda x,y: max(x - 10,y - 3) - max(y,5) >= 0'

        sage: IeqMPP.get_lambda_exp(
            [x-10, y-3],[y,5], is_maxplus=True,is_formula=False,is_eq=False)
        'lambda x,y: max(x - 10,y - 3) - max(y,5)'

        sage: IeqMPP.get_lambda_exp(
            [x-10, y-3],[y], is_maxplus=True,is_formula=False,is_eq=False)
        'lambda x,y: max(x - 10,y - 3) - (y)'

        sage: IeqMPP.get_lambda_exp(
            [x-10, y-3],[y], is_maxplus=True,is_formula=False,is_eq=True)
        'lambda x,y: max(x - 10,y - 3) - (y)'

        sage: IeqMPP.get_lambda_exp(
            [x-10, y-3],[y], is_maxplus=True,is_formula=True,is_eq=True)
        'lambda x,y: max(x - 10,y - 3) - (y) == 0'

        sage: IeqMPP.get_lambda_exp(
            [x-10, y-3],[y+12], is_maxplus=False,is_formula=True,is_eq=True)
        'lambda x,y: min(x - 10,y - 3) - (y + 12) == 0'

        sage: IeqMPP.get_lambda_exp(
            [x-10, y-3],[y+12], is_maxplus=False,is_formula=True,is_eq=True)
        'lambda x,y: min(x - 10,y - 3) - (y + 12) == 0'
    """
    assert isinstance(lh, tuple) and lh, lh
    assert isinstance(rh, tuple) and rh, rh

    op = 'max' if is_maxplus else 'min'

    def f(ls):
        assert ls
        if len(ls) >= 2:
            return '{}({})'.format(op, ', '.join(map(str, ls)))
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

    symbols_str = ','.join(map(str, Miscs.getVars(lh + rh)))
    expr_str = "{} - {}".format(f(lh), f(rh))
    if is_formula:
        rel = '==' if is_eq else '>='
        expr_str = "{} {} 0".format(expr_str, rel)
    return "lambda {}: {}".format(symbols_str, expr_str)


def test_trace(lambda_str, trace):
    """
    Examples:

    sage: assert InvMPP.test_trace('lambda x,y: max(x - 13,-3) >= y', {'x': 11,'y':100}) == False

    sage: assert InvMPP.test_trace('lambda x,y: x+y == 5', {'x': 2,'y':3,'d':7})

    sage: assert InvMPP.test_trace('lambda x,y: x+y == 6', {'x': 2,'y':3,'d':7}) == False


    sage: assert InvMPP.test_trace('lambda x,y: x+y', {'x': 2,'y':3,'d':7}, is_formula=False) == 5


    sage: assert InvMPP.test_trace('lambda x,y: x+y == 10 or x + y == 5', {'x': 2,'y':3,'d':7})

    sage: assert InvMPP.test_trace('lambda x,y: x+y == 1 or x + y == 2', {'x': 2,'y':3,'d':7}) == False
    """
    assert isinstance(lambda_str, str) and 'lambda' in lambda_str

    f = sage.all.sage_eval(lambda_str)
    symbols = f.func_code.co_varnames
    # if trace has more keys than variables in lambda str then remove tehm
    trace = dict([(s, trace[s]) for s in symbols])
    rs = f(**trace)
    return rs


# def _get_terms_mp(ts):
#     """
#     Generate mpp terms of the form
#     max(c1+x1,...,cn+xn,c0) >= xi,
#     where ci are in cs (e.g., 0,-oo for max plus)

#     sage: var('x y z t s w')
#     (x, y, z, t, s, w)

#     sage: ts = _get_terms_mpp([x,y,z,t,s],[]); len(ts)
#     145

#     sage: ts = _get_terms_mpp([x,y,z],[]); ts; len(ts)
#     [([x, y, 0], z),
#     ([x, y], z),
#     ([x, z, 0], y),
#     ([x, z], y),
#     ([x, 0], y),
#     ([x, 0], z),
#     ([x], y),
#     ([x], z),
#     ([y, z, 0], x),
#     ([y, z], x),
#     ([y, 0], x),
#     ([y, 0], z),
#     ([y], z),
#     ([z, 0], x),
#     ([z, 0], y),
#     ([0], x),
#     ([0], y),
#     ([0], z)]
#     18


#     sage: ts = _get_terms_mpp([x,y,z],['z']); ts; len(ts)
#     [([x, y, 0], z),
#     ([x, y], z),
#     ([x, 0], z),
#     ([x], z),
#     ([y, 0], z),
#     ([y], z),
#     ([z, 0], x),
#     ([z, 0], y),
#     ([0], x),
#     ([0], y)]
#     10

#     sage: ts = _get_terms_mpp([x,y,z],['x','y']); ts; len(ts)
#     [([x, y, 0], z),
#     ([x, y], z),
#     ([x, 0], z),
#     ([x], z),
#     ([y, 0], z),
#     ([y], z),
#     ([z, 0], x),
#     ([z, 0], y),
#     ([0], z)]
#     9

#     sage: ts = _get_terms_mpp([x,y,z],['x','y','z']); len(ts)
#     0

#     sage: ts = _get_terms_mpp([x,y,z,w],[]); ts; len(ts)
#     [([x, y, z, 0], w),
#     ([x, y, z], w),
#     ([x, y, w, 0], z),
#     ([x, y, w], z),
#     ([x, y, 0], z),
#     ([x, y, 0], w),
#     ([x, y], z),
#     ([x, y], w),
#     ([x, z, w, 0], y),
#     ([x, z, w], y),
#     ([x, z, 0], y),
#     ([x, z, 0], w),
#     ([x, z], y),
#     ([x, z], w),
#     ([x, w, 0], y),
#     ([x, w, 0], z),
#     ([x, w], y),
#     ([x, w], z),
#     ([x, 0], y),
#     ([x, 0], z),
#     ([x, 0], w),
#     ([x], y),
#     ([x], z),
#     ([x], w),
#     ([y, z, w, 0], x),
#     ([y, z, w], x),
#     ([y, z, 0], x),
#     ([y, z, 0], w),
#     ([y, z], x),
#     ([y, z], w),
#     ([y, w, 0], x),
#     ([y, w, 0], z),
#     ([y, w], x),
#     ([y, w], z),
#     ([y, 0], x),
#     ([y, 0], z),
#     ([y, 0], w),
#     ([y], z),
#     ([y], w),
#     ([z, w, 0], x),
#     ([z, w, 0], y),
#     ([z, w], x),
#     ([z, w], y),
#     ([z, 0], x),
#     ([z, 0], y),
#     ([z, 0], w),
#     ([z], w),
#     ([w, 0], x),
#     ([w, 0], y),
#     ([w, 0], z),
#     ([0], x),
#     ([0], y),
#     ([0], z),
#     ([0], w)]
#     54


#     sage: ts = _get_terms_mpp([x,y,z,w],['z','w']); ts; len(ts)
#     [([x, y, 0], z),
#     ([x, y, 0], w),
#     ([x, y], z),
#     ([x, y], w),
#     ([x, 0], z),
#     ([x, 0], w),
#     ([x], z),
#     ([x], w),
#     ([y, 0], z),
#     ([y, 0], w),
#     ([y], z),
#     ([y], w),
#     ([z, w, 0], x),
#     ([z, w, 0], y),
#     ([z, w], x),
#     ([z, w], y),
#     ([z, 0], x),
#     ([z, 0], y),
#     ([w, 0], x),
#     ([w, 0], y),
#     ([0], x),
#     ([0], y)]
#     22

#     sage: ts = _get_terms_mpp([x,y,z,w],['x','y','z']); ts; len(ts)
#     [([x, y, z, 0], w),
#     ([x, y, z], w),
#     ([x, y, 0], w),
#     ([x, y], w),
#     ([x, z, 0], w),
#     ([x, z], w),
#     ([x, 0], w),
#     ([x], w),
#     ([y, z, 0], w),
#     ([y, z], w),
#     ([y, 0], w),
#     ([y], w),
#     ([z, 0], w),
#     ([z], w),
#     ([w, 0], x),
#     ([w, 0], y),
#     ([w, 0], z),
#     ([0], w)]
#     18


#     sage: ts = _get_terms_mpp([x,y],[]); ts; len(ts)
#     [([x, 0], y), ([x], y), ([y, 0], x), ([0], x), ([0], y)]
#     5
#     """
#     ts_ext = list(ts) + [0]
#     d = {}
#     rs = []
#     ccs = itertools.product(*([[0, oo]]*len(ts_ext)))
#     ccs = list(ccs)
#     for cs in ccs:
#         lh = [c+t for c, t in zip(ts_ext, cs) if t != oo]

#         # ignore oo >= x1 + c
#         if not lh:
#             continue

#         # ignore x >= x + c ~> 0 >= c
#         # ignore [y],x if [x],y already in
#         if len(lh) == 1:
#             l0 = lh[0]
#             ts_ = []

#             for t in ts:
#                 if l0 != t and (t, l0) not in d:
#                     ts_.append(t)
#                     d[(l0, t)] = None

#         else:
#             # ignore (lh, xi)  if xi in lh, e.g., [x,y,0] x
#             # this is because [x,y,0] x  is implied by [y,0] x
#             ts_ = [t for t in ts if t not in lh]

#         rs.extend([(lh, t) for t in ts_])

#     return rs


# class IeqMPPFixed(IeqMPP):
#     """
#     sage: var('y z')
#     (y, z)
#     sage: tcs = [{x:2,y:-8,z:-7},{x:-1,y:-15,z:88},{x:15,y:5,z:0}]
#     sage: ieq = IeqMPPFixed(terms=[x,y],tcs=tcs,xinfo={'Input':[],'Output':[]})
#     dig:Info:*** IeqMPPFixed ***
#     sage: ieq.solve()
#     dig_polynomials:Debug:Build (fixed max-plus) poly from 3 tcs (~ 10 facets)
#     sage: Inv.print_invs(ieq.sols)
#     0: -y + 5 >= 0, 0 >= y - 5
#     1: x + 1 >= 0, x + 1 >= 0
#     2: -x + 15 >= 0, 0 >= x - 15
#     3: x - y - 10 >= 0, x >= y + 10
#     4: -x + y + 14 >= 0, y + 14 >= x
#     5: y + 15 >= 0, y + 15 >= 0
#     6: max(x,0) - (y + 10) >= 0, If(x >= 0,x >= y + 10,0 >= y + 10)
#     7: x + 1 - max(y,0) >= 0, If(y >= 0, x + 1 >= y, x + 1 >= 0)
#     8: max(y,0) - (x - 10) >= 0, If(y >= 0,y >= x - 10,0 >= x - 10)
#     9: y + 15 - max(x,0) >= 0, If(x >= 0, y + 15 >= x, y + 15 >= 0)

#     sage: ieq = IeqMPPFixed(terms=[x,y,z],tcs=tcs,xinfo={'Input':[],'Output':[]})
#     dig:Info:*** IeqMPPFixed ***
#     sage: ieq.solve()
#     dig_polynomials:Debug:Build (fixed max-plus) poly from 3 tcs (~ 36 facets)
#     sage: Inv.print_invs(ieq.sols)
#     0: -y + 5 >= 0, 0 >= y - 5
#     1: x + 1 >= 0, x + 1 >= 0
#     2: -y + z + 5 >= 0, z + 5 >= y
#     3: z + 7 >= 0, z + 7 >= 0
#     4: -x + 15 >= 0, 0 >= x - 15
#     5: -z + 88 >= 0, 0 >= z - 88
#     6: x - y - 10 >= 0, x >= y + 10
#     7: x - z + 89 >= 0, x >= z - 89
#     8: -x + y + 14 >= 0, y + 14 >= x
#     9: y + 15 >= 0, y + 15 >= 0
#     10: -x + z + 15 >= 0, z + 15 >= x
#     11: y - z + 103 >= 0, y >= z - 103
#     12: max(z,0) - (y - 5) >= 0, If(z >= 0,z >= y - 5,0 >= y - 5)
#     13: max(x,0) - (y + 10) >= 0, If(x >= 0,x >= y + 10,0 >= y + 10)
#     14: max(x,0) - (z - 88) >= 0, If(x >= 0,x >= z - 88,0 >= z - 88)
#     15: max(x,y) - (z - 89) >= 0, If(x >= y,x >= z - 89,y >= z - 89)
#     16: max(x,z) - (y + 10) >= 0, If(x >= z,x >= y + 10,z >= y + 10)
#     17: x + 1 - max(y,0) >= 0, If(y >= 0, x + 1 >= y, x + 1 >= 0)
#     18: z + 7 - max(y,0) >= 0, If(y >= 0, z + 7 >= y, z + 7 >= 0)
#     19: max(y,0) - (x - 10) >= 0, If(y >= 0,y >= x - 10,0 >= x - 10)
#     20: max(y,0) - (z - 88) >= 0, If(y >= 0,y >= z - 88,0 >= z - 88)
#     21: max(y,z) - (x - 10) >= 0, If(y >= z,y >= x - 10,z >= x - 10)
#     22: max(z,0) - (x - 15) >= 0, If(z >= 0,z >= x - 15,0 >= x - 15)
#     23: y + 15 - max(x,0) >= 0, If(x >= 0, y + 15 >= x, y + 15 >= 0)
#     24: z + 15 - max(x,0) >= 0, If(x >= 0, z + 15 >= x, z + 15 >= 0)
#     25: z + 15 - max(x,y) >= 0, If(x >= y, z + 15 >= x, z + 15 >= y)
#     26: x + 89 - max(y,z) >= 0, If(y >= z, x + 89 >= y, x + 89 >= z)
#     27: x + 89 - max(z,0) >= 0, If(z >= 0, x + 89 >= z, x + 89 >= 0)
#     28: y + 103 - max(x,z) >= 0, If(x >= z, y + 103 >= x, y + 103 >= z)
#     29: y + 103 - max(z,0) >= 0, If(z >= 0, y + 103 >= z, y + 103 >= 0)
#     30: max(x,y,0) - (z - 88) >= 0, If(And(x >= y,x >= 0),x >= z - 88,If(And(y >= x,y >= 0),y >= z - 88,0 >= z - 88))
#     31: max(x,z,0) - (y + 10) >= 0, If(And(x >= z,x >= 0),x >= y + 10,If(And(z >= x,z >= 0),z >= y + 10,0 >= y + 10))
#     32: max(y,z,0) - (x - 10) >= 0, If(And(y >= z,y >= 0),y >= x - 10,If(And(z >= y,z >= 0),z >= x - 10,0 >= x - 10))
#     33: z + 15 - max(x,y,0) >= 0, If(And(x >= y,x >= 0), z + 15 >= x, If(And(y >= x,y >= 0), z + 15 >= y, z + 15 >= 0))
#     34: x + 89 - max(y,z,0) >= 0, If(And(y >= z,y >= 0), x + 89 >= y, If(And(z >= y,z >= 0), x + 89 >= z, x + 89 >= 0))
#     35: y + 103 - max(x,z,0) >= 0, If(And(x >= z,x >= 0), y + 103 >= x, If(And(z >= x,z >= 0), y + 103 >= z, y + 103 >= 0))


#     sage: ieq.subset_siz = 2
#     sage: ieq.solve()
#     dig_polynomials:Debug:Build (fixed max-plus) poly from 3 tcs (~ 24 facets)
#     sage: Inv.print_invs(ieq.sols)
#     0: -y + 5 >= 0, 0 >= y - 5
#     1: x + 1 >= 0, x + 1 >= 0
#     2: -y + z + 5 >= 0, z + 5 >= y
#     3: z + 7 >= 0, z + 7 >= 0
#     4: -x + 15 >= 0, 0 >= x - 15
#     5: -z + 88 >= 0, 0 >= z - 88
#     6: x - y - 10 >= 0, x >= y + 10
#     7: x - z + 89 >= 0, x >= z - 89
#     8: -x + y + 14 >= 0, y + 14 >= x
#     9: y + 15 >= 0, y + 15 >= 0
#     10: -x + z + 15 >= 0, z + 15 >= x
#     11: y - z + 103 >= 0, y >= z - 103
#     12: max(z,0) - (y - 5) >= 0, If(z >= 0,z >= y - 5,0 >= y - 5)
#     13: max(x,0) - (y + 10) >= 0, If(x >= 0,x >= y + 10,0 >= y + 10)
#     14: max(x,0) - (z - 88) >= 0, If(x >= 0,x >= z - 88,0 >= z - 88)
#     15: x + 1 - max(y,0) >= 0, If(y >= 0, x + 1 >= y, x + 1 >= 0)
#     16: z + 7 - max(y,0) >= 0, If(y >= 0, z + 7 >= y, z + 7 >= 0)
#     17: max(y,0) - (x - 10) >= 0, If(y >= 0,y >= x - 10,0 >= x - 10)
#     18: max(y,0) - (z - 88) >= 0, If(y >= 0,y >= z - 88,0 >= z - 88)
#     19: max(z,0) - (x - 15) >= 0, If(z >= 0,z >= x - 15,0 >= x - 15)
#     20: y + 15 - max(x,0) >= 0, If(x >= 0, y + 15 >= x, y + 15 >= 0)
#     21: z + 15 - max(x,0) >= 0, If(x >= 0, z + 15 >= x, z + 15 >= 0)
#     22: x + 89 - max(z,0) >= 0, If(z >= 0, x + 89 >= z, x + 89 >= 0)
#     23: y + 103 - max(z,0) >= 0, If(z >= 0, y + 103 >= z, y + 103 >= 0)


#     sage: tcs=[{x:8,y:8},{x:0,y:-15},{x:0,y:0},{x:1,y:1}]
#     sage: ieq = IeqMPPFixed(terms=[x,y],tcs=tcs,xinfo={'Input':[],'Output':[]})
#     dig:Info:*** IeqMPPFixed ***
#     sage: ieq.solve()
#     dig_polynomials:Debug:Build (fixed max-plus) poly from 4 tcs (~ 10 facets)
#     sage: ieq.refine()
#     sage: Inv.print_invs(ieq.sols)
#     0: max(y,0) - (x) == 0, If(y >= 0,y == x,0 == x)
#     1: x >= 0, x >= 0
#     2: x - y >= 0, x >= y
#     3: -x + 8 >= 0, 0 >= x - 8
#     4: -y + 8 >= 0, 0 >= y - 8
#     5: y + 15 >= 0, y + 15 >= 0
#     6: -x + y + 15 >= 0, y + 15 >= x
#     7: max(x,0) - (y) >= 0, If(x >= 0,x >= y,0 >= y)
#     8: y + 15 - max(x,0) >= 0, If(x >= 0, y + 15 >= x, y + 15 >= 0)
#     """

#     def __init__(self, terms, tcs, xinfo):
#         super(IeqMPPFixed, self).__init__(terms, tcs, xinfo)
#         self.mpp_opt = IeqMPP.opt_maxplus  # default
#         self.subset_siz = None

#     def solve(self):  # mpp fixed
#         ts = [t for t in self.terms if t != 1]

#         tcs = Miscs.keys_to_str(self.tcs)

#         if self.subset_siz is None:
#             subset_siz = len(ts)
#         else:
#             subset_siz = self.subset_siz

#         blacklist = []

#         ts_common = get_terms_fixed_coefs(ts, subset_siz=subset_siz,
#                                           blacklist=blacklist,
#                                           is_mpp=True)

#         if self.mpp_opt == IeqMPP.opt_max_then_min:
#             def wprocess(is_maxplus, Q):
#                 Q.put(IeqMPPFixed.build_poly(ts_common, tcs, is_maxplus))

#             Q = mp.Queue()
#             workers = [mp.Process(target=wprocess, args=(is_maxplus, Q))
#                        for is_maxplus in [True, False]]

#             for w in workers:
#                 w.start()
#             rs = []
#             for _ in workers:
#                 rs.extend(Q.get())

#         else:
#             is_maxplus = self.mpp_opt == IeqMPP.opt_maxplus
#             rs = IeqMPPFixed.build_poly(ts_common, tcs, is_maxplus)

#         self.sols = map(InvMPP, rs)

#     #### Helpers for IeqMPPFixed ####
#     @staticmethod
#     def build_poly(ts, tcs, is_maxplus):
#         mpp_str = 'max-plus' if is_maxplus else 'min-plus'

#         logger.debug('Build (fixed {}) poly from {} tcs '
#                      '(~ {} facets)'
#                      .format(mpp_str, len(tcs), 2*len(ts)))

#         # Can be done in parallel
#         rs = []
#         for (lh, rh) in ts:
#             #lh - rh
#             r_lambda = IeqMPP.get_lambda_exp(lh, [rh], is_maxplus,
#                                              is_formula=False, is_eq=False)
#             r_evals = [InvMPP.test_trace(r_lambda, tc, is_formula=False)
#                        for tc in tcs]

#             # since Z3 doen't like numbers like 7/5
#             def to_numeric(c): return c.n() if '/' in str(c) else c
#             c_min = to_numeric(min(r_evals))  # lh >= rh + c_min
#             c_max = to_numeric(max(r_evals))  # rh +c_max >= lh

#             if c_min == c_max:  # lh == rh + cmin
#                 r_e = IeqMPP.get_lambda_disj(lh, [rh+c_min],
#                                              is_maxplus,
#                                              is_eq=True)
#                 rs.append(r_e)
#             else:
#                 r_u = IeqMPP.get_lambda_disj(lh, [rh+c_min],
#                                              is_maxplus,
#                                              is_eq=False)
#                 r_l = IeqMPP.get_lambda_disj([rh+c_max], lh,
#                                              is_maxplus,
#                                              is_eq=False)
#                 rs.extend([r_u, r_l])

#         return rs


# class IeqMPP(Ieq):
#     __metaclass__ = ABCMeta

#     opt_maxplus = 0
#     opt_min_plus = 1
#     opt_max_then_min = 2

#     # utils for MPP

#     @staticmethod
#     def get_lambda_disj(lh, rh, is_maxplus, is_eq):
#         """
#         shortcut that creates lambda expr and disj formula
#         """
#         r_lambda = IeqMPP.get_lambda_exp(lh, rh,
#                                          is_maxplus, is_formula=True,
#                                          is_eq=is_eq)
#         r_disj = IeqMPP.get_disj_exp(lh, rh, is_maxplus, is_eq)
#         return (r_lambda, r_disj)

#     @staticmethod
#     def get_lambda_exp(ls, rs, is_maxplus, is_formula, is_eq):
#         """
#         Return lambda expression
#         lambda x,y, ...  =  max(x,y...) >= max(x,y...)

#         Examples:

#         sage: var('y')
#         y

#         sage: IeqMPP.get_lambda_exp([x-10,y-3],[y,5], is_maxplus=True,is_formula=True,is_eq=False)
#         'lambda x,y: max(x - 10,y - 3) - max(y,5) >= 0'
#         sage: IeqMPP.get_lambda_exp([x-10,y-3],[y,5], is_maxplus=True,is_formula=True,is_eq=False)
#         'lambda x,y: max(x - 10,y - 3) - max(y,5) >= 0'
#         sage: IeqMPP.get_lambda_exp([x-10,y-3],[y,5], is_maxplus=True,is_formula=False,is_eq=False)
#         'lambda x,y: max(x - 10,y - 3) - max(y,5)'
#         bsage: IeqMPP.get_lambda_exp([x-10,y-3],[y], is_maxplus=True,is_formula=False,is_eq=False)
#         'lambda x,y: max(x - 10,y - 3) - (y)'
#         sage: IeqMPP.get_lambda_exp([x-10,y-3],[y], is_maxplus=True,is_formula=False,is_eq=True)
#         'lambda x,y: max(x - 10,y - 3) - (y)'
#         sage: IeqMPP.get_lambda_exp([x-10,y-3],[y], is_maxplus=True,is_formula=True,is_eq=True)
#         'lambda x,y: max(x - 10,y - 3) - (y) == 0'
#         sage: IeqMPP.get_lambda_exp([x-10,y-3],[y+12], is_maxplus=False,is_formula=True,is_eq=True)
#         'lambda x,y: min(x - 10,y - 3) - (y + 12) == 0'
#         sage: IeqMPP.get_lambda_exp([x-10,y-3],[y+12], is_maxplus=False,is_formula=True,is_eq=True)
#         'lambda x,y: min(x - 10,y - 3) - (y + 12) == 0'

#         """

#         if __debug__:
#             assert is_list(ls) and ls, ls
#             assert is_list(rs) and rs, rs

#         op = 'max' if is_maxplus else 'min'

#         str_op = (lambda s: '{}({})'
#                   .format(op, ','.join(map(str, s)))
#                   if len(s) >= 2 else s[0])

#         if len(rs) == 1:

#             if len(ls) == 1:  # (x+3,y+8),  (3,8), (3,y)
#                 ss = ls[0] - rs[0]

#             else:  # len(ls) >= 2
#                 rss = rs[0]
#                 lss = str_op(ls)
#                 if rss.is_zero():
#                     ss = lss
#                 else:
#                     if rss.operator is None:  # x,,y7
#                         ss = '{} - {}'.format(lss, rss)
#                     else:  # x + 3,  y - 3
#                         ss = '{} - ({})'.format(lss, rss)
#         else:  # len(rs) >= 2:
#             ss = '{} - {}'.format(str_op(ls), str_op(rs))

#         ss = ('lambda {}: {}{}'
#               .format(','.join(map(str, get_vars(ls+rs))), ss,
#                       ' {} 0'.format('==' if is_eq else '>=')
#                       if is_formula else ''))
#         return ss

#     @staticmethod
#     def get_disj_exp(ls, rs, is_maxplus, is_eq):
#         """
#         Return disjunctive format

#         Examples:

#         sage: var('y')
#         y

#         sage: IeqMPP.get_disj_exp([x-10,y-3],[y+12], is_maxplus=True,is_eq=True)
#         'If(x - 10 >= y - 3,x - 10 == y + 12,y - 3 == y + 12)'

#         sage: IeqMPP.get_disj_exp([x-10,y-3],[y+12], is_maxplus=True,is_eq=False)
#         'If(x - 10 >= y - 3,x - 10 >= y + 12,y - 3 >= y + 12)'

#         sage: IeqMPP.get_disj_exp([x-10,y-3],[y+12], is_maxplus=False,is_eq=False)
#         'If(x - 10 <= y - 3,x - 10 >= y + 12,y - 3 >= y + 12)'

#         sage: IeqMPP.get_disj_exp([x-10,y-3],[y+12], is_maxplus=False,is_eq=False)
#         'If(x - 10 <= y - 3,x - 10 >= y + 12,y - 3 >= y + 12)'

#         sage: IeqMPP.get_disj_exp([x-10,y-3],[y,12], is_maxplus=False,is_eq=False)
#         'If(x - 10 <= y - 3,If(y <= 12, x - 10 >= y, x - 10 >= 12),If(y <= 12, y - 3 >= y, y - 3 >= 12))'

#         sage: IeqMPP.get_disj_exp([x-10,y-3],[y,12], is_maxplus=False,is_eq=True)
#         'If(x - 10 <= y - 3,If(y <= 12, x - 10 == y, x - 10 == 12),If(y <= 12, y - 3 == y, y - 3 == 12))'
#         """

#         if not is_list(ls):
#             ls = [ls]
#         if not is_list(rs):
#             rs = [rs]

#         return IeqMPP.l_mp2df(ls, rs, is_maxplus, 0, is_eq)


# def l_mp2df(ls, rs, is_maxplus, idx, is_eq):
#     if __debug__:
#         assert not is_empty(ls), ls
#         assert not is_empty(rs), rs
#         assert idx >= 0, idx
#         assert is_bool(is_maxplus), is_maxplus

#     ls_ = ls[idx:]

#     if __debug__:
#         assert ls_, ls_

#     first_elem = ls_[0]
#     first_elem_f = IeqMPP.r_mp2df(first_elem, rs, is_maxplus, 0, is_eq)

#     if len(ls_) == 1:  # t <= max(x,y,z)
#         return first_elem_f
#     else:
#         op = ">=" if is_maxplus else "<="
#         rest_f = IeqMPP.l_mp2df(ls, rs, is_maxplus, idx+1, is_eq)

#         others = ls[:idx]+ls[idx+1:]
#         csts = ','.join('{} {} {}'.format(first_elem, op, t)
#                         for t in others)
#         cond = ("And({})" if len(others) >= 2 else "{}").format(csts)
#         return "If({},{},{})".format(cond, first_elem_f, rest_f)

#     @staticmethod
#     def r_mp2df(t, rs, is_maxplus, idx, is_eq):
#         """
#         Convert max/min-plus format to disjunctive formula
#         Inputs:
#         t = single term
#         rs = list of terms
#         idx = operate over rs[idx:]
#         """
#         if __debug__:
#             assert not is_empty(rs)
#             assert idx >= 0, idx
#             assert is_bool(is_maxplus), is_maxplus

#         rs_ = rs[idx:]

#         if __debug__:
#             assert not is_empty(rs_)

#         first_elem = rs_[0]
#         first_elem_f = ("{} {} {}"
#                         .format(t, '==' if is_eq else '>=', first_elem))

#         if len(rs_) == 1:  # t <= x ==> t <= x
#             return first_elem_f

#         else:  # t <= max(x,y,z) ==> If(x>=y and x >= z, t <= x, ...)
#             op = ">=" if is_maxplus else "<="
#             rest_f = IeqMPP.r_mp2df(t, rs, is_maxplus, idx+1, is_eq)

#             others = rs[:idx]+rs[idx+1:]
#             csts = ','.join('{} {} {}'.
#                             format(first_elem, op, t) for t in others)
#             cond = ('And({})' if len(others) >= 2 else '{}').format(csts)
#             return "If({}, {}, {})".format(cond, first_elem_f, rest_f)


 ((y, x), z),
 ((y, x, 0), z),
 ((z, x), y),
 ((z, x, 0), y),
 ((z, y), x),
 ((z, y, 0), x)]


[([x, y, 0], z),
 ([x, y], z),
 ([x, z, 0], y),
 ([x, z], y),
 ([y, z, 0], x),
 ([y, z], x),



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

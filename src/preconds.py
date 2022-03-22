import pdb
from pathlib import Path
from typing import Union, List
import json
import z3

import settings
from helpers.miscs import Miscs
from helpers.z3utils import Z3
from data.symstates import SymStates

IUPPER = 10
DBG = pdb.set_trace


def mysimplify(expr):
    return z3.Tactic('ctx-solver-simplify')(expr)[0]


def approx_term(f, term) -> Union[None, z3.ExprRef]:
    assert z3.is_expr(f), f

    v, stat = SymStates.mmaximize(f, term, iupper=IUPPER)
    if v is not None:
        assert isinstance(v, int), v
        f_approx = term <= v
        #print(f, f_approx)
        return f_approx
    return None

def approx_terms(f, terms) -> List:
    approxs = [approx_term(f, t) for t in terms]
    approxs = [a for a in approxs if a is not None]
    # print(f)
    # print(approxs)
    #ret = Z3._and(approxs)
    #return ret
    return approxs


def myimply(f: z3.ExprRef, ors: List[z3.ExprRef]) -> z3.ExprRef:
    assert z3.is_expr(f), f
    assert isinstance(ors, list) and all(z3.is_expr(x) for x in ors) and ors, ors

    ors_ = []
    for x in ors:
        ret = Z3.is_valid(z3.Implies(f, x))
        if not ret:
            ors_.append(x)

    ors_ = Z3._or(ors_)
    if ors_ is None: 
        ret = f 
    else:
        ret = z3.simplify(z3.And(f, ors_))
    return ret


def combine(ys: List[z3.ExprRef], ns: List[z3.ExprRef]):

    commons = set()
    for y in ys:
        for n in ns:
            if Z3.is_valid(y == n):
                commons.add(y)

    if commons:
        ys = [y for y in ys if y not in commons]
        ns = [n for n in ns if n not in commons]
        c = z3.simplify(Z3._and(list(commons)))
    else:
        c = Z3.zTrue

    if not ys and not ns:
        y = Z3.zTrue
        n = Z3.zTrue
    elif ys and not ns:
        y = Z3._and(ys)
        n = z3.Not(y)
    elif not ys and ns:
        n = Z3._and(ns)
        y = z3.Not(n)
    else:
        assert ys and ns, (ys, ns)
        ys_: z3.ExprRef = Z3._and(ys)
        ns_: z3.ExprRef = Z3._and(ns)

        y = myimply(ys_, [z3.Not(x) for x in ns])
        n = myimply(ns_, [z3.Not(x) for x in ys])
    
    y = z3.simplify(y)
    n = z3.simplify(n)
    return c, y, n
    
        
def check(f:z3.ExprRef, ss:z3.ExprRef) -> bool:
    claim = z3.Not(z3.Implies(f, ss)) #f is an underapprox of ss
    models, stat = Z3.get_models(f, k=2)
    cexs, is_succ = Z3.extract(models, int)
    print(stat,is_succ)
    print(cexs)
    DBG()

def precond(f_y, f_n, inputs):
    assert z3.is_expr(f_y), f_y
    assert z3.is_expr(f_n), f_n
    assert isinstance(inputs, list), inputs

    terms = Miscs.get_terms_fixed_coefs(inputs, 2, settings.ICOEFS)
    f_y_approx: List[z3.ExprRef] = approx_terms(f_y, terms)
    f_n_approx: List[z3.ExprRef] = approx_terms(f_n, terms)
    c,y,n = combine(f_y_approx, f_n_approx)  
    print(f"c: {c}; y: {y}; n: {n}")
    #check(y, f_y)
    check(n, f_n)
    # print("result f_n_", f_n_)
    return c,y, n


def go(filename):
    data = filename.read_text()
    data = json.loads(data)
    inps = data["inps"]
    inps = [z3.Int(inp) for inp in inps]
    ss = data["ss"]
    for loc in ss:
        ss_ = [Z3.from_smt2_str(ss[loc][depth]) for depth in ss[loc]]
        ss[loc] = z3.simplify(z3.Or(ss_))
    
    for loc in ss:
        if '_else' in loc:
            continue
        if 'pc0' not in loc:
            continue
        f_y = ss[loc]
        f_n = ss[f"{loc}_else"]
        print(f"- analyzing preconds reaching '{loc}'")
        precond(f_y, f_n, inps)

#go(Path('ss_json/pldi09_fig2.json'))
go(Path('ss_json/ex7.json'))


# ex1
# f_y = z3.Int('x') * z3.Int('x') > 100
# f_n = z3.Not(f_y)

# ex2
#f_y = z3.And(z3.Int('x') * z3.Int('x') > 100, z3.Int('y') > 5)
#f_n = z3.And(z3.Int('x') * z3.Int('x') <= 100, z3.Int('y') > 5)

# ix = z3.Int("x")
# iy = z3.Int("y")
# inputs = [ix, iy]
# precond(f_y, f_n, inputs)

#print(Z3.to_smt2_str(ix))
#print(Z3.to_smt2_str(iy))
#print(Z3.to_smt2_str(f_y))
#print(Z3.to_smt2_str(f_n))

"""
a & (b || c)
"""


""" def test():
    x = z3.Int('x')
    y = z3.Int('y')
    a = x >= 10
    b = x >= 5
    c = y >= 1

    f = z3.And(a,z3.Or(b,c))
    z3.prove(f == a)
    print(mysimplify(f))

test() """
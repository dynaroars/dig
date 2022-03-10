import pdb
import z3
from typing import Union

import settings
from helpers.miscs import Miscs
from helpers.z3utils import Z3
from data.symstates import SymStates

DBG = pdb.set_trace

def approx_term(f, term):
    assert z3.is_expr(f), f    
    v, stat = SymStates.mmaximize(f, term, iupper=100)
    if v is not None:
        assert isinstance(v, int), v
        f_approx = term <= v
        print(f, f_approx)
        return f_approx
    return None

def approx_terms(f, terms):
    approxs = [approx_term(f, t) for t in terms]
    ret = Z3._and(approxs)
    return ret

def approx(f_y, f_n, terms)->Union[None, z3.ExprRef]:
    f_y_approx = approx_terms(f_y, terms)
    f_n_approx = approx_terms(f_n, terms)
    
    if f_y_approx is not None and f_n_approx is not None:
        f_y_ = z3.simplify(z3.And(f_y_approx, z3.Not(f_n_approx)))
        f_n_ = z3.simplify(z3.And(f_n_approx, z3.Not(f_y_approx)))
    elif f_y_approx is not None and f_n_approx is None:
        f_y_ = z3.simplify(f_y_approx)
        f_n_ = z3.simplify(z3.Not(f_y_approx))
    elif f_y_approx is None and f_n_approx is not None:
        f_y_ = z3.simplify(z3.Not(f_n_approx))
        f_n_ = z3.simplify(f_n_approx)
    else:
        assert f_y_approx is None and f_n_approx is None
        f_y_ = None
        f_n_ = None
    
    return f_y_, f_n_ 

def precond(f_y, f_n, inputs):
    assert z3.is_expr(f_y)
    assert z3.is_expr(f_n)

    terms = Miscs.get_terms_fixed_coefs(inputs, 1, settings.ICOEFS)
    print(terms)                
    f_y_, f_n_ = approx(f_y, f_n, terms)
    print("result f_y_", f_y_)
    print("result f_n_", f_n_)
    return f_y_, f_n_


def go(filename):
    data = filename.read_text()
    inps = data["inps"]
    ss = data["ss"]


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
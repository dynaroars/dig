import pdb
import z3
from data.symstates import SymStates
DBG = pdb.set_trace

def overapprox(f, term):
    assert z3.is_expr(f), f    
    v, stat = SymStates.mmaximize(f, term, iupper=100)
    if v is not None:
        assert isinstance(v, int), v
        f_approx = term <= v
        print(f, f_approx)
        return f_approx
    return z3.BoolVal("True")

def precond(f_y, f_n):
    assert z3.is_expr(f_y)
    assert z3.is_expr(f_n)

    terms = [z3.Int('x'), -1*z3.Int('x')]

    f_y_approxs = []
    f_n_approxs = []
    for t in terms:
        f_y_approxs.append(overapprox(f_y, t))
        f_n_approxs.append(overapprox(f_n, t))

    f_y_approx = z3.And(*f_y_approxs)
    f_n_approx = z3.And(*f_n_approxs)

    approx = z3.simplify(z3.And(f_y_approx, z3.Not(f_n_approx)))
    print("result", approx)
    return approx


f_y = z3.Int('x') * z3.Int('x') > 100
f_n = z3.Not(f_y)

precond(f_y, f_n)
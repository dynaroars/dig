import z3

def overapprox(f):
    assert z3.is_expr(f_y)
    pass

def precond(f_y, f_n):
    assert z3.is_expr(f_y)
    assert z3.is_expr(f_n)

    f_y_approx = f_y
    f_n_approx = f_n

    return z3.And(f_y_approx, f_n_approx)


f_y = z3.Int('x') * z3.Int('x') > 100
f_n = z3.Not(f_y)

precond(f_y, f_n)
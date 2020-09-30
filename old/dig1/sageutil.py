from collections import OrderedDict
from sage.all import (operator, flatten, PolynomialRing, SR, QQ, ZZ, RR, sage, oo)
from vu_common import (pause, get_logger,is_iterable, is_str, is_empty) 
                       
is_sage_expr = lambda x: isinstance(x, sage.symbolic.expression.Expression)
is_sage_real = lambda x: isinstance(x, sage.rings.real_mpfr.RealLiteral)
is_sage_int = lambda x: isinstance(x, sage.rings.integer.Integer)
is_sage_num = lambda x: is_sage_real(x) or is_sage_int(x)
def is_sage_inf(x):
    """
    Example:
    sage: is_sage_inf(oo)
    True
    sage: is_sage_inf(-oo)
    True
    sage: is_sage_inf(oo+3)
    True
    sage: is_sage_inf(oo-3)
    True
    sage: is_sage_inf(SR(-oo))
    True
    sage: is_sage_inf(x)
    False
    sage: is_sage_inf(x+3)
    False
    sage: is_sage_inf(8)
    False
    """
    try:
        return x.is_infinity()
    except AttributeError:
        return x == oo or x == -oo

is_sage_int_inf = lambda x: is_sage_int(x) or is_sage_inf(x)
to_sage_int = lambda x: x if is_sage_int(x) else ZZ(x)


def is_sage_symbol(s):
    """
    sage: assert is_sage_symbol(x)
    sage: assert not is_sage_symbol(x+1)
    sage: assert not is_sage_symbol(1)
    """
    try:
        return s.is_symbol()
    except AttributeError:
        return False

def is_sage_rel(f, rel=None):
    """
    sage: assert not is_sage_rel(7.2)
    sage: assert not is_sage_rel(x)
    sage: assert not is_sage_rel(x+7)
    sage: assert is_sage_rel(x==3,operator.eq)

    sage: assert is_sage_rel(x<=3,operator.le)
    sage: assert not is_sage_rel(x<=3,operator.lt)
    sage: assert not is_sage_rel(x+3,operator.lt)

    sage: y = var('y')
    sage: assert is_sage_rel(x+y<=3)
    """

    try:
        if not f.is_relational(): 
            return False

        if rel is None:
            return True
        else:
            return f.operator() == rel

    except AttributeError:
        return False
        
is_sage_eq = lambda f: is_sage_rel(f, operator.eq)

def get_vars(ps):
    """
    Returns a list of uniq variables from a list of properties

    Examples:

    sage: var('a b c x')
    (a, b, c, x)

    sage: assert [a, b, c, x] == get_vars([x^(a*b) + a**2+b+2==0, c**2-b==100, b**2 + c**2 + a**3>= 1])
    sage: assert get_vars(a**2+b+5*c+2==0) == [a, b, c]
    sage: assert get_vars(x+x^2) == [x]
    sage: assert get_vars([3]) == []
    sage: assert get_vars((3,'x + c',x+b)) == [b, x]
    """

    ps = ps if is_iterable(ps) else [ps]

    vs = flatten([p.variables() for p in ps if is_sage_expr(p)])

    return sorted(set(vs), key=str)


def get_coefs_terms(p, base_ring = QQ, as_dict=False):
    """
    Returns the Coefs and Terms of a given expression

    Examples:
    sage: assert get_coefs_terms(x) == ([1], [x])

    sage: assert get_coefs_terms(x,as_dict=True) == {x: 1}

    sage: var('a b c')
    (a, b, c)

    sage: assert get_coefs_terms(a**2+b+5*c+2==0) == ([1, 1, 5, 2], [a^2, b, c, 1])
    sage: assert get_coefs_terms(a**2+b+5*c+2==0, as_dict=True) == {b: 1, 1: 2, a^2: 1, c: 5}

    sage: assert get_coefs_terms(10/3*a**2+3*b+5*c+2) == ([10/3, 3, 5, 2], [a^2, b, c, 1])
    sage: assert get_coefs_terms(10/3*a**2+3*b+5*c+2, as_dict=True) == {b: 3, 1: 2, a^2: 10/3, c: 5}

    sage: assert get_coefs_terms(a+b<=3, as_dict=True) == {1: -3, b: 1, a: 1}
    sage: assert all(is_sage_int(v) for v in get_coefs_terms(a+b<=3, as_dict=True, base_ring=ZZ).values())

    #sage 6.2 breaks this
    #sage: assert get_coefs_terms(a - b <= oo) == ([1, -1, -infinity], [a, b, 1])

    sage: assert get_coefs_terms(SR(7), as_dict=True) == {1: 7}
    sage: assert get_coefs_terms(SR(3))==([3], [1])
    sage: assert get_coefs_terms(SR(oo))==([+Infinity], [1])
    sage: assert get_coefs_terms(SR(-oo)) ==  ([-Infinity], [1])
    sage: assert get_coefs_terms(a + b <= .9,base_ring=ZZ) == ([1, 1, -0.900000000000000], [a, b, 1])
    
    sage: assert is_sage_int(get_coefs_terms(SR(7),base_ring=ZZ,as_dict=True).values()[0])

    """

    use_wrong_base_ring = False

    if is_sage_rel(p):
        p = mk_rhs_0(p).lhs()

    if p.is_integer() or p.is_real():
        ts = [SR(1)]
        cs = [p if p.is_infinity() else base_ring(p)]

    else:
        ss = get_vars(p)
        assert not is_empty(ss), (p,ss)

        mk_pr = lambda b, p: PolynomialRing(b, ss, None if len(ss) >= 2 else 1)(p)

        try:
            pr_p = mk_pr(base_ring, p)
        except TypeError:
            
            if base_ring == RR:
                #if cannot do over RR then return None
                return None  
            else:
                #otherwise, try with RR
                try:
                    pr_p = mk_pr(RR,p)
                    use_wrong_base_ring = True
                except Exception as msg:
                    return None
        
        cs = pr_p.coefficients()
        ts = map(SR, pr_p.monomials())


        if use_wrong_base_ring:
            ts = [SR(1) if bool(t.is_one()) else t for t in ts]
            cs_ = []
            for c in cs:
                if c == oo:
                    cs_.append(oo)
                elif c == -oo:
                    cs_.append(-oo)
                else:
                    try:
                        cs_.append(base_ring(c))
                    except ValueError:
                        cs_.append(c)
                    except TypeError:
                        cs_.append(c)
            cs = cs_
        
        assert all(is_sage_expr(t) for t in ts), ts

    if as_dict:
        d = OrderedDict()
        for t,c in zip(ts,cs):
            d[t] = c
        return d
    else:
        return cs,ts


def mk_rhs_0(p):
    """
    sage: var('x,y')
    (x, y)
    sage: mk_rhs_0(x - y  >= 3)
    x - y - 3 >= 0

    sage: mk_rhs_0(x - y  - 3 >= 0)
    x - y - 3 >= 0


    sage: mk_rhs_0(0 <= x - y - 3)
    -x + y + 3 <= 0

    sage: mk_rhs_0(0 == x)
    -x == 0

    sage: mk_rhs_0(10 == -x)
    x + 10 == 0

    #Sage 5.11 broke all these (i.e., broke lhs.add(..,hold=))
    # sage: mk_rhs_0(x <= oo)
    # x - Infinity <= 0

    # sage: mk_rhs_0(x <= -oo)
    # x + +Infinity <= 0

    # sage: mk_rhs_0(x >= oo)
    # x - Infinity >= 0

    # sage: mk_rhs_0(oo >= x)
    # +Infinity - x >= 0

    sage: mk_rhs_0(x - y - 3)
    Traceback (most recent call last):
    ...
    AssertionError: x - y - 3


    """
    assert is_sage_rel(p), p

    rhs = p.rhs()
    lhs = p.lhs()
    if not rhs.is_zero():
        lhs = lhs.add(-rhs, hold=(rhs.is_infinity() or lhs.is_infinity()))
        rhs = 0
        p = p.operator()(lhs, rhs)

    return p


# def myreduce(op, ls):
#     """
#     Apply operator op to list of arguments

#     Note, it seems the above arguments are *enough*, no need to implement for (-,div) etc because the function that calls this will break  x - y to myreduce(op,[x,-y]) or  x / y to myreduce(op,[x,1/y]) and 1/y =>  mul(1,y^{-1})

#     sage: assert myreduce(operator.add, [x,x]) == 2*x
#     sage: assert myreduce(operator.add, [3,x]) == x + 3
#     sage: myreduce(operator.le, [3,x])
#     3 <= x
#     sage: assert myreduce(operator.pow,[3,x]) == 3^x


#     """
#     if __debug__:
#         assert len(ls) >= 2, ls
#         assert op in [operator.add,operator.mul,
#                       operator.pow,operator.eq,operator.ne,
#                       operator.le,operator.lt,operator.ge,operator.gt], op
#     return reduce(lambda a, b: op(a,b), ls[1:], ls[0])



# def mk_expr(expr, d, ring_typ=ZZ):
#     """
#     Make a new expression like expr but with all vars in expr replaced
#     with those in dictionary d. Used when subs() is not applicable
#     sage: y = var('y')

#     sage: lp = MixedIntegerLinearProgram()
#     sage: s0 = lp['s0']
#     sage: s1 = lp['s1']
#     sage: d = {x:s0,y:s1}
#     sage: mk_expr(x+y+3, d)
#     3 + x_0 + x_1
#     sage: mk_expr(x+y+3<=8,d)
#     3 + x_0 + x_1 <= 8
#     sage: mk_expr(x==y+5,d)
#     x_0 == 5 + x_1
#     """
#     def retval(expr):
#         if is_sage_symbol(expr):  #symbol, e.g. x
#             return d[expr]
#         else: #const , e.g. 3
#             return ring_typ(expr)
#     try:
#         oprs = expr.operands()
#     except AttributeError:
#         #e.g. const 3, .5
#         return retval(expr)

#     if is_empty(oprs): #symbol
#         return retval(expr)
#     else:
#         oprs = [mk_expr(o,d) for o in oprs]
#         print oprs
#         rs = myreduce(expr.operator(), oprs)
#         return rs



if __name__ == "__main__":
    import doctest
    doctest.testmod()

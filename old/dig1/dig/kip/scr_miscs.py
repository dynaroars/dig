###########################################
# Miscellaneous / Helpers methods related
# to SCR
#
# Author: ThanhVu (Vu) Nguyen
############################################


"""
This file consists of helper methods specific to SCR semantics.

IMPORTANT: SCR has the next variable, e.g.  v' whereas I use the
pre variable.  So an SCR expression  v and not(v')  is equivalent
to my notation  pre(v) and v   .
"""

from vu_common import is_list
from z3util import mk_var, get_vars, is_expr_var, fhash, myOr, myAnd
from z3 import is_expr, substitute, Not
#from z3 import *


pre_kw = '_pre'
pre_vars_dict = {}
cur_vars_dict = {}



def pre(v):
    """
    Return a new variable of the same sort as v called v_pre

    >>> from z3 import *
    >>> x = Bool('x')
    >>> pre(x)
    x_pre

    """

    if __debug__:
        assert is_expr_var(v) and not is_pre(v), v

    key_v = fhash(v)
    try:
        pre_v = pre_vars_dict[key_v]
    except KeyError:
        pre_v = mk_var(str(v) + pre_kw, v.sort())
        pre_vars_dict[key_v] = pre_v

        cur_vars_dict[fhash(pre_v)] = v


    assert pre_v.sort().kind() == v.sort().kind(), \
        'perhaps pre_vars_dict needs reset ?'

    return pre_v



def is_pre(v):
    """
    Return if the variable v is a pre variable,
    i.e. if v ends with pre_kw
    """
    return str(v).endswith(pre_kw)



def is_pre_f(f):
    """
    Check if all variables in f are pre variables

    Examples:

    >>> from z3 import *
    >>> x,y = Ints('x y')
    >>> is_pre_f(x)
    False
    >>> is_pre_f(pre(x))
    True
    >>> is_pre_f(Or(pre(x)==10, y==3))
    False
    >>> is_pre_f(Or(pre(x)==10, pre(y)==3))
    True
    """
    if __debug__:
        assert is_expr(f),f

    return all(is_pre(v) for v in get_vars(f))



def pre_f(f):
    """
    Convert a formula f with cur vars to a formula with pre vars

    >>> from z3 import *
    >>> x,y,z = Ints('x y z')

    >>> pre_f(z == 9)
    z_pre == 9

    >>> pre_f(And(y == 4, z == 9) )
    And(y_pre == 4, z_pre == 9)

    """
    if __debug__:
        assert f is None or is_cur_f(f), f

    if f is None:
        return None
    elif is_expr_var(f):
        return pre(f)
    else:
        vss = [(v, pre(v)) for v in get_vars(f)]
        return substitute(f, *vss)



def cur(v):
    """
    Given a pre variable v, return the non-pre version of.
    For example, if v  =  myvar_pre, then cur(v) gives myvar
    """
    if __debug__:
        assert is_expr_var(v) and is_pre(v), v

    return cur_vars_dict[fhash(v)]


def is_cur_f(f):
    """
    Check if all variables in f are cur (not pre)

    Examples:

    >>> from z3 import *
    >>> x,y = Ints('x y')
    >>> is_cur_f(x)
    True
    >>> is_cur_f(pre(x))
    False
    >>> is_cur_f(Or(x==10, y==3))
    True
    >>> is_cur_f(Or(pre(x)==10, y==3))
    False
    >>> is_cur_f(Or(pre(x)==10, pre(y)==3))
    False
    """
    if __debug__:
        assert is_expr(f),f

    return all(not is_pre(v) for v in get_vars(f))




def cur_f(f):
    """
    Convert a formula f with pre vars to a formula with cur vars

    >>> from z3 import *
    >>> x,y,z = Ints('x y z')

    >>> cur_f(pre(z) == 9)
    z == 9

    >>> cur_f(And(pre(y) == 4, pre(z) == 9) )
    And(y == 4, z == 9)

    >>> cur_f(pre(y) == z)
    Traceback (most recent call last):
    ...
    AssertionError: y_pre == z
    """
    if __debug__:
        assert f is None or is_pre_f(f), f

    if f is None:
        return None
    if is_expr_var(f):
        return cur(f)
    else:
        vss = [(v, cur(v)) for v in get_vars(f)]
        return substitute(f, *vss)


def is_trans(f):
    """
    Check if f has some pre variables

    Examples:

    >>> from z3 import *
    >>> x,y = Ints('x y')
    >>> is_trans(x)
    False
    >>> is_trans(x+y==10)
    False
    >>> is_trans(Implies(x==10,y==0))
    False
    >>> is_trans(And(x==y,y==4))
    False
    >>> is_trans(IntVal(3))
    False
    >>> is_trans(3)
    Traceback (most recent call last):
    ...
    AssertionError: 3
    """

    if __debug__:
        assert is_expr(f),f

    return pre_kw in str(f)


def is_state(f):
    """
    Check if f has no pre variables

    Examples:

    >>> from z3 import *
    >>> x,y = Ints('x y')
    >>> is_state(x)
    True
    >>> is_state(x+y==10)
    True
    >>> is_state(Implies(x==10,y==0))
    True
    >>> is_state(And(x==y,y==4))
    True
    >>> is_state(IntVal(3))
    True
    >>> is_state(3)
    Traceback (most recent call last):
    ...
    AssertionError: 3
    """
    return not is_trans(f)



def gen_vars(vs,i,s):
    """
    Generates variables at state s_i. See examples for details.

    v ->  v_i
    v_pre -> v_(i-1)

    Examples:

    >>> from z3 import *
    >>> x,y = Ints('x y')

    >>> gen_vars([x,y],10,s=None)
    [(y, y_10), (x, x_10)]

    >>> gen_vars([x,pre(y)],10,s=None)
    [(y_pre, y_9), (x, x_10)]

    >>> gen_vars([x,pre(y)],1,s=None)
    [(y_pre, y_0), (x, x_1)]

    >>> gen_vars([x,pre(y)],0,s=None)
    Traceback (most recent call last):
    ...
    AssertionError: cannot generate pre(var) with i=0

    >>> gen_vars([x,pre(y)],9,s='i')
    [(y_pre, y_i_8), (x, x_i_9)]

    >>> gen_vars([x,pre(y)],1,s='n')
    [(y_pre, y_n_0), (x, x_n_1)]

    """
    if __debug__:
        assert len(vs) > 0, vs
        assert i>=0, i
        assert (not i==0) or all(not is_pre(v) for v in vs), \
            'cannot generate pre(var) with i=0'

    def mk_name(i,v):
        s_ = '_'
        if s is not None:
            s_ = s_ + s + '_'

        if str(v).endswith(pre_kw):
            d = i-1
            name = str(v)[:-len(pre_kw)] + s_ + str(d)
        else:
            name = str(v) + s_ + str(i)
        return name



    #so that the longest one is replaced first
    old_vars = sorted(vs,key=str,reverse=True)

    new_names = [mk_name(i,v) for v in old_vars]
    new_vars= [mk_var(ns,v.sort())
               for ns,v in zip(new_names,old_vars)]


    vss = zip(old_vars,new_vars)

    return vss



def substitute_f(f,i,s=None):
    """
    Replaces all variables v in f with v_(i*_)

    s = a symbol string, e.g. n (so we will have the variable
    x_n_1 instead of x_1

    Examples:

    >>> from z3 import *
    >>> x,x_pre,y,y_pre = Ints('x x_pre y y_pre')

    >>> substitute_f(Implies(x==10,y==5),i=0)
    Or(Not(x_0 == 10), y_0 == 5)

    >>> substitute_f(Implies(x==10,y==5),i=1)
    Or(Not(x_1 == 10), y_1 == 5)

    >>> substitute_f(Implies(x==10,pre(y)==5),i=1)
    Or(Not(x_1 == 10), y_0 == 5)

    >>> substitute_f(Implies(x==10,pre(y)==5),1,s='m')
    Or(Not(x_m_1 == 10), y_m_0 == 5)


    >>> substitute_f(Implies(x==10,pre(y)==5),10,s='m')
    Or(Not(x_m_10 == 10), y_m_9 == 5)

    >>> substitute_f(BoolVal(False),i=10)
    False

    >>> substitute_f(IntVal(100),i=10)
    100

    """

    if __debug__:
        assert is_expr(f)
        assert i >= 0
        assert i != 0 or is_state(f) # v_pre => i!=0
        assert not s or isinstance(s,str) and len(s) >= 1

    vs = get_vars(f)

    if not vs: #e.g. True, 5, etc  has no variables so return as is
        return f
    else:
        vss = gen_vars(vs,i,s)
        f_ = f
        for vs in vss:
            f_ = substitute(f_,vs)
        return f_


def mk_OIA(vs):
    """
    Create an expression representing the One Input Assumption over
    the variables in vs.

    version 1 (this implementation):
    (x # pre(x) and y=pre(y) ...) OR
    (y # pre(y) and x=pre(x) ...) OR

    version 2:
    (x # pre(x) => y=pre(y) and ...) AND
    (y # pre(y) => x=pre(x) and ...) AND
    (x#pre(x) or y#pre(y) ...)

    Examples:

    >>> from z3 import *
    >>> x = Int('x')
    >>> y = Real('y')
    >>> z = Bool('z')
    >>> mk_OIA([x,y,z])
    Or(And(x != x_pre, y == y_pre, z == z_pre),
       And(y != y_pre, x == x_pre, z == z_pre),
       And(z != z_pre, x == x_pre, y == y_pre))

   >>> mk_OIA([x])
   x != x_pre

   >>> mk_OIA([])
   """
    if __debug__:
        assert is_list(vs) and all(not is_pre(v) for v in vs), vs

    oia = lambda v,vs: myAnd(v != pre(v),
                           *[v_ == pre(v_) for v_ in vs])

    return myOr([oia(v,vs[:i]+vs[i+1:]) for i,v in enumerate(vs)])



def atT(c,when_c=None):
    """
    Return And(!pre(c),c,when_c)

    When seeing the SCR syntax such as `@T(x) when c1`, the parser calls
    atT(x,c1') where c1' is c1 with all variables v => pre(v).
    In other words, the when_c only contains 'pre' variables.

    IMPORTANT: SCR syntax allows syntax such as `@T(x) when c1 OR @T(x) when c2`
    But I require explicit parentheses around these
    `(@T(x) when c1) OR (@T(x) when c2)`.
    The reason is to avoid ambiguity:
    'c1 OR @T(x) when c2' could be treated as an expression c3, i.e.
    @T(x) when c3.

    EXAMPLES:

    >>> from z3 import *
    >>> x,y = Ints('x y')
    >>> atT(x==10)
    And(Not(x_pre == 10), x == 10)


    >>> atT(x==10, pre(x)!= pre(y))
    And(Not(x_pre == 10), x == 10, x_pre != y_pre)

    >>> atT(Or(x==10,y==3),pre(x)!= pre(y))
    And(Not(Or(x_pre == 10, y_pre == 3)),
        Or(x == 10, y == 3),
        x_pre != y_pre)

    """

    if __debug__:
        assert is_state(c), c
        assert not when_c or is_pre_f(when_c),\
             "'{}' does not have the right WHEN format. "\
                    "Perhaps missing parenthesis, e.g."\
                    "(@T(x) when c1) OR (@T(y) when c2). "\
                    "See document in function for details.".format(when_c)


    vss_c_cur = get_vars(c)

    vss_c_pre = map(pre, vss_c_cur)
    vss_c     = zip(vss_c_cur, vss_c_pre)

    not_c = Not(substitute(c,*vss_c))
    return myAnd(not_c,c,when_c)


def atF(c,when_c=None):
    """Analogous to atT"""
    return atT(Not(c), when_c=when_c)


def atC(v,when_c=None):
    """
    Analogous to atT

    Return And(pre(v) != v, when_c)

    EXAMPLES:

    >>> from z3 import *
    >>> x,y = Bools('x y')
    >>> atC(x)
    x_pre != x

    >>> atC(x,when_c = pre(x) == pre(y))
    And(x_pre != x, x_pre == y_pre)
    """
    if __debug__:
        assert is_expr_var(v) and not is_pre(v), v
        assert not when_c or is_pre_f(when_c), when_c


    f = myAnd(pre(v) != v, when_c)
    return f



def atT_compat(c,when_c=None):
    """
    Similar to atT but the when_c condition contains only current variables.
    Essentially a syntactical sugar because typing pre(x) , pre(y)  is
    tiresome.  Mostly use in invariant generation.

    EXAMPLES:

    >>> from z3 import *
    >>> x,y = Ints('x y')
    >>> atT_compat(x==10)
    And(Not(x_pre == 10), x == 10)


    >>> atT_compat(x==10, x!= y)
    And(Not(x_pre == 10), x == 10, Not(x_pre == y_pre))

    >>> atT_compat(Or(x==10,y==3),x!= y)
    And(Not(Or(x_pre == 10, y_pre == 3)),
        Or(x == 10, y == 3),
        Not(x_pre == y_pre))
    """
    if __debug__:
        assert is_state(c), c
        assert when_c is None or is_cur_f(when_c), when_c

    return atT(c,when_c=pre_f(when_c))


def atF_compat(c,when_c=None):
    """
    Analogous to atT_compat
    """
    return atT_compat(Not(c),when_c=when_c)


def atC_compat(c,when_c=None):
    """
    Analogous to atT_compat

    EXAMPLES:

    >>> from z3 import *
    >>> x,y = Bools('x y')
    >>> atC(x)
    x_pre != x

    >>> atC_compat(x,when_c = x == y)
    And(x_pre != x, x_pre == y_pre)
    """

    if __debug__:
        assert is_state(c), c
        assert when_c is None or is_cur_f(when_c), when_c
    return atC(c,when_c=pre_f(when_c))



if __name__ == '__main__':
    import doctest
    doctest.testmod()

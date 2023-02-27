# from z3util import mk_var, get_vars, is_expr_var, fhash, myOr, myAnd
import z3
from z3 import (is_expr, substitute, Not)
# from z3 import *


class SCR:
    pre_kw = '_pre'
    pre_vars_dict = {}
    cur_vars_dict = {}

    @classmethod
    def is_pre(cls, v):
        """
        Return if the variable v is a pre variable,
        i.e. if v ends with pre_kw
        """
        return str(v).endswith(cls.pre_kw)

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
        assert is_expr(f), f

        return all(cls.is_pre(v) for v in get_vars(f))

    @classmethod
    def pre_f(cls, f):
        """
        Convert a formula f with cur vars to a formula with pre vars

        >>> from z3 import *
        >>> x,y,z = Ints('x y z')

        >>> pre_f(z == 9)
        z_pre == 9

        >>> pre_f(And(y == 4, z == 9) )
        And(y_pre == 4, z_pre == 9)

        """
        assert f is None or is_cur_f(f), f

        if f is None:
            return None
        elif is_expr_var(f):
            return pre(f)
        else:
            vss = [(v, pre(v)) for v in get_vars(f)]
            return substitute(f, *vss)

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
        assert is_expr(f), f

        return all(not is_pre(v) for v in get_vars(f))

    # def cur_f(f):
    #     """
    #     Convert a formula f with pre vars to a formula with cur vars

    #     >>> from z3 import *
    #     >>> x,y,z = Ints('x y z')

    #     >>> cur_f(pre(z) == 9)
    #     z == 9

    #     >>> cur_f(And(pre(y) == 4, pre(z) == 9) )
    #     And(y == 4, z == 9)

    #     >>> cur_f(pre(y) == z)
    #     Traceback (most recent call last):
    #     ...
    #     AssertionError: y_pre == z
    #     """
    #     assert f is None or is_pre_f(f), f

    #     if f is None:
    #         return None
    #     if is_expr_var(f):
    #         return cur(f)
    #     else:
    #         vss = [(v, cur(v)) for v in get_vars(f)]
    #         return substitute(f, *vss)

    # def is_trans(f):
    #     """
    #     Check if f has some pre variables

    #     Examples:

    #     >>> from z3 import *
    #     >>> x,y = Ints('x y')
    #     >>> is_trans(x)
    #     False
    #     >>> is_trans(x+y==10)
    #     False
    #     >>> is_trans(Implies(x==10,y==0))
    #     False
    #     >>> is_trans(And(x==y,y==4))
    #     False
    #     >>> is_trans(IntVal(3))
    #     False
    #     >>> is_trans(3)
    #     Traceback (most recent call last):
    #     ...
    #     AssertionError: 3
    #     """

    #     assert is_expr(f), f

    #     return pre_kw in str(f)

    # def is_state(f):
    #     """
    #     Check if f has no pre variables

    #     Examples:

    #     >>> from z3 import *
    #     >>> x,y = Ints('x y')
    #     >>> is_state(x)
    #     True
    #     >>> is_state(x+y==10)
    #     True
    #     >>> is_state(Implies(x==10,y==0))
    #     True
    #     >>> is_state(And(x==y,y==4))
    #     True
    #     >>> is_state(IntVal(3))
    #     True
    #     >>> is_state(3)
    #     Traceback (most recent call last):
    #     ...
    #     AssertionError: 3
    #     """

    # def mk_OIA(vs):
    #     """
    #     Create an expression representing the One Input Assumption over
    #     the variables in vs.

    #     version 1 (this implementation):
    #     (x # pre(x) and y=pre(y) ...) OR
    #     (y # pre(y) and x=pre(x) ...) OR

    #     version 2:
    #     (x # pre(x) => y=pre(y) and ...) AND
    #     (y # pre(y) => x=pre(x) and ...) AND
    #     (x#pre(x) or y#pre(y) ...)

    #     Examples:

    #     >>> from z3 import *
    #     >>> x = Int('x')
    #     >>> y = Real('y')
    #     >>> z = Bool('z')
    #     >>> mk_OIA([x,y,z])
    #     Or(And(x != x_pre, y == y_pre, z == z_pre),
    #        And(y != y_pre, x == x_pre, z == z_pre),
    #        And(z != z_pre, x == x_pre, y == y_pre))

    #    >>> mk_OIA([x])
    #    x != x_pre

    #    >>> mk_OIA([])
    #    """
    #     assert vs and all(not is_pre(v) for v in vs), vs

    #     def oia(v, vs): return myAnd(v != pre(v),
    #                                  *[v_ == pre(v_) for v_ in vs])

    #     return myOr([oia(v, vs[:i]+vs[i+1:]) for i, v in enumerate(vs)])

    # def atT(c, when_c=None):
    #     """
    #     Return And(!pre(c),c,when_c)

    #     When seeing the SCR syntax such as `@T(x) when c1`, the parser calls
    #     atT(x,c1') where c1' is c1 with all variables v => pre(v).
    #     In other words, the when_c only contains 'pre' variables.

    #     IMPORTANT: SCR syntax allows syntax such as `@T(x) when c1 OR @T(x) when c2`
    #     But I require explicit parentheses around these
    #     `(@T(x) when c1) OR (@T(x) when c2)`.
    #     The reason is to avoid ambiguity:
    #     'c1 OR @T(x) when c2' could be treated as an expression c3, i.e.
    #     @T(x) when c3.

    #     EXAMPLES:

    #     >>> from z3 import *
    #     >>> x,y = Ints('x y')
    #     >>> atT(x==10)
    #     And(Not(x_pre == 10), x == 10)

    #     >>> atT(x==10, pre(x)!= pre(y))
    #     And(Not(x_pre == 10), x == 10, x_pre != y_pre)

    #     >>> atT(Or(x==10,y==3),pre(x)!= pre(y))
    #     And(Not(Or(x_pre == 10, y_pre == 3)),
    #         Or(x == 10, y == 3),
    #         x_pre != y_pre)

    #     """

    #     assert is_state(c), c
    #     assert not when_c or is_pre_f(when_c),\
    #         "'{}' does not have the right WHEN format. "\
    #         "Perhaps missing parenthesis, e.g."\
    #         "(@T(x) when c1) OR (@T(y) when c2). "\
    #         "See document in function for details.".format(when_c)

    #     vss_c_cur = get_vars(c)

    #     vss_c_pre = map(pre, vss_c_cur)
    #     vss_c = zip(vss_c_cur, vss_c_pre)

    #     not_c = Not(substitute(c, *vss_c))
    #     return myAnd(not_c, c, when_c)

    # def atF(c, when_c=None):
    #     """Analogous to atT"""
    #     return atT(Not(c), when_c=when_c)

    # def atC(v, when_c=None):
    #     """
    #     Analogous to atT

    #     Return And(pre(v) != v, when_c)

    #     EXAMPLES:

    #     >>> from z3 import *
    #     >>> x,y = Bools('x y')
    #     >>> atC(x)
    #     x_pre != x

    #     >>> atC(x,when_c = pre(x) == pre(y))
    #     And(x_pre != x, x_pre == y_pre)
    #     """
    #     assert is_expr_var(v) and not is_pre(v), v
    #     assert not when_c or is_pre_f(when_c), when_c

    #     f = myAnd(pre(v) != v, when_c)
    #     return f

    # def atT_compat(c,when_c=None):
    #     """
    #     Similar to atT but the when_c condition contains only current variables.
    #     Essentially a syntactical sugar because typing pre(x) , pre(y)  is
    #     tiresome.  Mostly use in invariant generation.

    #     EXAMPLES:

    #     >>> from z3 import *
    #     >>> x,y = Ints('x y')
    #     >>> atT_compat(x==10)
    #     And(Not(x_pre == 10), x == 10)

    #     >>> atT_compat(x==10, x!= y)
    #     And(Not(x_pre == 10), x == 10, Not(x_pre == y_pre))

    #     >>> atT_compat(Or(x==10,y==3),x!= y)
    #     And(Not(Or(x_pre == 10, y_pre == 3)),
    #         Or(x == 10, y == 3),
    #         Not(x_pre == y_pre))
    #     """
    #     assert is_state(c), c
    #     assert when_c is None or is_cur_f(when_c), when_c

    #     return atT(c,when_c=pre_f(when_c))

    # def atF_compat(c,when_c=None):
    #     """
    #     Analogous to atT_compat
    #     """
    #     return atT_compat(Not(c),when_c=when_c)

    # def atC_compat(c,when_c=None):
    #     """
    #     Analogous to atT_compat

    #     EXAMPLES:

    #     >>> from z3 import *
    #     >>> x,y = Bools('x y')
    #     >>> atC(x)
    #     x_pre != x

    #     >>> atC_compat(x,when_c = x == y)
    #     And(x_pre != x, x_pre == y_pre)
    #     """

    #     assert is_state(c), c
    #     assert when_c is None or is_cur_f(when_c), when_c
    #     return atC(c,when_c=pre_f(when_c))


# if __name__ == '__main__':
#     import doctest
#     doctest.testmod()

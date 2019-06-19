from z3 import *


import settings
timeout = settings.SOLVER_TIMEOUT * 1000


class Z3(object):
    @classmethod
    def isVar(cls, v):
        return z3.is_const(v) and v.decl().kind() == z3.Z3_OP_UNINTERPRETED

    @classmethod
    def _getVars(cls, f, rs):
        """
        Helper method to obtain variables from a formula f recursively.
        Results are stored in the list rs.
        """
        assert z3.is_expr(f) or z3.is_const(f), f
        if z3.is_const(f):
            if cls.isVar(f):
                rs.add(f)
        else:
            for c in f.children():
                cls._getVars(c, rs)

    @classmethod
    def getVars(cls, f):
        """
        sage: x,y,z = z3.Ints("x y z")
        sage: f = z3.And(x + y == z , y + z == z)
        sage: assert(Z3.getVars(f) == {z, y, x})
        """
        assert z3.is_expr(f), f

        rs = set()
        cls._getVars(f, rs)
        return frozenset(rs)

    @classmethod
    def createSolver(cls):
        solver = z3.Solver()
        timeout = settings.SOLVER_TIMEOUT * 1000
        solver.set(timeout=timeout)  # secs
        return solver

    @classmethod
    def extract(self, models):
        assert models is None or models is False \
            or (isinstance(models, list) and
                all(isinstance(m, z3.ModelRef) for m in models)
                and models), models

        cexs = set()
        isSucc = models is not None
        if isSucc and models:  # disproved
            cexs = [{str(s): sage.all.sage_eval(str(model[s])) for s in model}
                    for model in models]
        return cexs, isSucc

    @classmethod
    def getModels(cls, f, k):
        """
        Returns the first k models satisfiying f.
        If f is not satisfiable, returns False.
        If f cannot be solved, returns None
        If f is satisfiable, returns the first k models
        Note that if f is a tautology, i.e., True, then the result is []
        """
        assert z3.is_expr(f), f
        assert k >= 1, k

        solver = cls.createSolver()
        solver.add(f)

        models = []
        i = 0
        while solver.check() == z3.sat and i < k:
            i = i + 1
            m = solver.model()
            if not m:  # if m == []
                break
            models.append(m)
            # create new constraint to block the current model
            block = z3.Not(z3.And([v() == m[v] for v in m]))
            solver.add(block)

        stat = solver.check()

        if stat == z3.unknown:
            rs = None
        elif stat == z3.unsat and i == 0:
            rs = False
        else:
            rs = models

        if isinstance(rs, list) and not rs:
            print 'bug'
            print(f)
            print(k)

        return rs, stat

    @classmethod
    def imply(cls, fs, g, use_reals):
        """
        sage: var('x y')
        (x, y)
        sage: assert Z3.imply([x-6==0],x*x-36==0,use_reals=False)
        sage: assert Z3.imply([x-6==0,x+6==0],x*x-36==0,use_reals=False)
        sage: assert not Z3.imply([x*x-36==0],x-6==0,use_reals=False)
        sage: assert not Z3.imply([x-6==0],x-36==0,use_reals=False)
        sage: assert Z3.imply([x-7>=0], x>=6,use_reals=False)
        sage: assert not Z3.imply([x-7>=0], x>=8,use_reals=False)
        sage: assert not Z3.imply([x-6>=0], x-7>=0,use_reals=False)
        sage: assert not Z3.imply([x-7>=0,y+5>=0],x+y-3>=0,use_reals=False)
        sage: assert Z3.imply([x-7>=0,y+5>=0],x+y-2>=0,use_reals=False)
        sage: assert Z3.imply([x-2*y>=0,y-1>=0],x-2>=0,use_reals=False)
        sage: assert not Z3.imply([],x-2>=0,use_reals=False)
        sage: assert Z3.imply([x-7>=0,y+5>=0],x+y-2>=0,use_reals=False)
        sage: assert Z3.imply([x^2-9>=0,x>=0],x-3>=0,use_reals=False)
        sage: assert not Z3.imply([1/2*x**2 - 3/28*x + 1 >= 0],1/20*x**2 - 9/20*x + 1 >= 0,use_reals=True)
        sage: assert Z3.imply([1/20*x**2 - 9/20*x + 1 >= 0],1/2*x**2 - 3/28*x + 1 >= 0,use_reals=True)
        sage: assert Z3.imply([x-6==0],x*x-36==0,use_reals=False)
        sage: assert not Z3.imply([x+7>=0,y+5>=0],x*y+36>=0,use_reals=False)
        sage: assert not Z3.imply([x+7>=0,y+5>=0],x*y+35>=0,use_reals=False)
        sage: assert not Z3.imply([x+7>=0,y+5>=0],x*y-35>=0,use_reals=False)
        sage: assert not Z3.imply([x+7>=0],x-8>=0,use_reals=False)
        sage: assert Z3.imply([x+7>=0],x+8>=0,use_reals=False)
        sage: assert Z3.imply([x+7>=0],x+8.9>=0,use_reals=True)
        sage: assert Z3.imply([x>=7,y>=5],x*y>=35,use_reals=False)
        sage: assert not Z3.imply([x>=-7,y>=-5],x*y>=35,use_reals=False)
        """

        assert all(Miscs.is_expr(f) for f in fs), fs
        assert Miscs.is_expr(g), g
        assert isinstance(use_reals, bool), use_reals

        if not fs:
            return False  # conservative approach
        fs = [cls.toZ3(f, use_reals, useMod=False) for f in fs]
        g = cls.toZ3(g, use_reals, useMod=False)
        return cls._imply(fs, g)

    @classmethod
    def _imply(cls, fs, g):
        assert fs

        claim = z3.Implies(z3.And(fs), g)
        models, _ = cls.getModels(z3.Not(claim), k=1)
        return models is False

    # @classmethod
    # def reduceSMT(cls, ps, use_reals):
    #     eqts, eqtsLargeCoefs, ieqs = [], [], []
    #     for p in ps:
    #         if p.operator() == sage.all.operator.eq:
    #             if len(Miscs.getCoefs(p)) > 10:
    #                 eqtsLargeCoefs.append(p)
    #             else:
    #                 eqts.append(p)
    #         else:
    #             ieqs.append(p)

    #     if len(eqts + ieqs) <= 1:
    #         return ps

    #     ps = sorted(ieqs) + eqts
    #     rs = list(ps)

    #     for p in ps:
    #         if p not in rs:
    #             continue
    #         xclude = [p_ for p_ in rs if p_ != p]
    #         if cls.imply(xclude, p, use_reals):
    #             rs = xclude

    #     rs.extend(eqtsLargeCoefs)
    #     return rs

    @classmethod
    def toZ3(cls, p, use_reals, useMod):
        """
        Convert a Sage expression to a Z3 expression

        Initially implements with a dictionary containing variables
        e.g. {x:Real('x')} but the code is longer and more complicated.
        This implemention does not require a dictionary pass in.

        sage: Z3.toZ3(x*x*x, False, useMod=False)
        x*x*x
        """

        assert isinstance(use_reals, bool), use_reals
        assert isinstance(useMod, bool), useMod

        def retval(p):
            if p.is_symbol():
                _f = z3.Real if use_reals else z3.Int
            else:
                _f = z3.RealVal if use_reals else z3.IntVal

            try:
                return _f(str(p))
            except Exception:
                assert False, "cannot parse {}".format(p)

        oprs = p.operands()
        if oprs:
            op = p.operator()

            # z3 has problem w/ t^c , so use t*t*t..
            if op == operator.pow:
                assert len(oprs) == 2, oprs
                t, c = oprs
                t = cls.toZ3(t, use_reals, useMod)
                if useMod:
                    c = cls.toZ3(c, use_reals, useMod)
                    res = reduce(operator.mod, [t, c])
                else:
                    vs = [t] * c
                    res = reduce(operator.mul, vs)
            else:
                oprs = [cls.toZ3(o, use_reals, useMod) for o in oprs]
                res = reduce(op, oprs)

        else:
            res = retval(p)

        assert z3.is_expr(res), res
        if useMod:
            mlog.debug("mod hack: {} => {}".format(p, res))
        return res


k_3_SYMINT, z_1_SYMINT, a_2_SYMINT, a, c, x, y, z, k = z3.Ints(
    'k_3_SYMINT, z_1_SYMINT, a_2_SYMINT, a, c, x, y, z, k')

f = Not(Implies(And(Not(k_3_SYMINT <= 5),
                    Not(k_3_SYMINT <= 4),
                    Not(k_3_SYMINT <= 3),
                    Not(k_3_SYMINT <= 2),
                    Not(k_3_SYMINT <= 1),
                    k_3_SYMINT <= 10,
                    Not(k_3_SYMINT <= 0),
                    z_1_SYMINT <= 10,
                    z_1_SYMINT >= 0,
                    z == z_1_SYMINT,
                    a == a_2_SYMINT,
                    k == k_3_SYMINT,
                    x ==
                    z_1_SYMINT *
                    (z_1_SYMINT *
                     (z_1_SYMINT *
                      (z_1_SYMINT *
                       (a_2_SYMINT*z_1_SYMINT + a_2_SYMINT) +
                          a_2_SYMINT) +
                         a_2_SYMINT) +
                     a_2_SYMINT) +
                    a_2_SYMINT,
                    y ==
                    z_1_SYMINT *
                    z_1_SYMINT *
                    z_1_SYMINT *
                    z_1_SYMINT *
                    z_1_SYMINT,
                    c == 6),
                a*a*3 + x*x*-3 + x*z*-1 + a*41 + x*-41 == 0))


print Z3.getModels(f, 1)


@staticmethod
def my_ite_test(m, expr):
        s1 = str(z3.simplify(expr))

        simpl = z3.Tactic('ctx-solver-simplify')
        simpl = z3.TryFor(simpl, settings.SOLVER_TIMEOUT * 1000)
        s2 = str(simpl(expr)[0][0])

        if s1 != s2:
            print 'mismatch', m.lh, m.rh, m.term, str(m)
            print expr
            print s1
            print s2

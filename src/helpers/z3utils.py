from __future__ import annotations
from collections.abc import Callable
from typing import Any

import ast
import pdb
import operator
import functools
import z3
import helpers.vcommon as CM
import settings

DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.LOGGER_LEVEL)

class Z3:
    zTrue = z3.BoolVal(True)
    zFalse = z3.BoolVal(False)
    RLIMIT = settings.SOLVER_RLIMIT

    @classmethod
    def _process_fs(cls: type[Z3],
                    fs: list[z3.ExprRef | None],
                    and_or_f: Callable[[list[z3.ExprRef]], Any]) -> z3.ExprRef | None:

        assert (isinstance(fs, list) and
                all(isinstance(f, z3.ExprRef) or f is None for f in fs)), fs

        filtered: list[z3.ExprRef] = [f for f in fs if f is not None]
        if not filtered:
            return None
        if len(filtered) == 1:
            return filtered[0]

        return and_or_f(filtered)

    @classmethod
    def _and(cls: type[Z3], fs: list[z3.ExprRef | None]) -> z3.ExprRef | None:
        return cls._process_fs(fs, z3.And)

    @classmethod
    def _or(cls: type[Z3], fs: list[z3.ExprRef | None]) -> z3.ExprRef | None:
        return cls._process_fs(fs, z3.Or)

    @classmethod
    def is_var(cls: type[Z3], v: Any) -> bool:
        return z3.is_const(v) and v.decl().kind() == z3.Z3_OP_UNINTERPRETED

    @classmethod
    def _get_vars(cls: type[Z3], f: z3.ExprRef, rs: set[Any]) -> None:
        """
        Helper method to obtain variables from a formula f recursively.
        Results are stored in the list rs.
        """
        assert isinstance(f, z3.ExprRef) or z3.is_const(f), f
        if z3.is_const(f):
            if cls.is_var(f):
                rs.add(f)
        else:
            for c in f.children():
                cls._get_vars(c, rs)

    @classmethod
    @functools.cache
    def get_vars(cls: type[Z3], f: z3.ExprRef) -> frozenset[z3.ExprRef]:
        """
        >>> x,y,z = z3.Ints("x y z")
        >>> assert(Z3.get_vars(z3.And(x + y == z , y + z == z)) == {z, y, x})
        """
        assert isinstance(f, z3.ExprRef), f

        rs: set[Any] = set()
        cls._get_vars(f, rs)
        return frozenset(rs)

    @classmethod
    def create_solver(cls: type[Z3],
                        maximize: bool = False
                        ) -> z3.Optimize | z3.Solver:
        assert isinstance(maximize, bool), maximize

        solver = z3.Optimize() if maximize else z3.Solver()
        # rlimit = deterministic work-unit cutoff (reproducible under MP
        # contention), the sole solver bound.
        solver.set("rlimit", cls.RLIMIT)
        return solver

    @classmethod
    def extract(cls: type[Z3], models: list[z3.ModelRef],
                f: Callable[[str], str]) -> tuple[list[dict[str, str]], bool]:

        assert (
                models is None
                or models is False
                or (
                        isinstance(models, list)
                        and all(isinstance(m, z3.ModelRef) for m in models)
                        and models
                )
        ), models

        cexs: list = []
        is_succ = models is not None
        if is_succ and models:  # disproved
            cexs = []
            for model in models:
                cex = {}
                for v in model:
                    mv = str(model[v])
                    try:
                        cex[str(v)] = mv if f is None else f(mv)
                    except ValueError:
                        # mlog.warning('cannot analyze {}'.format(model))
                        pass
                cexs.append(cex)
        return cexs, is_succ

    @classmethod
    def get_models(cls: type[Z3],
                   f: z3.ExprRef,
                   k: int
                  ) -> tuple[None | bool | list[z3.Optimize | z3.Solver], z3.CheckSatResult]:
        """
        Returns the first k models satisfiying f.
        If f is not satisfiable, returns False.
        If f cannot be solved, returns None
        If f is satisfiable, returns the first k models
        Note that if f is a tautology, i.e., True, then the result is []
        """
        assert z3.is_expr(f), f
        assert k >= 1, k
        solver = cls.create_solver(maximize=False)
        solver.add(f)
        models = []
        i = 0
        while solver.check() == z3.sat and i < k:
            i += 1
            m = solver.model()
            if not m:  # if m == []
                mlog.warning("sat but no model")
                break
            models.append(m)
            # create new constraint to block the current model
            ands = []
            for v in m:
                try:
                    e = v() == m[v]
                    ands.append(e)
                except z3.Z3Exception:
                    """
                    when the model contains functions, e.g.,
                    [..., div0 = [(3, 2) -> 1, else -> 0]]
                    """
                    # mlog.warning('cannot analyze {}'.format(m))
                    pass
            block = z3.Not(z3.And(ands))
            solver.add(block)

        stat = solver.check()
        if stat == z3.unknown:  # for unknown/unsat/sat, use == instead of is
            rs: None | bool | list[Any] = None
        elif stat == z3.unsat and i == 0:
            rs = False
        else:
            if models:
                rs = models
            else:
                # tmp fix,  ProdBin has a case when
                # stat is sat but model is []
                # so tmp fix is to treat that as unknown
                rs = None
                stat = z3.unknown

        assert not (isinstance(rs, list) and not rs), rs
        return rs, stat

    @classmethod
    def is_valid(cls: type[Z3], claim: z3.ExprRef) -> bool:
        _, stat = cls.get_models(z3.Not(claim), 1)
        return stat == z3.unsat

    @classmethod
    def imply(cls: type[Z3], fs: list[z3.ExprRef], g: z3.ExprRef) -> bool:
        """
        >>> var('x y')
        (x, y)
        >>> assert Z3.imply([x-6==0],x*x-36==0)
        >>> assert Z3.imply([x-6==0,x+6==0],x*x-36==0)
        >>> assert not Z3.imply([x*x-36==0],x-6==0)
        >>> assert not Z3.imply([x-6==0],x-36==0)
        >>> assert Z3.imply([x-7>=0], x>=6)
        >>> assert not Z3.imply([x-7>=0], x>=8)
        >>> assert not Z3.imply([x-6>=0], x-7>=0)
        >>> assert not Z3.imply([x-7>=0,y+5>=0],x+y-3>=0)
        >>> assert Z3.imply([x-7>=0,y+5>=0],x+y-2>=0)
        >>> assert Z3.imply([x-2*y>=0,y-1>=0],x-2>=0)
        >>> assert not Z3.imply([],x-2>=0)
        >>> assert Z3.imply([x-7>=0,y+5>=0],x+y-2>=0)
        >>> assert Z3.imply([x**2-9>=0,x>=0],x-3>=0)
        >>> assert Z3.imply([x-6==0],x*x-36==0)
        >>> assert not Z3.imply([x+7>=0,y+5>=0],x*y+36>=0)
        >>> assert not Z3.imply([x+7>=0,y+5>=0],x*y+35>=0)
        >>> assert not Z3.imply([x+7>=0,y+5>=0],x*y-35>=0)
        >>> assert not Z3.imply([x+7>=0],x-8>=0)
        >>> assert Z3.imply([x+7>=0],x+8>=0)
        >>> assert Z3.imply([x>=7,y>=5],x*y>=35)
        >>> assert not Z3.imply([x>=-7,y>=-5],x*y>=35)

        # >>> assert not Z3.imply([1/2*x**2 - 3/28*x + 1 >= 0],1/20*x**2 - 9/20*x + 1 >= 0,use_reals=True)
        # >>> assert Z3.imply([1/20*x**2 - 9/20*x + 1 >= 0],1/2*x**2 - 3/28*x + 1 >= 0,use_reals=True)
        # >>> assert Z3.imply([x+7>=0],x+8.9>=0,use_reals=True)

        """

        if not fs:
            return False  # conservative approach

        fs = [Z3.parse(str(f)) for f in fs]
        g = Z3.parse(str(g))

        return cls._imply(fs, g)

    @classmethod
    def _imply(cls: type[Z3],
                fs: z3.ExprRef | list[z3.ExprRef],
                g: z3.ExprRef,
                is_conj: bool | None = True) -> bool:
        assert z3.is_expr(g), g

        if is_conj:  # And(fs) => g
            if z3.is_expr(fs):
                claim = z3.Implies(fs, g)
            else:
                claim = z3.Implies(z3.And(fs), g)
        else:  # g => Or(fs)
            if z3.is_expr(fs):
                claim = z3.Implies(g, fs)
            else:
                claim = z3.Implies(g, z3.Or(fs))

        models, _ = cls.get_models(z3.Not(claim), k=1)
        return models is False

    @classmethod
    @functools.cache
    def _parse_str(cls, s: str) -> z3.ExprRef:
        """
        Cached string->z3 path. Terms (e.g. octagon lhs) get parsed many times
        across the incremental-depth solver loops; memoizing on the source
        string avoids redundant ast.parse + z3.simplify. The recursive parse
        below is passed ast nodes (never str), so it never re-enters this cache.
        """
        s = s.replace("^", "**")
        tnode = ast.parse(s)
        tnode = tnode.body[0].value
        try:
            expr = cls.parse(tnode)
            expr = z3.simplify(expr)
            return expr
        except NotImplementedError:
            mlog.error(f"cannot parse: '{s}'\n{ast.dump(tnode)}")
            raise

    @classmethod
    def parse(cls, node: str | Any) -> z3.ExprRef:
        """
        Parse a string to a Z3 expression
        E.g.,  parse("x>=10*10")

        Note cannot parse something like tCtr == y - 1/2*sqrt(4*y**2 - 8*x + 4*y + 1) + 1/2
        """
        # print(ast.dump(node))

        if isinstance(node, str):
            return cls._parse_str(node)

        elif isinstance(node, ast.BoolOp):
            vals = [cls.parse(v) for v in node.values]
            op = cls.parse(node.op)
            return op(vals)

        elif isinstance(node, ast.And):
            return z3.And

        elif isinstance(node, ast.Or):
            return z3.Or

        elif isinstance(node, ast.BinOp):
            if (isinstance(node.op, ast.Pow)
                    and isinstance(node.right, ast.Constant)
                    and isinstance(node.right.value, int)
                    and node.right.value >= 0):
                # z3.Int('x') ** n returns Real sort; expand to multiplication to stay in Int
                base = cls.parse(node.left)
                exp = node.right.value
                if exp == 0:
                    return z3.IntVal(1)
                result = base
                for _ in range(exp - 1):
                    result = result * base
                return result
            left = cls.parse(node.left)
            right = cls.parse(node.right)
            op = cls.parse(node.op)
            return op(left, right)

        elif isinstance(node, ast.UnaryOp):
            operand = cls.parse(node.operand)
            op = cls.parse(node.op)
            return op(operand)

        elif isinstance(node, ast.Compare):
            assert len(node.ops) == 1 and len(
                node.comparators) == 1, ast.dump(node)
            left = cls.parse(node.left)
            right = cls.parse(node.comparators[0])
            op = cls.parse(node.ops[0])
            return op(left, right)

        elif isinstance(node, ast.Name):
            return z3.Int(str(node.id))
        elif isinstance(node, ast.Constant):
            if isinstance(node.value, bool):
                return z3.BoolVal(node.value)
            if isinstance(node.value, float):
                return z3.RealVal(str(node.value))
            return z3.IntVal(str(node.value))
        elif isinstance(node, ast.Not):
            return z3.Not
        elif isinstance(node, ast.Add):
            return operator.add
        elif isinstance(node, ast.Mult):
            return operator.mul
        elif isinstance(node, ast.Div):
            return operator.truediv  # tvn:  WARNING: might not be accurate
        elif isinstance(node, ast.FloorDiv):
            return operator.truediv  # tvn:  WARNING: might not be accurate
        elif isinstance(node, ast.Mod):
            return operator.mod
        elif isinstance(node, ast.Pow):
            return operator.pow
        elif isinstance(node, ast.Sub):
            return operator.sub
        elif isinstance(node, ast.USub):
            return operator.neg
        elif isinstance(node, ast.Eq):
            return operator.eq
        elif isinstance(node, ast.NotEq):
            return operator.ne
        elif isinstance(node, ast.Lt):
            return operator.lt
        elif isinstance(node, ast.LtE):
            return operator.le
        elif isinstance(node, ast.Gt):
            return operator.gt
        elif isinstance(node, ast.GtE):
            return operator.ge

        else:
            raise NotImplementedError(ast.dump(node))

    @staticmethod
    @functools.cache
    def simplify(f: z3.ExprRef) -> z3.ExprRef:
        assert z3.is_expr(f), f
        # Use Z3's built-in lightweight simplifier (constant folding, arithmetic
        # normalization) instead of ctx-solver-simplify which is solver-backed and
        # can take seconds per call.
        return z3.simplify(f)

    @staticmethod
    def to_smt2_str(f: z3.ExprRef, status: str = "unknown", name: str = "benchmark", logic: str = "") -> str:
        v = (z3.Ast * 0)()
        s = z3.Z3_benchmark_to_smtlib_string(
            f.ctx_ref(), name, logic, status, "", 0, v, f.as_ast()
        )
        return s

    @classmethod
    def from_smt2_str(cls: type[Z3], s: str) -> z3.ExprRef:
        assertions = z3.parse_smt2_string(s)
        expr = cls.zTrue if not assertions else assertions[0]
        assert z3.is_expr(expr), expr
        return expr

    @classmethod
    def model_str(cls: type[Z3], m: list | z3.ModelRef, as_str: bool = True) -> list | str | z3.ModelRef | None:
        """
        Returned a 'sorted' model by its keys.
        e.g. if the model is y = 3 , x = 10, then the result is
        x = 10, y = 3

        EXAMPLES:
        see doctest examples from function prove()

        """
        assert m is None or m == [] or isinstance(m, z3.ModelRef)

        if m:
            vs = [(v, m[v]) for v in m]
            vs = sorted(vs, key=lambda a: str(a[0]))
            if as_str:
                return '\n'.join(f"{k} = {v}" for (k, v) in vs)
            else:
                return vs
        else:
            return str(m) if as_str else m

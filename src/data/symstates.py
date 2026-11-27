"""
Symbolic States
"""
import functools
import sys
import abc
from pathlib import Path

import z3

from typing import NamedTuple
import settings
import helpers.vcommon as CM
from helpers.miscs import MP
from helpers.z3utils import Z3
import data.prog
import data.traces
import infer.inv

mlog = CM.getLogger(__name__, settings.LOGGER_LEVEL)


class PathCond(NamedTuple):
    loc: str
    pc: z3.ExprRef
    slocal: z3.ExprRef

    def __str__(self) -> str:
        return f"loc: {self.loc}\npc: {self.pc}\nslocal: {self.slocal}"

    @property
    def expr(self):
        return z3.simplify(z3.And(self.pc, self.slocal))


class PathCondC(PathCond):
    pass


class PCs(set):  #{PathConds}

    def __init__(self, loc:str, depth:int) -> None:
        assert depth >= 1, depth
        
        super().__init__()
        self.loc = loc
        self.depth = depth

    def add(self, pc:PathCond):
        super().add(pc)

    @functools.cached_property
    def myexpr(self) -> z3.ExprRef:
        return Z3.simplify(z3.Or([p.expr for p in self]))

    @functools.cached_property
    def mypc(self) -> z3.ExprRef:
        return Z3.simplify(z3.Or([p.pc for p in self]))


class SymStatesDepth(dict):  # depth -> PCs

    @property
    def siz(self) -> int:
        return sum(len(x) for x in self.values())

          
class SymStates(dict):
    # loc -> SymStatesDepth

    def __init__(self, inp_decls: data.prog.Symbs , inv_decls: data.prog.DSymbs) -> None:
        self.inp_decls = inp_decls
        self.inv_decls = inv_decls
        self.inp_exprs = inp_decls.exprs
        self.exploration_info = {}

        super().__init__()

    @property
    def siz(self) -> int:
        return sum(symstatesdepth.siz for symstatesdepth in self.values())

    def compute(self, symstatesmaker_cls,
                filename: Path, mainQName: str, funname: str, tmpdir:Path) -> None:
        symstatesmaker = symstatesmaker_cls(
            filename, mainQName, funname, len(self.inp_decls), tmpdir
        )
        # Entry inputs and observed variables can share source names but
        # differ in value after assignments. Use the backend's entry symbols
        # when generating or excluding concrete inputs.
        self.inp_exprs = [z3.Const(symstatesmaker.input_prefix+s.name, s.expr.sort())
                          for s in self.inp_decls]
        ss = symstatesmaker.compute()
        self.exploration_info = getattr(symstatesmaker, "exploration_info", {})
        for loc in ss:
            self[loc] = SymStatesDepth(ss[loc])

    def check(self, dinvs: infer.inv.DInvs, 
              inps: None | data.traces.Inps
              ) -> tuple[dict, infer.inv.DInvs]:
        """
        Check invs, return cexs
        Also update inps
        """
        # assert not inps or (isinstance(inps, data.traces.Inps) and inps), inps

        mlog.debug(
            f"checking {dinvs.siz} invs:\n"
            f"{dinvs.__str__(print_first_n=20)}")
        tasks = [(loc, inv)
                 for loc in dinvs for inv in dinvs[loc] if inv.stat is None]
        refsD = {(loc, id(inv)): inv for loc, inv in tasks}

        def f(tasks):
            return [
                (loc, id(inv), self.mcheck_d(loc, inv, inps, ncexs=1))
                for loc, inv in tasks
            ]

        wrs = MP.run_mp("prove", tasks, f, settings.DO_MP)
        mCexs = []
        mdinvs = infer.inv.DInvs()
        for loc, inv_id, (cexs, is_succ) in wrs:
            inv = refsD[(loc, inv_id)]

            if cexs:
                stat = infer.inv.Inv.DISPROVED
                mCexs.append({loc: {str(inv): cexs}})
            else:
                stat = (
                    infer.inv.Inv.PROVED if is_succ else infer.inv.Inv.UNKNOWN
                )
            inv.stat = stat
            mdinvs.setdefault(loc, infer.inv.Invs()).add(inv)

        return merge(mCexs), mdinvs

    def mcheck_d(self, loc: str,
                 inv: None | infer.inv.Inv | z3.ExprRef,
                 inps: None | data.traces.Inps,
                 ncexs: int) -> tuple[list, bool]:

        assert ncexs >= 1, ncexs

        try:
            inv_expr = inv.expr
            if inv_expr is Z3.zFalse:
                inv_expr = None
        except AttributeError:
            if z3.is_expr(inv):
                inv_expr = inv
            else:
                inv_expr = None

        cexs, is_succ = self.mcheck_depth(
            self[loc], inv, inv_expr, inps, ncexs)
        return cexs, is_succ
    
    def mcheck_depth(self, ssd: SymStatesDepth,
                     inv:infer.inv.Inv | None,
                     inv_expr: None | z3.BoolRef,
                     inps: None | data.traces.Inps,
                     ncexs:int ) -> tuple[list, bool]:
        # assert inv_expr is None or z3.is_expr(inv_expr), inv_expr

        def f(depth):
            ss = ssd[depth]
            if inv_expr is not None:
                # Substitute concrete symbolic snapshots before asking SMT
                # to prove a polynomial identity. Expansion can certify the
                # equality directly, including quotient/remainder identities
                # already normalized by the C execution engine.
                counterexample_paths = []
                for path in ss:
                    equations = (path.slocal.children() if z3.is_and(path.slocal)
                                 else [path.slocal])
                    bindings = [(eq.arg(0), eq.arg(1)) for eq in equations
                                if z3.is_eq(eq) and z3.is_const(eq.arg(0))]
                    claim = z3.simplify(z3.substitute(inv_expr, *bindings), som=True)
                    if not z3.is_true(claim):
                        # Keep the snapshot equalities so counterexample
                        # models still expose the observed program variables.
                        counterexample_paths.append(z3.And(path.pc, path.slocal,
                                                           z3.Not(claim)))
                if ss and not counterexample_paths:
                    return [], True, z3.unsat
                if counterexample_paths:
                    cexs, is_succ, stat = self.mcheck(z3.Or(counterexample_paths),
                                                     None, inps, ncexs)
                    return cexs, is_succ, stat
            ##ss = ss.mypc if inv_expr is None else ss.myexpr
            ss = ss.myexpr
            cexs, is_succ, stat = self.mcheck(ss, inv_expr, inps, ncexs)
            return cexs, is_succ, stat

        depths = sorted(ssd.keys())
        depth_idx = 0

        cexs, is_succ, stat = f(depths[depth_idx])

        nochanges = 0
        while (
                stat != z3.sat
                and nochanges <= settings.SE_DEPTH_NOCHANGES_MAX
                and depth_idx < len(depths) - 1
        ):
            depth_idx_ = depth_idx + 1
            cexs_, is_succ_, stat_ = f(depths[depth_idx_])
            if stat_ != stat:
                nochanges = 0

                mydepth_ = depths[depth_idx_]
                mydepth = depths[depth_idx]
                mlog.debug(
                    f"check depth diff {inv_expr}: "
                    f"{stat} @depth {mydepth}, {stat_} @depth {mydepth_}"
                )
            else:
                nochanges += 1

            depth_idx = depth_idx_
            cexs, is_succ, stat = cexs_, is_succ_, stat_

        return cexs, is_succ

    def mcheck(self, symstates_expr: z3.ExprRef,
               expr: None | z3.ExprRef,
               inps: None | data.traces.Inps,
               ncexs: int) -> tuple:
        """
        check if pathcond => expr
        if not, return cex
        return cexs, is_succ (if the solver does not timeout)
        """

        #assert inps is None or isinstance(inps, data.traces.Inps), inps
        assert ncexs >= 0, ncexs

        f = symstates_expr
        iconstr = self.get_inp_constrs(inps)
        if iconstr is not None:
            f = z3.simplify(z3.And(iconstr, f))

        if expr is not None:
            f = z3.Not(z3.Implies(f, expr))

        models, stat = Z3.get_models(f, ncexs)
        if isinstance(models, list):
            for model in models:
                for symbol in self.inp_exprs:
                    model.eval(symbol, model_completion=True)
        cexs, is_succ = Z3.extract(models, int)
        return cexs, is_succ, stat

    def maximize(self, loc:str, term_expr:z3.ExprRef, iupper: int) -> int | None:
        """
        maximize value of term using symstates
        Essentially computing convex hull
        """
        assert z3.is_expr(term_expr), term_expr

        v, stat = self.mmaximize_depth(loc, self[loc], term_expr, iupper)
        return v

    def mmaximize_depth(self, loc: str, ssd:SymStatesDepth ,
                        term_expr: z3.ExprRef,
                        iupper: int) -> tuple[int | None, z3.CheckSatResult]:


        def f(depth: int):
            # reuse one Optimize per (loc, depth) with the symbolic state
            # asserted once; each term just pushes its objective and pops.
            # avoids rebuilding+re-asserting ss for every one of the hundreds
            # of candidate terms maximized at this loc.
            opt = self._get_max_opt(loc, depth, ssd)
            opt.push()
            try:
                maxv, stat = self._solve_max(opt, term_expr, iupper)
            finally:
                opt.pop()
            return maxv, stat

        depths = sorted(ssd.keys())
        depth_idx = 0

        maxv, stat = f(depths[depth_idx])
        nochanges = 0
        changes = 0
        while (
                maxv is not None
                and changes <= settings.SE_DEPTH_NOCHANGES_MAX
                and nochanges <= settings.SE_DEPTH_NOCHANGES_MAX
                and depth_idx < len(depths) - 1
        ):

            depth_idx_ = depth_idx + 1
            maxv_, stat_ = f(depths[depth_idx_])

            if maxv_ is not None and maxv_ < maxv:
                maxv_ = maxv

            if maxv_ != maxv:
                nochanges = 0
                changes += 1
                mydepth_ = depths[depth_idx_]
                mydepth = depths[depth_idx]
                mlog.debug(
                    f"max depth diff {term_expr}: "
                    f"{maxv} {stat} @depth {mydepth}, "
                    f"{maxv_} {stat_} @depth {mydepth_}"
                )
            else:
                nochanges += 1

            depth_idx = depth_idx_
            maxv, stat = maxv_, stat_

        if maxv is not None and changes >= settings.SE_DEPTH_NOCHANGES_MAX:
            mlog.debug(f"value of {term_expr} changes frequently, skip")
            maxv = None

        return maxv, stat

    @staticmethod
    def _solve_max(opt: z3.Solver, term_expr: z3.ExprRef,
                   iupper: int) -> tuple[int | None, z3.CheckSatResult]:
        """
        Find a certified maximum in [-iupper, iupper] by bounded SAT search.

        Nonlinear Optimize can spend an unbounded time establishing an
        optimum even with a resource limit. Here every query is an ordinary
        bounded solver check. Unknown never supplies an upper-bound claim.
        Caller owns the outer push/pop scope.
        """
        def query(claim):
            opt.push()
            try:
                opt.add(claim)
                return opt.check()
            finally:
                opt.pop()

        stat = query(term_expr > iupper)
        if stat != z3.unsat:
            return None, stat
        stat = query(term_expr >= -iupper)
        if stat != z3.sat:
            return None, stat
        lower, upper = -iupper, iupper
        while lower < upper:
            middle = (lower+upper+1)//2
            stat = query(term_expr >= middle)
            if stat == z3.sat:
                lower = middle
            elif stat == z3.unsat:
                upper = middle-1
            else:
                return None, stat
        # Real-valued terms may have a fractional supremum. Certify the
        # integer upper bound rather than reporting the rounded-down value.
        stat = query(term_expr > lower)
        return (lower, z3.sat) if stat == z3.unsat else (None, stat)

    def _get_max_opt(self, loc: str, depth: int,
                     ssd: SymStatesDepth) -> z3.Solver:
        """
        Process-local cache of a Solver per (loc, depth) with the symbolic
        state asserted once. Built lazily so each forked MP worker populates
        its own cache (z3 objects must not cross the fork boundary).
        """
        cache = self.__dict__.setdefault("_max_opt_cache", {})
        key = (loc, depth)
        opt = cache.get(key)
        if opt is None:
            ss = self.get_symstates_at_depth(ssd, depth=depth)
            opt = Z3.create_solver(maximize=False)
            opt.add(ss)
            cache[key] = opt
        return opt

    # helpers
    @classmethod
    def get_symstates_at_depth(cls, ssd: SymStatesDepth, 
                        depth: None | int=None) -> z3.ExprRef:
        
        assert depth is None or depth >= 0, depth

        if depth is None:  # use all
            return z3.Or([ssd[depth].myexpr for depth in ssd])
        else:  # use up to depth
            ss = []
            for d in sorted(ssd):
                if d > depth:
                    break
                ss.append(ssd[d].myexpr)

            return z3.Or(ss)

    def get_inp_constrs(self, inps: None | data.traces.Inps) -> None | z3.ExprRef:
        cstrs = []
        if isinstance(inps, data.traces.Inps) and inps:
            inpCstrs = [inp.mk_expr(self.inp_exprs) for inp in inps]
            inpCstrs = [z3.Not(expr) for expr in inpCstrs if expr is not None]
            cstrs.extend(inpCstrs)

        if not cstrs:
            return None
        elif len(cstrs) == 1:
            return cstrs[0]
        else:
            return z3.And(cstrs)


class SymStatesMaker(abc.ABC):

    input_prefix = ""

    def __init__(self, 
                 filename: Path, 
                 mainQName: str, 
                 funname: str, 
                 ninps: int, 
                 tmpdir: Path) -> None:
        assert tmpdir.is_dir(), tmpdir

        self.filename = filename
        self.mainQName = mainQName
        self.funname = funname
        self.tmpdir = tmpdir
        self.ninps = ninps
        self.exploration_info = {}

    @property
    def maxdepth(self) -> int:
        return settings.SE_MAX_DEPTH

    def compute(self) -> dict:
        """
        Run symbolic execution to obtain symbolic states
        """

        mind = self.mindepth
        maxd = self.maxdepth
        if mind >= maxd:
            mlog.warning(f"symbolic execution: mindepth {mind} >= maxdepth {maxd}, "
                         f"setting mindepth=maxdepth={maxd}")
            mind = maxd
            
        tasks = list(range(mind, maxd + 1))

        # The Python symex engine builds z3 path conditions and we consume them
        # directly, so it runs in-process (no multiprocessing): z3 ASTs can't be
        # pickled across forked workers, and avoiding that boundary is the whole
        # point of returning z3 instead of serializing to text and re-parsing.
        wrs = [(depth, ss) for depth in tasks
               if (ss := self.get_symstates(depth))]

        if not wrs:
            mlog.fatal("symbolic execution cannot obtain symstates, unreachable locs?"
                       f" Or try increasing maxdepth using --se_maxdepth N (current N={maxd})")
            sys.exit(0)

        symstates = self.merge(wrs, self.pc_cls)
        for loc in symstates:
            for depth in symstates[loc]:
                mlog.debug(f"loc {loc} depth {depth} has "
                           f"{len(symstates[loc][depth])} uniq symstates")
        return symstates

    @abc.abstractmethod
    def get_symstates(self, depth: int) -> None | list:
        pass

    @classmethod
    def merge(cls, depthss: list, pc_cls) -> dict:
        """
        Merge PC's info into symstates sd[loc][depth]
        """
        assert depthss, depthss
        assert all(
            depth >= 1 and isinstance(ss, list) for depth, ss in depthss
        ), depthss

        # pc/slocal arrive as z3 expressions straight from the symex engine
        # (no text round-trip); just wrap them in the PathCond record.
        symstates: dict = {}
        for depth, ss in depthss:
            for (loc, pc, slocal) in ss:
                pcond = pc_cls(loc, pc, slocal)
                symstates.setdefault(loc, {}).setdefault(
                    depth, PCs(loc, depth)).add(pcond)

        # only store incremental states at each depth
        for loc in symstates:
            depths = sorted(symstates[loc])
            if len(depths) < 2:
                continue

            for i in range(len(depths)):
                iss = symstates[loc][depths[i]]
                for j in range(i):
                    jss = symstates[loc][depths[j]]
                    for s in jss:
                        if s in iss:
                            iss.remove(s)

        # clean up
        empties = [
            (loc, depth)
            for loc in symstates
            for depth in symstates[loc]
            if not symstates[loc][depth]
        ]
        for loc, depth in empties:
            mlog.debug(f"{loc}: no new symstates at depth {depth}")
            symstates[loc].pop(depth)

        empties = [loc for loc in symstates if not symstates[loc]]
        for loc in empties:
            mlog.warning(f"{loc}: no symstates found")
            symstates.pop(loc)

        if all(not symstates[loc] for loc in symstates):
            mlog.error("No symstates found for any locs. Exit!")
            sys.exit(0)

        return symstates


def merge(ds) -> dict:
    newD = {}
    for d in ds:
        for loc in d:
            assert d[loc]
            newD.setdefault(loc, {})
            for inv in d[loc]:
                assert d[loc][inv]
                newD[loc].setdefault(inv, [])
                for e in d[loc][inv]:
                    newD[loc][inv].append(e)
    return newD


class SymStatesMakerC(SymStatesMaker):
    """
    Python symbolic execution engine for simple C programs.
    Overrides get_symstates() to call CSymEx directly.
    """
    pc_cls = PathCondC
    input_prefix = "X_"
    # Python symex explores paths incrementally — a lower starting depth is fine.
    mindepth = 2

    def get_symstates(self, depth: int) -> None | list:
        assert depth >= 1, depth
        from data.symex_c import CSymEx
        mlog.debug(f"python symex: {self.filename} depth={depth}")
        try:
            engine = CSymEx(self.filename, depth,
                            solver_rlimit=settings.SOLVER_RLIMIT)
            results = engine.run()
            self.exploration_info[depth] = {"truncated": engine._incomplete,
                                            "records": len(results)}
        except Exception as ex:
            mlog.error(f"python symex failed at depth {depth}: {ex}")
            return None
        if results:
            mlog.debug(f"got {len(results)} symstates at depth {depth}")
        return results or None

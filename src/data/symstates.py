"""
Symbolic States
"""

from time import time
import sys
import shlex
from collections import defaultdict
from abc import ABCMeta
import pdb
from multiprocessing import Queue
from queue import Empty
import subprocess
import threading

import z3
from sage.all import cached_function, sage_eval
from typing import NamedTuple
import settings
import helpers.vcommon as CM
import helpers.miscs
from helpers.miscs import Z3
import data.prog
import data.traces
import data.inv.base
import data.inv.invs
import analysis

DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


class PathCondition(NamedTuple):
    loc: str
    pc: z3.ExprRef
    slocal: z3.ExprRef

    def __str__(self):
        return f"loc: {self.loc}\npc: {self.pc}\nslocal: {self.slocal}"

    @property
    def expr(self):
        return z3.simplify(z3.And(self.pc, self.slocal))

    @classmethod
    def parse(cls, s):
        assert isinstance(s, str), s

        parts = cls.parse_parts(s.splitlines())
        if not parts:
            return None

        pcs = [cls.parse_part(p) for p in parts]
        return pcs


class PC_CIVL(PathCondition):
    @classmethod
    def parse_parts(cls, lines):
        """
        vtrace1: q = 0; r = X_x; a = 0; b = 0; x = X_x; y = X_y
        path condition: (0<=(X_x-1))&&(0<=(X_y-1))
        vtrace3: x = X_x; y = X_y; r = X_x; q = 0
        path condition: ((X_x+(-1*X_y)+1)<=0)&&(0<=(X_x-1))&&(0<=(X_y-1))
        vtrace2: q = 0; r = X_x; a = 1; b = X_y; x = X_x; y = X_y
        path condition: (0<=(X_x+(-1*X_y)))&&(0<=(X_x-1))&&(0<=(X_y-1))
        """
        slocals = []
        pcs = []
        lines = [line.strip() for line in lines]
        lines = [line for line in lines if line]
        for line in lines:
            if line.startswith("vtrace"):
                slocals.append(line)
            elif line.startswith("path condition"):
                assert len(pcs) == len(slocals) - 1
                pcs.append(line)

        parts = [[slocal, pc] for slocal, pc in zip(slocals, pcs)]
        return parts

    @classmethod
    def parse_part(cls, ss):
        """
        ['vtrace1: q = 0; r = X_x; a = 0; b = 0; x = X_x; y = X_y',
        'path condition: (0<=(X_x-1))&&(0<=(X_y-1))']
        """
        assert isinstance(ss, list) and len(ss) == 2, ss
        slocal, pc = ss
        pc = pc.split(":")[1].strip()  # path condition: ...
        pc = None if pc == "true" else cls.replace_str(pc)
        loc, slocal = slocal.split(":")
        slocal = cls.replace_str(slocal)

        assert pc is None or len(pc) >= 1
        assert slocal
        return loc, pc, slocal

    @staticmethod
    def replace_str(s):
        return (
            s.replace(" = ", " == ")
            .replace(";", " and ")
            .replace("&&", "and")
            .replace("||", "or")
            .replace("div ", "/ ")
            .replace("^", "**")
            .strip()
        )


class PC_JPF(PathCondition):
    @classmethod
    def parse_parts(cls, lines, delim="**********"):
        """
        Return a list of strings representing path conditions
        [['loc: vtrace1(IIIIII)V',
        'pc: constraint # = 2',
        'y_2_SYMINT >= CONST_1 &&', 'x_1_SYMINT >= CONST_1',
        'vars: int x, int y, int q, int r, int a, int b,',
        'SYM: x = x_1_SYMINT',
        'SYM: y = y_2_SYMINT',
        'CON: q = 0',
        'SYM: r = x_1_SYMINT',
        'CON: a = 0',
        'CON: b = 0']]
        """
        parts, curpart = [], []

        start = delim + " START"
        end = delim + " END"
        do_append = False

        lines = [line.strip() for line in lines]
        lines = [line for line in lines if line]
        for line in lines:
            if line.startswith(start):
                do_append = True
                continue
            elif line.startswith(end):
                do_append = False
                if curpart:
                    parts.append(curpart)
                    curpart = []
            else:
                if do_append:
                    curpart.append(line)

        return parts

    @classmethod
    def parse_part(cls, ss):
        """
        vtrace1
        [('int', 'x'), ('int', 'y'), ('int', 'q'),
          ('int', 'r'), ('int', 'a'), ('int', 'b')]
        ['y_2_SYMINT >= 1', 'x_1_SYMINT >= 1']
        ['x==x_1_SYMINT', 'y==y_2_SYMINT', 'q==0', 'r==x_1_SYMINT', 'a==0', 'b==0']
        """

        assert isinstance(ss, list) and ss, ss
        loc = None
        pcs = []

        curpart = []
        for s in ss:
            if "loc: " in s:
                loc = s.split()[1]  # e.g., vtrace30(I)V
                loc = loc.split("(")[0]  # vtrace30
                continue
            elif "vars: " in s:
                pcs = curpart[1:]  # ignore pc constraint #
                curpart = []
                continue
            curpart.append(s)
        slocals = curpart[:]
        assert loc, loc

        slocals = [cls.replace_str(p) for p in slocals if p and not cls.too_large(p)]
        slocals = " and ".join(slocals) if slocals else None
        pcs = [cls.replace_str(pc) for pc in pcs if pc]
        pcs = " and ".join(pcs) if pcs else None

        return loc, pcs, slocals

    @staticmethod
    @cached_function
    def too_large(p):
        return False
        # if "CON:" not in p:
        #     return False

        # ps = p.split("=")
        # assert len(ps) == 2
        # v = sage_eval(ps[1])
        # if helpers.miscs.Miscs.is_num(v) and v >= settings.LARGE_N:
        #     mlog.warning(f"ignore {p} (larger than {settings.LARGE_N})")
        #     return True
        # else:
        #     return False

    @staticmethod
    @cached_function
    def replace_str(s):
        return (
            s.replace("&&", "")
            .replace(" = ", "==")
            .replace("CONST_", "")
            .replace("REAL_", "")
            .replace("%NonLinInteger%", "")
            .replace("SYM:", "")
            .replace("CON:", "")
            .strip()
        )


class PCs(set):
    def __init__(self, loc, depth):
        assert isinstance(loc, str), loc
        assert depth >= 1, depth

        super().__init__(set())
        self.loc = loc
        self.depth = depth

    def add(self, pc):
        assert isinstance(pc, PathCondition), pc
        super().add(pc)

    @property
    def myexpr(self):
        try:
            return self._expr
        except AttributeError:
            _expr = z3.Or([p.expr for p in self])
            self._expr = Z3.simplify(_expr)
            return self._expr

    @property
    def mypc(self):
        try:
            return self._pc
        except AttributeError:
            _pc = z3.Or([p.pc for p in self])
            self._pc = Z3.simplify(_pc)
            return self._pc



EXPR_MAPPER = {
    # For HOLA H32
    # TODO: Don't need this in Python 3.8
    # 'j==((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((j_1_SYMINT + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) and i==((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((j_1_SYMINT + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) and k==100 and b==0 and n==200':
    #     'j==(j_1_SYMINT + 100) and i==(j_1_SYMINT + 100) and k==100 and b==0 and n==200'
}


class SymStatesMaker(metaclass=ABCMeta):
    def __init__(self, filename, mainQName, funname, ninps, tmpdir):
        assert tmpdir.is_dir(), tmpdir

        self.filename = filename
        self.mainQName = mainQName
        self.funname = funname
        self.tmpdir = tmpdir
        self.ninps = ninps

    def compute(self):
        """
        Run symbolic execution to obtain symbolic states
        """
        tasks = [depth for depth in range(self.mindepth, settings.SE_MAXDEPTH + 1)]

        def f(tasks):
            rs = [(depth, self.get_ss(depth)) for depth in tasks]
            rs = [(depth, ss) for depth, ss in rs if ss]
            return rs

        wrs = helpers.miscs.Miscs.run_mp("get symstates", tasks, f)

        if not wrs:
            mlog.warning("cannot obtain symbolic states, unreachable locs?")
            sys.exit(0)

        symstates = self.merge(wrs, self.pc_cls)
        # symstates = self.merge2(wrs)

        # precompute all z3 exprs
        tasks = [(loc, depth) for loc in symstates for depth in symstates[loc]]

        def f(tasks):
            rs = [symstates[loc][depth] for loc, depth in tasks]
            rs = [
                (loc, depth, Z3.to_smt2_str(pcs.myexpr), Z3.to_smt2_str(pcs.mypc))
                for pcs, (loc, depth) in zip(rs, tasks)
            ]
            return rs

        wrs = helpers.miscs.Miscs.run_mp("symstates exprs", tasks, f)
        for loc, depth, myexpr, mypc in sorted(wrs, key=lambda ts: (ts[0], ts[1])):
            pcs = symstates[loc][depth]
            pcs._expr = Z3.from_smt2_str(myexpr)
            pcs._pc = Z3.from_smt2_str(mypc)
            mlog.debug(f"loc {loc} depth {depth} has {len(pcs)} uniq symstates")
        return symstates

    def get_ss(self, depth):
        assert depth >= 1, depth

        cmd = self.mk(depth)
        timeout = depth
        mlog.debug(f"Obtain symbolic states at depth {depth} (timeout {timeout}s)")
        mlog.debug(cmd)

        s = None
        try:
            cp = subprocess.run(
                shlex.split(cmd),
                timeout=timeout,
                capture_output=True,
                check=True,
                text=True,
            )
            s = cp.stdout
        except subprocess.TimeoutExpired as ex:
            mlog.debug(
                f"{ex.__class__.__name__}: {' '.join(ex.cmd)} "
                f"time out after {ex.timeout}s"
            )
            s = ex.stdout

        except subprocess.CalledProcessError as ex:
            mlog.warning(ex)
            return None

        pcs = self.pc_cls.parse(s)
        return pcs

    # @classmethod
    # def get_uniq_ss(cls, loc, depth, symstates):
    #     pcs = list(symstates[loc][depth])
    #     for loc_ in symstates:
    #         if loc != loc:
    #             continue
    #         for depth_ in symstates[loc]:
    #             if depth_ >= depth:
    #                 continue
    #             otherpcs = symstates[loc][depth_]
    #             assert isinstance(otherpcs, PCs)
    #             pcs = [pc for pc in pcs if pc not in otherpcs]

    #     pcs = PCs(loc, depth)
    #     for pc in pcs:
    #         pcs.add(pc)
    #     return pcs

    @classmethod
    def merge(cls, depthss, pc_cls):
        """
        Merge PC's info into symbolic states sd[loc][depth]
        """
        assert isinstance(depthss, list) and depthss, depthss
        assert all(
            depth >= 1 and isinstance(ss, list) for depth, ss in depthss
        ), depthss

        @cached_function
        def zpc(p):
            return Z3.zTrue if p is None else Z3.parse(p)

        @cached_function
        def zslocal(p):
            return Z3.parse(p)

        symstates = defaultdict(lambda: defaultdict(lambda: PCs(loc, depth)))
        for depth, ss in depthss:
            for (loc, pcs, slocals) in ss:
                slocals = EXPR_MAPPER.get(slocals, slocals)
                try:
                    pc = pc_cls(loc, zpc(pcs), zslocal(slocals))
                    symstates[loc][depth].add(pc)
                except MemoryError:
                    mlog.error(f"cannot parse pcs {pcs}")
                    mlog.error(f"cannot parse slocals {slocals}")

        # only store incremental states at each depth
        for loc in symstates:
            depths = sorted(symstates[loc])
            assert len(depths) >= 2, depths
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
            mlog.debug(f"{loc}: no new symbolic states at depth {depth}")
            symstates[loc].pop(depth)

        empties = [loc for loc in symstates if not symstates[loc]]
        for loc in empties:
            mlog.warning(f"{loc}: no symbolic states found")
            symstates.pop(loc)

        if all(not symstates[loc] for loc in symstates):
            mlog.error("No symbolic states found for any locs. Exit!")
            sys.exit(1)

        return symstates


def merge(ds):
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
    pc_cls = PC_CIVL
    mindepth = settings.C.SE_MIN_DEPTH

    def mk(self, depth):
        """
        civl verify -maxdepth=20 -seed=10 /var/tmp/Dig_04lfhmlz/cohendiv.c
        """
        return settings.C.CIVL_RUN(maxdepth=depth, file=self.filename)


class SymStatesMakerJava(SymStatesMaker):
    pc_cls = PC_JPF
    mindepth = settings.Java.SE_MIN_DEPTH

    def mk(self, depth):
        max_val = settings.INP_MAX_V
        return settings.Java.JPF_RUN(jpffile=self.mk_JPF_runfile(max_val, depth))

    def mk_JPF_runfile(self, max_int, depth):
        assert max_int >= 0, max_int

        symargs = ["sym"] * self.ninps
        symargs = "#".join(symargs)
        stmts = [
            f"target={self.funname}",
            f"classpath={self.tmpdir}",
            f"symbolic.method={self.funname}.{self.mainQName}({symargs})",
            "listener=gov.nasa.jpf.symbc.InvariantListenerVu",
            "vm.storage.class=nil",
            "search.multiple_errors=true",
            f"symbolic.min_int={-max_int}",
            f"symbolic.max_int={max_int}",
            f"symbolic.min_long={-max_int}",
            f"symbolic.max_long={max_int}",
            f"symbolic.min_short={-max_int}",
            f"symbolic.max_short={max_int}",
            f"symbolic.min_float={-max_int}.0f",
            f"symbolic.max_float={max_int}.0f",
            f"symbolic.min_double={-max_int}.0",
            f"symbolic.max_double={max_int}.0",
            "symbolic.dp=z3bitvector",
            f"search.depth_limit={depth}",
        ]
        contents = "\n".join(stmts)

        filename = self.tmpdir / f"{self.funname}_{max_int}_{depth}.jpf"

        assert not filename.is_file(), filename
        CM.vwrite(filename, contents)
        return filename


class SymStatesDepth(dict):  # depth -> PCs
    pass


class SymStates(dict):
    # loc -> SymStatesDepth

    def __init__(self, inp_decls, inv_decls):
        self.inp_decls = inp_decls
        self.inv_decls = inv_decls
        self.inp_exprs = inp_decls.exprs

        self.solver_stats = Queue() if settings.DO_SOLVER_STATS else None
        self.solver_stats_ = []  # periodically save solver_stats results here

        super().__init__(dict())

    def compute(self, symstatesmaker_cls, filename, mainQName, funname, tmpdir):
        symstatesmaker = symstatesmaker_cls(
            filename, mainQName, funname, len(self.inp_decls), tmpdir
        )
        ss = symstatesmaker.compute()
        for loc in ss:
            self[loc] = SymStatesDepth(ss[loc])

    # Checking invariants using symbolic states

    def check(self, dinvs, inps):
        """
        Check invs, return cexs
        Also update inps
        """
        assert isinstance(dinvs, data.inv.invs.DInvs), dinvs
        assert not inps or (isinstance(inps, data.traces.Inps) and inps), inps

        mlog.debug(f"checking {dinvs.siz} invs:\n" f"{dinvs.__str__(print_first_n=20)}")
        tasks = [(loc, inv) for loc in dinvs for inv in dinvs[loc] if inv.stat is None]
        refsD = {(loc, str(inv)): inv for loc, inv in tasks}

        def f(tasks):
            return [
                (loc, str(inv), self.mcheck_d(loc, inv, inps, ncexs=1))
                for loc, inv in tasks
            ]

        wrs = helpers.miscs.Miscs.run_mp("prove", tasks, f)

        mCexs = []
        mdinvs = data.inv.invs.DInvs()
        for loc, str_inv, (cexs, is_succ) in wrs:
            inv = refsD[(loc, str_inv)]

            if cexs:
                stat = data.inv.base.Inv.DISPROVED
                mCexs.append({loc: {str(inv): cexs}})
            else:
                stat = (
                    data.inv.base.Inv.PROVED if is_succ else data.inv.base.Inv.UNKNOWN
                )
            inv.stat = stat
            mdinvs.setdefault(loc, data.inv.invs.Invs()).add(inv)

        return merge(mCexs), mdinvs

    def mcheck_d(self, loc, inv, inps, ncexs):
        assert isinstance(loc, str), loc
        assert inv is None or isinstance(inv, data.inv.base.Inv) or z3.is_expr(inv), inv
        assert inps is None or isinstance(inps, data.traces.Inps), inps
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

        if settings.DO_INCR_DEPTH:
            cexs, is_succ = self.mcheck_depth(self[loc], inv, inv_expr, inps, ncexs)
        else:
            cexs, is_succ, stat = self.mcheck(
                self.get_ss_at_depth(self[loc], depth=None), inv_expr, inps, ncexs
            )

        return cexs, is_succ

    def mcheck_depth(self, ssd, inv, inv_expr, inps, ncexs):
        assert inv_expr is None or z3.is_expr(inv_expr), inv_expr
        assert isinstance(ssd, SymStatesDepth), ssd  # self.ss[loc]

        def f(depth):
            ss = ssd[depth]
            ss = ss.mypc if inv_expr is None else ss.myexpr
            cexs, is_succ, stat = self.mcheck(ss, inv_expr, inps, ncexs)
            self.put_solver_stats(analysis.CheckSolverCalls(stat))
            return cexs, is_succ, stat

        depths = sorted(ssd.keys())
        depth_idx = 0

        cexs, is_succ, stat = f(depths[depth_idx])
        if stat != z3.unsat:  # if disprove (sat) or unknown first time
            self.put_solver_stats(
                analysis.CheckDepthChanges(
                    str(inv), None, None, stat, depths[depth_idx]
                )
            )

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
                self.put_solver_stats(
                    analysis.CheckDepthChanges(str(inv), stat, mydepth, stat_, mydepth_)
                )
            else:
                nochanges += 1

            depth_idx = depth_idx_
            cexs, is_succ, stat = cexs_, is_succ_, stat_

        return cexs, is_succ

    def mcheck(self, symstates_expr, expr, inps, ncexs):
        """
        check if pathcond => expr
        if not, return cex
        return cexs, is_succ (if the solver does not timeout)
        """
        assert z3.is_expr(symstates_expr), symstates_expr
        assert expr is None or z3.is_expr(expr), expr
        assert inps is None or isinstance(inps, data.traces.Inps), inps
        assert ncexs >= 0, ncexs

        f = symstates_expr
        iconstr = self.get_inp_constrs(inps)
        if iconstr is not None:
            f = z3.simplify(z3.And(iconstr, f))

        if expr is not None:
            f = z3.Not(z3.Implies(f, expr))

        models, stat = Z3.get_models(f, ncexs)
        cexs, is_succ = Z3.extract(models)
        return cexs, is_succ, stat

    # Find maximal values for term using symbolic states
    def maximize(self, loc, term_expr, iupper, extra_constr=None):
        """
        maximize value of term
        """
        assert z3.is_expr(term_expr), term_expr
        assert extra_constr is None or z3.is_expr(extra_constr), extra_constr

        if settings.DO_INCR_DEPTH:
            v, stat = self.mmaximize_depth(self[loc], term_expr, iupper, extra_constr)
        else:
            v, stat = self.mmaximize(
                self.get_ss_at_depth(self[loc], depth=None), term_expr, iupper
            )
        return v

    def mmaximize_depth(self, ssd, term_expr, iupper, extra_constr):
        assert isinstance(ssd, SymStatesDepth), ssd
        assert z3.is_expr(term_expr), term_expr
        assert extra_constr is None or z3.is_expr(extra_constr), extra_constr

        def f(depth):
            ss = self.get_ss_at_depth(ssd, depth=depth)
            if extra_constr is not None:
                ss = z3.And(ss, extra_constr)
            maxv, stat = self.mmaximize(ss, term_expr, iupper)
            self.put_solver_stats(analysis.MaxSolverCalls(stat))
            return maxv, stat

        depths = sorted(ssd.keys())
        depth_idx = 0

        maxv, stat = f(depths[depth_idx])
        if maxv is not None:  # if changed
            self.put_solver_stats(
                analysis.MaxDepthChanges(
                    str(term_expr), None, None, maxv, depths[depth_idx]
                )
            )
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
                # if (max_ is int and maxv is int) then maxv_ > maxv
                # assert(not(isinstance(maxv_, int) and isinstance(maxv, int))
                # or (maxv_ > maxv)), (maxv_, maxv)

                mydepth_ = depths[depth_idx_]
                mydepth = depths[depth_idx]
                mlog.debug(
                    f"max depth diff {term_expr}: "
                    f"{maxv} {stat} @depth {mydepth}, "
                    f"{maxv_} {stat_} @depth {mydepth_}"
                )
                self.put_solver_stats(
                    analysis.MaxDepthChanges(
                        str(term_expr), maxv, mydepth, maxv_, mydepth_
                    )
                )
            else:
                nochanges += 1
                # changes = 0 # yes, this is intentional

            depth_idx = depth_idx_
            maxv, stat = maxv_, stat_

        if maxv is not None and changes >= settings.SE_DEPTH_NOCHANGES_MAX:
            mlog.warning(f"value of {term_expr} changes frequently, skip")
            maxv = None

        return maxv, stat

    def mmaximize(self, ss, term_expr, iupper):
        assert z3.is_expr(ss), ss
        assert z3.is_expr(term_expr), term_expr
        assert isinstance(iupper, int) and iupper >= 1, iupper

        opt = Z3.create_solver(maximize=True)
        opt.add(ss)
        h = opt.maximize(term_expr)
        try:
            stat = opt.check()
        except Exception as ex:
            mlog.error(f"maximize: {ex} {term_expr}")
            stat = z3.unknown

        assert stat == z3.sat or stat == z3.unknown, stat
        v = None
        if stat == z3.sat:
            v = str(opt.upper(h))
            if v != "oo":  # no bound
                try:
                    v = int(v)
                    if abs(v) <= iupper:
                        return v, stat
                except ValueError:  # invalid literal for 3/4
                    pass

        return None, stat

    # helpers

    def get_ss_at_depth(self, ssd, depth=None):
        assert isinstance(ssd, SymStatesDepth), ssd

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

    def get_inp_constrs(self, inps):
        cstrs = []
        if isinstance(inps, data.traces.Inps) and inps:
            inpCstrs = [inp.mkExpr(self.inp_exprs) for inp in inps]
            inpCstrs = [z3.Not(expr) for expr in inpCstrs if expr is not None]
            cstrs.extend(inpCstrs)

        if not cstrs:
            return None
        elif len(cstrs) == 1:
            return cstrs[0]
        else:
            return z3.And(cstrs)

    def put_solver_stats(self, e):
        if self.solver_stats is not None:
            self.solver_stats.put(e, block=True)

    def get_solver_stats(self):
        if self.solver_stats is not None:
            while True:
                try:
                    stat = self.solver_stats.get(block=False)
                    self.solver_stats_.append(stat)
                except Empty:
                    break
                except:
                    mlog.exception(f"get_solver_stats() error")
                    break

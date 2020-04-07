"""
Symbolic States
"""
from collections import defaultdict
from abc import ABCMeta, abstractmethod
import pdb
from pathlib import Path

import z3
import sage.all
from sage.all import cached_function

import settings
import helpers.vcommon as CM
import helpers.miscs
import data.prog
import data.traces
import data.inv.base
import data.inv.invs

DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)

zTrue = z3.BoolVal(True)
zFalse = z3.BoolVal(False)


class PC(metaclass=ABCMeta):
    def __init__(self, loc, depth, pc, slocal, use_reals):
        assert isinstance(loc, str) and loc, loc
        assert depth >= 0, depth
        assert pc is None or isinstance(pc, str) and pc, pc
        assert isinstance(slocal, str) and slocal, slocal
        assert isinstance(use_reals, bool), bool

        self.pc = zTrue if pc is None else helpers.miscs.Z3.parse(
            pc, use_reals)
        self.slocal = helpers.miscs.Z3.parse(slocal, use_reals)
        self.loc = loc
        self.depth = depth
        self.use_reals = use_reals

    def __str__(self):
        return 'loc: {}\npc: {}\nslocal: {}'.format(
            self.loc, self.pc, self.slocal)

    def __eq__(self, other):
        return isinstance(other, self.__class__) and hash(self) == hash(other)

    def __hash__(self):
        return hash(self.__str__())

    @property
    def expr(self):
        return z3.simplify(z3.And(self.pc, self.slocal))

    @classmethod
    def parse(cls, filename):
        parts = cls.parse_parts(filename.read_text().splitlines())
        if not parts:
            mlog.error("Cannot obtain symstates from '{}'".format(filename))
            return None

        pcs = [cls.parse_part(p) for p in parts]
        return pcs


class PC_CIVL(PC):

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
        lines = [l.strip() for l in lines]
        lines = [l for l in lines if l]
        for l in lines:
            if l.startswith('vtrace'):
                slocals.append(l)
            elif l.startswith('path condition'):
                assert len(pcs) == len(slocals) - 1
                pcs.append(l)

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
        pc = pc.split(':')[1].strip()  # path condition: ...
        pc = None if pc == 'true' else cls.replace_str(pc)
        loc, slocal = slocal.split(':')
        slocal = cls.replace_str(slocal)

        assert pc is None or len(pc) >= 1
        assert slocal
        return loc, pc, slocal

    @staticmethod
    def replace_str(s):
        return (s.
                replace(' = ', ' == ').
                replace(';', ' and ').
                replace('&&', 'and').
                replace('||', 'or').
                replace('div ', '/ ').
                replace('^', '**').
                strip())


class PC_JPF(PC):

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

        lines = [l.strip() for l in lines]
        lines = [l for l in lines if l]
        for l in lines:
            if l.startswith(start):
                do_append = True
                continue
            elif l.startswith(end):
                do_append = False
                if curpart:
                    parts.append(curpart)
                    curpart = []
            else:
                if do_append:
                    curpart.append(l)

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

        curpart = []
        for s in ss:
            if 'loc: ' in s:
                loc = s.split()[1]  # e.g., vtrace30(I)V
                loc = loc.split('(')[0]  # vtrace30
                continue
            elif 'vars: ' in s:
                pcs = curpart[1:]  # ignore pc constraint #
                curpart = []
                continue
            curpart.append(s)

        slocals = curpart[:]

        # some clean up
        def isTooLarge(p):
            if 'CON:' not in p:
                return False

            ps = p.split('=')
            assert len(ps) == 2
            v = sage.all.sage_eval(ps[1])
            if helpers.miscs.Miscs.is_num(v) and v >= settings.LARGE_N:
                mlog.warning("ignore {} (larger than {})".format(
                    p, settings.LARGE_N))
                exit(-1)
                return True
            else:
                return False

        slocals = [p for p in slocals if not isTooLarge(p)]
        slocals = [cls.replace_str(p) for p in slocals if p]
        slocal = ' and '.join(slocals) if slocals else None
        pcs = [cls.replace_str(pc) for pc in pcs if pc]
        pc = ' and '.join(pcs) if pcs else None

        return loc, pc, slocal

    @staticmethod
    @cached_function
    def replace_str(s):
        return (s.replace('&&', '').
                replace(' = ', '==').
                replace('CONST_', '').
                replace('REAL_', '').
                replace('%NonLinInteger%', '').
                replace('SYM:', '').
                replace('CON:', '').
                strip())


class PCs(set):
    def __init__(self, loc, depth):
        assert isinstance(loc, str), loc
        assert depth >= 1, depth

        super().__init__(set())
        self.loc = loc
        self.depth = depth

    def add(self, pc):
        assert isinstance(pc, PC), pc
        super().add(pc)

    @property
    def myexpr(self):
        try:
            return self._expr
        except AttributeError:
            _expr = z3.Or([p.expr for p in self])
            self._expr = helpers.miscs.Z3.simplify(_expr)
            return self._expr

    @property
    def mypc(self):
        try:
            return self._pc
        except AttributeError:
            _pc = z3.Or([p.pc for p in self])
            self._pc = helpers.miscs.Z3.simplify(_pc)
            return self._pc


class SymStates(metaclass=ABCMeta):

    check_validity = 1  # sat(not(ss => f))
    check_consistency = 2  # sat(ss && f)

    def __init__(self, inp_decls, inv_decls, seed=None):
        assert isinstance(inp_decls, data.prog.Symbs), inp_decls  # I x, I y
        # {'vtrace1': (('q', 'I'), ('r', 'I'), ('x', 'I'), ('y', 'I'))}
        assert isinstance(inv_decls, data.prog.DSymbs), inv_decls

        self.inp_decls = inp_decls
        self.inv_decls = inv_decls
        self.use_reals = inv_decls.use_reals
        self.inp_exprs = inp_decls.exprs(self.use_reals)
        self.seed = seed if seed else 0

    def compute(self, filename, mainQName, funname, tmpdir):
        """
        Run symbolic execution to obtain symbolic states
        """
        assert tmpdir.is_dir(), tmpdir

        def _f(d):
            return self.mk(
                d, filename, mainQName, funname, tmpdir, len(self.inp_decls))

        tasks = [depth for depth in range(self.mindepth, self.maxdepth+1)]

        def f(tasks):
            rs = [(depth, _f(depth)) for depth in tasks]
            rs = [(depth, ss) for depth, ss in rs if ss]
            return rs

        wrs = helpers.miscs.Miscs.run_mp("get symstates", tasks, f)

        if not wrs:
            mlog.warning("cannot obtain symbolic states, unreachable locs?")
            import sys
            sys.exit(0)

        self.ss = self.merge(wrs, self.pc_cls, self.use_reals)

    @classmethod
    def merge(cls, depthss, pc_cls, use_reals):
        """
        Merge PC's info into symbolic states sd[loc][depth]
        """
        assert isinstance(depthss, list) and depthss, depthss
        assert all(depth >= 1 and isinstance(ss, list)
                   for depth, ss in depthss), depthss

        symstates = defaultdict(lambda: defaultdict(lambda: PCs(loc, depth)))
        for depth, ss in depthss:
            for (loc, pcs, slocals) in ss:
                pc = pc_cls(loc, depth, pcs, slocals, use_reals)
                # symstates.setdefault(loc, {})
                # symstates[loc] =
                # symstates[loc].setdefault(depth, PCs(loc, depth)).add(pc)
                symstates[loc][depth].add(pc)

        # only store incremental states at each depth
        for loc in symstates:
            depths = sorted(symstates[loc])
            assert len(depths) >= 2, depths
            for i in range(len(depths)):
                if i == 0:
                    pass
                iss = symstates[loc][depths[i]]
                for j in range(i):
                    jss = symstates[loc][depths[j]]
                    assert jss.issubset(iss)
                    assert len(jss) <= len(iss), (len(jss), len(iss))

                # only keep diffs
                for j in range(i):
                    jss = symstates[loc][depths[j]]
                    for s in jss:
                        assert s in iss, s
                        iss.remove(s)

        # clean up
        empties = [(loc, depth) for loc in symstates
                   for depth in symstates[loc] if not symstates[loc][depth]]
        for loc, depth in empties:
            mlog.warning(
                "{}: no symbolic states at depth {}".format(loc, depth))
            symstates[loc].pop(depth)

        empties = [loc for loc in symstates if not symstates[loc]]
        for loc in empties:
            mlog.warning("{}: no symbolic states found".format(loc))
            symstates.pop(loc)

        if all(not symstates[loc] for loc in symstates):
            mlog.error("No symbolic states found for any locs. Exit!")
            exit(1)

        # compute the z3 exprs once
        for loc in symstates:
            for depth in sorted(symstates[loc]):
                pcs = symstates[loc][depth]
                pcs.myexpr
                pcs.mypc
                mlog.debug("{} uniq symstates at loc {} depth {}".format(
                    len(pcs), loc, depth))
                # print(pcs.myexpr)

        return symstates

    def maximize(self, loc, term_expr):
        """
        maximize value of term
        """
        assert z3.is_expr(term_expr)

        opt = helpers.miscs.Z3.create_solver(maximize=True)
        opt.add(self.ss_at_loc(loc))
        h = opt.maximize(term_expr)
        stat = opt.check()

        if stat == z3.sat:
            v = str(opt.upper(h))
            if v != 'oo':  # no bound
                v = int(v)
                if v <= settings.OCT_MAX_V:
                    return v
        else:
            mlog.warning(
                "cannot find upperbound for {} at {} (stat {})".format(term_expr, loc, stat))

        return None

    def check(self, dinvs, inps, check_mode):
        """
        Check invs, return cexs
        Also update inps
        """
        assert isinstance(dinvs, data.inv.invs.DInvs), dinvs
        assert not inps or (isinstance(inps, data.traces.Inps) and inps), inps
        assert self.check_check_mode(check_mode), check_mode

        mlog.debug("checking {} invs:\n{}".format(
            dinvs.siz, dinvs.__str__(print_first_n=20)))
        tasks = [(loc, inv) for loc in dinvs for inv in dinvs[loc]
                 if inv.stat is None]
        refsD = {(loc, str(inv)): inv for loc, inv in tasks}

        def f(tasks):
            return [(loc, str(inv),
                     self.mcheck_d(loc, inv, inps,
                                   ncexs=1, check_mode=check_mode))
                    for loc, inv in tasks]
        wrs = helpers.miscs.Miscs.run_mp("prove", tasks, f)

        mCexs = []
        mdinvs = data.inv.invs.DInvs()
        mstats = []
        for loc, str_inv, (cexs, is_succ, solver_stats) in wrs:
            inv = refsD[(loc, str_inv)]

            if cexs:
                stat = data.inv.base.Inv.DISPROVED
                mCexs.append({loc: {str(inv): cexs}})
            else:
                stat = data.inv.base.Inv.PROVED if is_succ else data.inv.base.Inv.UNKNOWN
            inv.stat = stat
            mdinvs.setdefault(loc, data.inv.invs.Invs()).add(inv)

            mstats.extend(solver_stats)

        return merge(mCexs), mdinvs, mstats

    def ss_at_loc(self, loc):
        return z3.Or([self.ss[loc][depth].myexpr for depth in self.ss[loc]])

    # PRIVATE

    def mcheck_d(self, loc, inv, inps, ncexs, check_mode):

        assert isinstance(loc, str), loc
        assert inv is None or \
            isinstance(inv, data.inv.base.Inv) or \
            z3.is_expr(inv), (inv, type(inv))

        assert inps is None or isinstance(inps, data.traces.Inps), inps
        assert self.check_check_mode(check_mode), check_mode
        assert ncexs >= 1, ncexs

        try:
            inv_expr = inv.expr(self.use_reals)
            if inv_expr is zFalse:
                inv_expr = None
        except AttributeError:
            if z3.is_expr(inv):
                inv_expr = inv
                assert inv_expr is not None, inv_expr
            else:
                inv_expr = None

        if check_mode == self.check_validity:
            return self.mcheck_depth(loc, inv, inv_expr, inps, ncexs, check_mode)
        else:
            return self.mcheck_all(loc, inv_expr)

    def mcheck_all(self, loc, inv_expr):
        assert z3.is_expr(inv_expr) and inv_expr is not zFalse, inv_expr

        cexs, is_succ, stat = self.mcheck(
            self.ss_at_loc(loc), inv_expr,
            inps=None, ncexs=1, check_mode=self.check_consistency)

        return cexs, is_succ, []

    def mcheck_depth(self, loc, inv, inv_expr, inps, ncexs, check_mode):
        assert inv_expr is None or z3.is_expr(inv_expr), inv_expr

        solver_stats = []

        def f(depth):
            ss = self.ss[loc][depth]
            ss = ss.mypc if inv_expr is None else ss.myexpr
            cexs, is_succ, stat = self.mcheck(
                ss, inv_expr, inps, ncexs, check_mode)
            solver_stats.append((stat, is_succ))
            return cexs, is_succ, stat

        depths = sorted(self.ss[loc].keys())
        depth_idx = 0

        cexs, is_succ, stat = f(depths[depth_idx])
        if stat != z3.unsat:  # if disprove or unknown first time
            solver_stats.append((inv, None, None, stat, depths[depth_idx]))

        while(stat != z3.sat and depth_idx < len(depths) - 1):
            depth_idx_ = depth_idx + 1
            cexs_, is_succ_, stat_ = f(depths[depth_idx_])
            if stat_ != stat:
                mydepth_ = depths[depth_idx_]
                mydepth = depths[depth_idx]
                mlog.debug("depth diff {}: {} @ depth {}, {} @ depth {}"
                           .format(inv_expr, stat, mydepth, stat_, mydepth_))
                solver_stats.append((inv, stat, mydepth, stat_, mydepth_))

            depth_idx = depth_idx_
            cexs, is_succ, stat = cexs_, is_succ_, stat_

        return cexs, is_succ, solver_stats

    def mcheck(self, symstates_expr, inv, inps, ncexs, check_mode):
        """
        check if pathcond => inv
        if not, return cex
        return cexs, is_succ (if the solver does not timeout)
        """
        assert z3.is_expr(symstates_expr), symstates_expr
        assert inv is None or z3.is_expr(inv), inv
        assert inps is None or isinstance(inps, data.traces.Inps), inps
        assert ncexs >= 0, ncexs
        assert self.check_check_mode(check_mode), check_mode

        f = symstates_expr
        iconstr = self._get_inp_constrs(inps)
        if iconstr is not None:
            f = z3.simplify(z3.And(iconstr, f))

        if inv is not None:
            if check_mode == self.check_consistency:
                f = z3.And(f, inv)
            else:
                assert check_mode == self.check_validity, check_mode
                f = z3.Not(z3.Implies(f, inv))

        models, stat = helpers.miscs.Z3.get_models(f, ncexs)
        cexs, is_succ = helpers.miscs.Z3.extract(models)
        return cexs, is_succ, stat

    def _get_inp_constrs(self, inps):
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

    def check_check_mode(self, check_mode):
        return (isinstance(check_mode, int) and
                check_mode in {self.check_consistency, self.check_validity})


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


class SymStatesC(SymStates):
    pc_cls = PC_CIVL
    mindepth = settings.C.SE_MIN_DEPTH
    maxdepth = mindepth + settings.C.SE_DEPTH_INCR

    @classmethod
    def mk(cls, depth, filename, mainQName, funname, tmpdir, nInps):
        """
        civl verify -maxdepth=20 -seed=10 /var/tmp/Dig_04lfhmlz/cohendiv.c
        """

        tracefile = Path("{}.{}_{}.straces".format(filename, mainQName, depth))
        assert not tracefile.exists(), tracefile
        mlog.debug("Obtain symbolic states (tree depth {}){}"
                   .format(depth, ' ({})'.format(tracefile)))
        cmd = settings.C.CIVL_RUN(
            maxdepth=depth, file=filename, tracefile=tracefile)
        mlog.debug(cmd)
        CM.vcmd(cmd)
        pcs = PC_CIVL.parse(tracefile)
        return pcs


class SymStatesJava(SymStates):
    pc_cls = PC_JPF
    mindepth = settings.Java.SE_MIN_DEPTH
    maxdepth = mindepth + settings.Java.SE_DEPTH_INCR

    @classmethod
    def mk(cls, depth, filename, mainQName, funname, tmpdir, nInps):
        max_val = settings.INP_MAX_V
        tracefile = Path("{}.{}_{}_{}.straces".format(
            filename, mainQName, max_val, depth))

        mlog.debug("Obtain symbolic states (max val {}, tree depth {}){}"
                   .format(max_val, depth,
                           ' ({})'.format(tracefile)
                           if tracefile.is_file() else ''))

        if not tracefile.is_file():
            from helpers.src import Java as mysrc
            jpffile = mysrc.mk_JPF_runfile(
                funname, mainQName, tmpdir, nInps, max_val, depth)

            tracefile = "{}_{}_{}_{}.straces".format(
                funname, mainQName, max_val, depth)
            tracefile = tmpdir / tracefile

            assert not tracefile.is_file(), tracefile
            cmd = settings.Java.JPF_RUN(jpffile=jpffile, tracefile=tracefile)
            mlog.debug(cmd)
            CM.vcmd(cmd)

        pcs = PC_JPF.parse(tracefile)
        return pcs

"""
Symbolic States
"""
from collections import defaultdict
from abc import ABCMeta, abstractmethod
import pdb
from pathlib import Path
from multiprocessing import Queue

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
import analysis

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


class SymStatesMaker(metaclass=ABCMeta):
    def __init__(self, filename, mainQName, funname, ninps, use_reals, tmpdir, symstates_dir=None):
        assert tmpdir.is_dir(), tmpdir

        self.filename = filename
        self.mainQName = mainQName
        self.funname = funname
        self.tmpdir = tmpdir
        self.symstates_dir = symstates_dir
        self.ninps = ninps
        self.use_reals = use_reals

    def compute(self):
        """
        Run symbolic execution to obtain symbolic states
        """
        tasks = [depth for depth in range(self.mindepth, self.maxdepth+1)]

        def f(tasks):
            rs = [(depth, self.get_ss_at_depth(depth)) for depth in tasks]
            rs = [(depth, ss) for depth, ss in rs if ss]
            return rs

        wrs = helpers.miscs.Miscs.run_mp("get symstates", tasks, f)

        if not wrs:
            mlog.warning("cannot obtain symbolic states, unreachable locs?")
            import sys
            sys.exit(0)

        return self.merge(wrs, self.pc_cls, self.use_reals)

    def get_ss_at_depth(self, depth):
        tracefile, cmd = self.mk(depth)
        mlog.debug("Obtain symbolic states (tree depth {})".format(depth))
        mlog.debug("tracefile {}".format(tracefile))
        mlog.debug(cmd)
        CM.vcmd(cmd)
        pcs = self.pc_cls.parse(tracefile)
        return pcs

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

    @property
    def mindepth(self):
        return settings.C.SE_MIN_DEPTH

    @property
    def maxdepth(self):
        return self.mindepth + settings.C.SE_DEPTH_INCR

    def mk(self, depth):
        """
        civl verify -maxdepth=20 -seed=10 /var/tmp/Dig_04lfhmlz/cohendiv.c
        """

        tracefile = Path("{}.{}_{}.straces".format(
            self.filename, self.mainQName, depth))
        cmd = settings.C.CIVL_RUN(
            maxdepth=depth, file=self.filename, tracefile=tracefile)
        return tracefile, cmd


class SymStatesMakerJava(SymStatesMaker):
    pc_cls = PC_JPF

    @property
    def mindepth(self):
        return settings.Java.SE_MIN_DEPTH

    @property
    def maxdepth(self):
        return self.mindepth + settings.Java.SE_DEPTH_INCR

    def mk(self, depth):
        max_val = settings.INP_MAX_V

        tracefile = "{}_{}_{}_{}.straces".format(
            self.funname, self.mainQName, max_val, depth)
        tracefile = self.tmpdir / tracefile
        jpffile = self.mk_JPF_runfile(max_val, depth)
        cmd = settings.Java.JPF_RUN(jpffile=jpffile, tracefile=tracefile)
        return tracefile, cmd

    def mk_JPF_runfile(self, max_int, depth):
        assert max_int >= 0, max_int

        symargs = ['sym'] * self.ninps
        symargs = '#'.join(symargs)
        stmts = [
            "target={}".format(self.funname),
            "classpath={}".format(self.tmpdir),
            "symbolic.method={}.{}({})".format(
                self.funname, self.mainQName, symargs),
            "listener=gov.nasa.jpf.symbc.InvariantListenerVu",
            "vm.storage.class=nil",
            "search.multiple_errors=true",
            "symbolic.min_int={}".format(-max_int),
            "symbolic.max_int={}".format(max_int),
            "symbolic.min_long={}".format(-max_int),
            "symbolic.max_long={}".format(max_int),
            "symbolic.min_short={}".format(-max_int),
            "symbolic.max_short={}".format(max_int),
            "symbolic.min_float={}.0f".format(-max_int),
            "symbolic.max_float={}.0f".format(max_int),
            "symbolic.min_double={}.0".format(-max_int),
            "symbolic.max_double={}.0".format(max_int),
            "symbolic.dp=z3bitvector",
            "search.depth_limit={}".format(depth)]
        contents = '\n'.join(stmts)

        filename = self.tmpdir / \
            "{}_{}_{}.jpf".format(self.funname, max_int, depth)

        assert not filename.is_file(), filename
        CM.vwrite(filename, contents)
        return filename


class SymStates:
    solver_stats = Queue()

    def __init__(self, inp_decls, inv_decls):
        self.inp_decls = inp_decls
        self.inv_decls = inv_decls
        self.use_reals = inv_decls.use_reals
        self.inp_exprs = inp_decls.exprs(self.use_reals)

    def compute(self, symstatesmaker_cls, filename, mainQName, funname, tmpdir):
        symstatesmaker = symstatesmaker_cls(
            filename, mainQName, funname, len(self.inp_decls), self.use_reals, tmpdir)
        self.ss = symstatesmaker.compute()

    # Checking invariants using symbolic states
    def check(self, dinvs, inps):
        """
        Check invs, return cexs
        Also update inps
        """
        assert isinstance(dinvs, data.inv.invs.DInvs), dinvs
        assert not inps or (isinstance(inps, data.traces.Inps) and inps), inps
        # assert self.check_check_mode(check_mode), check_mode

        mlog.debug("checking {} invs:\n{}".format(
            dinvs.siz, dinvs.__str__(print_first_n=20)))
        tasks = [(loc, inv) for loc in dinvs for inv in dinvs[loc]
                 if inv.stat is None]
        refsD = {(loc, str(inv)): inv for loc, inv in tasks}

        def f(tasks):
            return [(loc, str(inv),
                     self.mcheck_d(loc, inv, inps, ncexs=1))
                    for loc, inv in tasks]
        wrs = helpers.miscs.Miscs.run_mp("prove", tasks, f)

        mCexs = []
        mdinvs = data.inv.invs.DInvs()
        for loc, str_inv, (cexs, is_succ) in wrs:
            inv = refsD[(loc, str_inv)]

            if cexs:
                stat = data.inv.base.Inv.DISPROVED
                mCexs.append({loc: {str(inv): cexs}})
            else:
                stat = data.inv.base.Inv.PROVED if is_succ else data.inv.base.Inv.UNKNOWN
            inv.stat = stat
            mdinvs.setdefault(loc, data.inv.invs.Invs()).add(inv)

        return merge(mCexs), mdinvs

    def mcheck_d(self, loc, inv, inps, ncexs):

        assert isinstance(loc, str), loc
        assert inv is None or \
            isinstance(inv, data.inv.base.Inv) or \
            z3.is_expr(inv), (inv, type(inv))

        assert inps is None or isinstance(inps, data.traces.Inps), inps
        assert ncexs >= 1, ncexs

        try:
            inv_expr = inv.expr(self.use_reals)
            if inv_expr is zFalse:
                inv_expr = None
        except AttributeError:
            if z3.is_expr(inv):
                inv_expr = inv
            else:
                inv_expr = None

        if settings.DO_INCR_DEPTH:
            cexs, is_succ = self.mcheck_depth(
                self.ss[loc], inv, inv_expr, inps, ncexs)
        else:
            cexs, is_succ, stat = self.mcheck(
                self.get_ss_at_depth(self.ss[loc], depth=None),
                inv_expr, inps, ncexs)

        return cexs, is_succ

    def mcheck_depth(self, ssl, inv, inv_expr, inps, ncexs):
        assert inv_expr is None or z3.is_expr(inv_expr), inv_expr
        assert isinstance(ssl, defaultdict), ssl  # self.ss[loc]

        def f(depth):
            ss = ssl[depth]
            ss = ss.mypc if inv_expr is None else ss.myexpr
            cexs, is_succ, stat = self.mcheck(ss, inv_expr, inps, ncexs)
            self.solver_stats.put(analysis.CheckSolverCalls(stat))
            return cexs, is_succ, stat

        depths = sorted(ssl.keys())
        depth_idx = 0

        cexs, is_succ, stat = f(depths[depth_idx])
        if stat != z3.unsat:  # if disprove (sat) or unknown first time
            self.solver_stats.put(analysis.CheckDepthChanges(
                inv, None, None, stat, depths[depth_idx]))

        while(stat != z3.sat and depth_idx < len(depths) - 1):
            depth_idx_ = depth_idx + 1
            cexs_, is_succ_, stat_ = f(depths[depth_idx_])
            if stat_ != stat:
                mydepth_ = depths[depth_idx_]
                mydepth = depths[depth_idx]
                mlog.debug("check depth diff {}: {} @ depth {}, {} @ depth {}"
                           .format(inv_expr, stat, mydepth, stat_, mydepth_))
                self.solver_stats.put(
                    analysis.CheckDepthChanges(inv, stat, mydepth, stat_, mydepth_))

            depth_idx = depth_idx_
            cexs, is_succ, stat = cexs_, is_succ_, stat_

        return cexs, is_succ

    def mcheck(self, symstates_expr, inv, inps, ncexs):
        """
        check if pathcond => inv
        if not, return cex
        return cexs, is_succ (if the solver does not timeout)
        """
        assert z3.is_expr(symstates_expr), symstates_expr
        assert inv is None or z3.is_expr(inv), inv
        assert inps is None or isinstance(inps, data.traces.Inps), inps
        assert ncexs >= 0, ncexs
        # assert self.check_check_mode(check_mode), check_mode

        f = symstates_expr
        iconstr = self.get_inp_constrs(inps)
        if iconstr is not None:
            f = z3.simplify(z3.And(iconstr, f))

        if inv is not None:
            f = z3.Not(z3.Implies(f, inv))

        models, stat = helpers.miscs.Z3.get_models(f, ncexs)
        cexs, is_succ = helpers.miscs.Z3.extract(models)
        return cexs, is_succ, stat

    # Find maximal values for term using symbolic states
    def maximize(self, loc, term_expr, do_all=True):
        """
        maximize value of term
        """
        assert z3.is_expr(term_expr), term_expr

        if settings.DO_INCR_DEPTH:
            v, stat = self.mmaximize_depth(self.ss[loc], term_expr)
        else:
            v, stat = self.mmaximize(
                self.get_ss_at_depth(self.ss[loc], depth=None),
                term_expr)
        return v

    def mmaximize_depth(self, ssl, term_expr):
        assert z3.is_expr(term_expr), term_expr
        assert isinstance(ssl, defaultdict)

        def f(depth):
            ss = self.get_ss_at_depth(ssl, depth=depth)
            maxv, stat = self.mmaximize(ss, term_expr)
            self.solver_stats.put(analysis.MaxSolverCalls(stat))
            return maxv, stat

        depths = sorted(ssl.keys())
        depth_idx = 0

        maxv, stat = f(depths[depth_idx])
        if maxv is None:  # if no solution (unsat) or unknown first time
            self.solver_stats.put(
                analysis.MaxDepthChanges(
                    str(term_expr), None, None, maxv, depths[depth_idx]))

        while(maxv is not None and depth_idx < len(depths) - 1):
            depth_idx_ = depth_idx + 1
            maxv_, stat_ = f(depths[depth_idx_])
            if maxv_ != maxv:
                assert(not(isinstance(maxv_, int) and isinstance(maxv, int))
                       or (maxv_ > maxv)), (maxv_, maxv)

                mydepth_ = depths[depth_idx_]
                mydepth = depths[depth_idx]
                mlog.debug("maximize depth diff {}: {} {} @ depth {}, {} {} @ depth {}"
                           .format(term_expr, maxv, stat, mydepth,
                                   maxv_, stat_, mydepth_))
                self.solver_stats.put(
                    analysis.MaxDepthChanges(str(term_expr), maxv, mydepth, maxv_, mydepth_))

            depth_idx = depth_idx_
            maxv, stat = maxv_, stat_

        return maxv, stat

    def mmaximize(self, ss, term_expr):
        opt = helpers.miscs.Z3.create_solver(maximize=True)
        opt.add(ss)
        h = opt.maximize(term_expr)
        stat = opt.check()
        v = None
        if stat == z3.sat:
            v = str(opt.upper(h))
            if v != 'oo':  # no bound
                v = int(v)
                if v <= settings.IUPPER:
                    return v, stat

        return None, stat

    # helpers

    def get_ss_at_depth(self, ssl, depth=None):
        assert depth is None or depth >= 0, depth

        if depth is None:
            return z3.Or([ssl[depth].myexpr for depth in ssl])
        else:
            ss = []
            for d in sorted(ssl):
                if d > depth:
                    break
                ss.append(ssl[d].myexpr)

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

"""
Symbolic States
"""
from abc import ABCMeta, abstractmethod
import pdb
from pathlib import Path

import z3
import sage.all
from sage.all import cached_function

import settings
import helpers.vcommon as CM
from helpers.miscs import Miscs, Z3
from data.miscs import Symbs, DSymbs
from data.traces import Inps
from data.inv.base import Inv
from data.inv.invs import Invs, DInvs

DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


class PC(metaclass=ABCMeta):

    def __init__(self, loc, depth, pc, slocal, use_reals):
        assert isinstance(loc, str) and loc, loc
        assert depth >= 0, depth
        assert pc is None or isinstance(pc, str) and pc, pc
        assert isinstance(slocal, str) and slocal, slocal
        assert isinstance(use_reals, bool), bool

        self.pc = z3.BoolVal('True') if pc is None else Z3.parse(pc, use_reals)
        self.slocal = Z3.parse(slocal, use_reals)
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

    # @property
    # def exprPC(self):
    #     constrs = self.pcs_z3
    #     return self._and(constrs)

    # @classmethod
    # def _and(cls, fs):
    #     assert all(z3.is_expr(f) for f in fs), fs

    #     f = z3.And(fs)
    #     f = z3.simplify(f)
    #     return f

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
        for l in lines:
            if not l:
                continue
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
        return loc, pc, slocal

    @staticmethod
    def replace_str(s):
        s_ = (s.
              replace(' = ', ' == ').
              replace(';', ' and ').
              replace('&&', 'and').
              replace('||', 'or').
              replace('div ', '/ ').
              replace('^', '**').
              strip())
        return s_


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
        for l in lines:
            l = l.strip()
            if not l:
                continue
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
            if Miscs.is_num(v) and v >= settings.LARGE_N:
                mlog.warning("ignore {} (larger than {})".format(
                    p, settings.LARGE_N))
                return True
            else:
                return False

        slocals = [p for p in slocals if not isTooLarge(p)]
        slocals = [cls.replace_str(p) for p in slocals if p]
        pcs = [cls.replace_str(pc) for pc in pcs if pc]
        return loc, pcs, slocals

    @staticmethod
    @cached_function
    def replace_str(s):
        s_ = (s.replace('&&', '').
              replace(' = ', '==').
              replace('CONST_', '').
              replace('REAL_', '').
              replace('%NonLinInteger%', '').
              replace('SYM:', '').
              replace('CON:', '').
              strip())
        return s_


class PCs(set):
    def __init__(self, loc, depth):
        assert isinstance(loc, str), loc
        assert depth >= 1, depth

        super(PCs, self).__init__(set())
        self.loc = loc
        self.depth = depth

    def add(self, pc):
        assert isinstance(pc, PC), pc
        super(PCs, self).add(pc)

    @property
    def expr(self):
        try:
            return self._expr
        except AttributeError:
            self._expr = z3.simplify(z3.Or([p.expr for p in self]))
            return self._expr

    @property
    def pc(self):
        try:
            return self._pc
        except AttributeError:
            self._pc = z3.simplify(z3.Or([p.pc for p in self]))
            return self._pc


class SymStates(metaclass=ABCMeta):

    def __init__(self, inp_decls, inv_decls, seed=None):
        assert isinstance(inp_decls, Symbs), inp_decls  # I x, I y
        # {'vtrace1': (('q', 'I'), ('r', 'I'), ('x', 'I'), ('y', 'I'))}
        assert isinstance(inv_decls, DSymbs), inv_decls

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

        tasks = [depth for depth in range(self.mindepth, self.maxdepth)]

        def f(tasks):
            rs = [(depth, _f(depth)) for depth in tasks]
            rs = [(depth, ss) for depth, ss in rs if ss]
            return rs

        wrs = Miscs.run_mp("get symstates", tasks, f)

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

        symstates = {}
        for depth, ss in depthss:
            for (loc, pcs, slocals) in ss:
                pc = pc_cls(loc, depth, pcs, slocals, use_reals)
                symstates.setdefault(loc, {})
                symstates[loc].setdefault(depth, PCs(loc, depth)).add(pc)

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
                "{}: no symbolic states found at depth {}".format(loc, depth))
            symstates[loc].pop(depth)

        empties = [loc for loc in symstates if not symstates[loc]]
        for loc in empties:
            mlog.warning("{}: no symbolic states found".format(loc))
            symstates.pop(loc)

        if all(not symstates[loc] for loc in symstates):
            mlog.error("No symbolic states found for any locs. Exit !!")
            exit(1)

        # output info
        mlog.debug('\n'.join("{}: depth {}: {} symstates\n{}".format(
            loc, depth, len(symstates[loc][depth]),
            '\n'.join("{}. {}".format(i, ss)
                      for i, ss in enumerate(symstates[loc][depth])))
            for loc in symstates for depth in symstates[loc]))

        return symstates

    def check(self, dinvs, inps, path_idx=None):
        """
        Check invs.
        Also update inps
        """
        assert isinstance(dinvs, DInvs), dinvs
        assert not inps or (isinstance(inps, Inps) and inps), inps

        mlog.debug("checking {} invs:\n{}".format(
            dinvs.siz, dinvs.__str__(print_first_n=20)))
        return self.get_inps(dinvs, inps, path_idx)

    def get_inps(self, dinvs, inps, path_idx=None):
        """call verifier on each inv"""

        tasks = [(loc, inv) for loc in dinvs for inv in dinvs[loc]
                 if inv.stat is None]
        refsD = {(loc, str(inv)): inv for loc, inv in tasks}

        def f(tasks):
            return [(loc, str(inv),
                     self._mcheck_d(
                         loc, path_idx,
                         inv.expr(self.use_reals), inps, ncexs=1))
                    for loc, inv in tasks]
        wrs = Miscs.run_mp("prove", tasks, f)

        mCexs, mdinvs = [], DInvs()
        for loc, str_inv, (cexs, isSucc) in wrs:
            inv = refsD[(loc, str_inv)]

            if cexs:
                stat = Inv.DISPROVED
                mCexs.append({loc: {str(inv): cexs}})
            else:
                stat = Inv.PROVED if isSucc else Inv.UNKNOWN
            inv.stat = stat
            mdinvs.setdefault(loc, Invs()).add(inv)

        return merge(mCexs), mdinvs

    # PRIVATE

    def _mcheck_d(self, loc, path_idx, inv, inps, ncexs=1):
        assert isinstance(loc, str), loc
        assert path_idx is None or path_idx >= 0
        assert inv is None or z3.is_expr(inv), inv
        assert inps is None or isinstance(inps, Inps), inps
        assert ncexs >= 1, ncexs

        if inv == z3.BoolVal(False):
            inv = None

        def f(depth):
            ss = self.ss[loc][depth]
            if inv == z3.BoolVal(False):
                ss = ss[path_idx].pc if path_idx else ss.pc
            else:
                ss = ss[path_idx].expr if path_idx else ss.expr
            return self._mcheck(ss, inv, inps, ncexs)

        depths = sorted(self.ss[loc].keys())
        depth_idx = 0

        cexs, isSucc, stat = f(depths[depth_idx])
        while(stat != z3.sat and depth_idx < len(depths) - 1):
            depth_idx = depth_idx + 1
            cexs_, isSucc_, stat_ = f(depths[depth_idx])
            if stat_ != stat:
                mlog.debug("depth diff {}: {} @ depth {}, {} @ depth {}"
                           .format(inv, stat_, depths[depth_idx - 1],
                                   stat, depths[depth_idx]))
            cexs, isSucc, stat = cexs_, isSucc_, stat_

        return cexs, isSucc

    def _mcheck(self, symstatesExpr, inv, inps, ncexs=1):
        """
        check if pathcond => inv
        if not, return cex

        return inps, cexs, isSucc (if the solver does not timeout)
        """
        assert z3.is_expr(symstatesExpr), symstatesExpr
        assert inv is None or z3.is_expr(inv), inv
        assert inps is None or isinstance(inps, Inps), inps
        assert ncexs >= 0, ncexs

        f = symstatesExpr
        iconstr = self._get_inp_constrs(inps)
        if iconstr is not None:
            f = z3.simplify(z3.And(iconstr, f))
        if inv is not None:
            f = z3.Not(z3.Implies(f, inv))

        models, stat = Z3.get_models(f, ncexs)
        cexs, isSucc = Z3.extract(models)
        return cexs, isSucc, stat

    def _get_inp_constrs(self, inps):
        cstrs = []
        if isinstance(inps, Inps) and inps:
            inpCstrs = [inp.mkExpr(self.inp_exprs) for inp in inps]
            inpCstrs = [z3.Not(expr) for expr in inpCstrs if expr is not None]
            cstrs.extend(inpCstrs)

        if not cstrs:
            return None
        elif len(cstrs) == 1:
            return cstrs[0]
        else:
            return z3.And(cstrs)


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
    mindepth = settings.C.CIVL_MIN_DEPTH
    maxdepth = mindepth + settings.C.CIVL_DEPTH_INCR

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
    mindepth = settings.Java.JPF_MIN_DEPTH
    maxdepth = mindepth + settings.Java.JPF_DEPTH_INCR

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

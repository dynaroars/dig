import random
from collections import OrderedDict
import itertools
import os.path
import sage.all
from sage.all import cached_function
import z3
import vcommon as CM
from miscs import Miscs, Z3
from ds import Symbs, Inps, Inv,  DInvs, Invs, DTraces
import srcJava
import settings
import pdb
trace = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)

"""
Symbolic States
"""


class PC(object):
    def __init__(self, loc, depth, pcs, slocals, st, sd, use_reals):
        assert isinstance(loc, str) and loc, loc
        assert depth >= 0, depth
        assert isinstance(pcs, list) and \
            all(isinstance(pc, str) for pc in pcs), pcs
        assert isinstance(slocals, list) and \
            all(isinstance(slocal, str)
                for slocal in slocals) and slocals, slocals
        assert all(isinstance(s, str) and isinstance(t, str)
                   for s, t in st.iteritems()), st
        assert all(isinstance(s, str) and Miscs.is_expr(se)
                   for s, se in sd.iteritems()), sd
        assert isinstance(use_reals, bool), bool

        pcs_ = []
        pcsModIdxs = set()  # contains idxs of pc's with % (modulus ops)
        for i, p in enumerate(pcs):
            p, isReplaced = PC.replaceMod(p)
            if isReplaced:
                pcsModIdxs.add(i)
            sexpr = Miscs.msage_eval(p, sd)
            assert not isinstance(
                sexpr, bool), "pc '{}' evals to '{}'".format(p, sexpr)
            pcs_.append(sexpr)

        pcs = [Miscs.elimDenom(pc) for pc in pcs_]
        pcs = [pc for pc in pcs
               if not (pc.is_relational() and str(pc.lhs()) == str(pc.rhs()))]

        def thack0(s):
            # for Hola H32.Java program
            return s.replace("((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((j + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)", "j + 100")

        slocals_ = []
        for p in slocals:
            try:
                sl = Miscs.msage_eval(p, sd)
            except MemoryError as mex:
                mlog.warn("{}: {}".format(mex, p))
                sl = Miscs.msage_eval(thack0(p), sd)

            slocals_.append(sl)
        slocals = slocals_
        slocals = [Miscs.elimDenom(p) for p in slocals]
        slocals = [p for p in slocals
                   if not (p.is_relational() and str(p.lhs()) == str(p.rhs()))]

        assert isinstance(loc, str) and loc, loc
        assert all(Miscs.isRel(pc) for pc in pcs), pcs
        assert all(Miscs.isRel(pc) for pc in slocals), slocals

        self.loc = loc
        self.depth = depth
        self.st = st
        self.pcs = pcs
        self.pcsModIdxs = pcsModIdxs
        self.slocals = slocals
        self.use_reals = use_reals

    def __str__(self):
        ss = ['loc: {}'.format(self.loc),
              'vs: {}'.format(', '.join('{} {}'.format(
                  self.st[v], v) for v in self.st)),
              'pcs: {}'.format(', '.join(map(str, self.pcs))),
              'slocals: {}'.format(', '.join(map(str, self.slocals)))]
        return '\n'.join(ss)

    def __eq__(self, other):
        return isinstance(other, self.__class__) and hash(self) == hash(other)

    def __hash__(self):
        return hash(self.__str__())

    @property
    def pcs_z3(self):
        try:
            return self._pcs_z3
        except AttributeError:
            self._pcs_z3 = [Z3.toZ3(pc, self.use_reals, i in self.pcsModIdxs)
                            for i, pc in enumerate(self.pcs)]
            return self._pcs_z3

    @property
    def slocals_z3(self):
        try:
            return self._slocals_z3
        except AttributeError:
            self._slocals_z3 = [Z3.toZ3(p, self.use_reals, useMod=False)
                                for p in self.slocals]
            return self._slocals_z3

    @property
    def expr(self):
        constrs = self.pcs_z3 + self.slocals_z3
        return self.andConstrs(constrs)

    @property
    def exprPC(self):
        constrs = self.pcs_z3
        return self.andConstrs(constrs)

    @classmethod
    def andConstrs(cls, fs):
        assert all(z3.is_expr(f) for f in fs), fs

        f = z3.And(fs)
        f = z3.simplify(f)
        return f

    @classmethod
    def parsePC(cls, ss):
        assert isinstance(ss, list) and ss, ss

        curpart = []
        for s in ss:
            if 'loc: ' in s:
                loc = s.split()[1]  # e.g., vtrace30(I)V
                loc = loc.split('(')[0]  # vtrace30
                continue
            elif 'vars: ' in s:
                vs = s.split(':')[1].split(',')  # int x, int y
                vs = [tuple(tv.split()) for tv in vs if tv]
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
            if Miscs.isNum(v) and v >= settings.LARGE_N:
                mlog.warn("ignore {} (larger than {})".format(
                    p, settings.LARGE_N))
                return True
            else:
                return False

        slocals = [p for p in slocals if not isTooLarge(p)]
        slocals = [PC.replaceStr(p) for p in slocals if p]
        pcs = [PC.replaceStr(pc) for pc in pcs if pc]
        return loc, vs, pcs, slocals

    @classmethod
    def parse(cls, filename, delim="**********"):
        """
        Return a list of strings representing pc's
        """

        parts, curpart = [], []

        start = delim + " START"
        end = delim + " END"
        doAppend = False
        for l in CM.iread_strip(filename):
            if l.startswith(start):
                doAppend = True
                continue
            elif l.startswith(end):
                doAppend = False
                if curpart:
                    parts.append(curpart)
                    curpart = []
            else:
                if doAppend:
                    curpart.append(l)

        if not parts:
            mlog.error("Cannot obtain symstates from '{}'".format(filename))
            return None

        pcs = [cls.parsePC(pc) for pc in parts]
        return pcs

    @cached_function
    def replaceStr(s):
        s_ = (s.replace('&&', '').
              replace(' = ', '==').
              replace('CONST_', '').
              replace('REAL_', '').
              replace('%NonLinInteger%', '').
              replace('SYM:', '').
              replace('CON:', '').
              strip())
        return s_

    @cached_function
    def replaceMod(s):
        if "%" not in s:
            return s, False
        s_ = s.replace("%", "^")
        mlog.debug("Uninterpreted (temp hack): {} => {}".format(s, s_))
        return s_, True


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
            self._expr = z3.simplify(z3.Or([pc.expr for pc in self]))
            return self._expr

    @property
    def exprPC(self):
        try:
            return self._exprPC
        except AttributeError:
            self._exprPC = z3.simplify(z3.Or([pc.exprPC for pc in self]))
            return self._exprPC


class SymStates(object):
    def __init__(self, inp_decls, inv_decls):
        assert isinstance(inp_decls, Symbs), inp_decls  # I x, I y
        # {'vtrace1': (('q', 'I'), ('r', 'I'), ('x', 'I'), ('y', 'I'))}
        assert isinstance(inv_decls, dict), inv_decls

        self.inp_decls = inp_decls
        self.inv_decls = inv_decls
        self.use_reals = any(s.isReal for syms in inv_decls.itervalues()
                             for s in syms)

        self.inp_exprs = inp_decls.exprs(self.use_reals)

    def compute(self, filename, mainQName, clsName, jpfDir):

        def _f(d): return self.mk(
            d, filename, mainQName, clsName, jpfDir, len(self.inp_decls))

        def wprocess(tasks, Q):
            rs = [(depth, _f(depth)) for depth in tasks]
            rs = [(depth, ss) for depth, ss in rs if ss]
            if Q is None:
                return rs
            else:
                Q.put(rs)

        mindepth = settings.JPF_MIN_DEPTH
        maxdepth = mindepth + settings.JPF_DEPTH_INCR
        tasks = [depth for depth in range(mindepth, maxdepth)]
        wrs = Miscs.runMP("get symstates", tasks, wprocess, chunksiz=1,
                          doMP=settings.doMP and len(tasks) >= 2)
        self.merge(wrs)

    @classmethod
    def mk(cls, depth, filename, mainQName, clsName, jpfDir, nInps):
        max_val = DTraces.inpMaxV
        ssfile = "{}.{}_{}_{}.straces".format(
            filename, mainQName, max_val, depth)

        mlog.debug("Obtain symbolic states (max val {}, tree depth {}){}"
                   .format(max_val, depth,
                           ' ({})'.format(ssfile) if os.path.isfile(ssfile)
                           else ''))

        if not os.path.isfile(ssfile):
            jpffile = srcJava.mkJPFRunFile(
                clsName, mainQName, jpfDir, nInps, max_val, depth)

            ssfile = os.path.join(
                jpfDir, "{}_{}_{}_{}.straces".format(
                    clsName, mainQName, max_val, depth))
            assert not os.path.isfile(ssfile), ssfile
            cmd = settings.JPF_CMD(jpffile=jpffile, tracefile=ssfile)
            mlog.debug(cmd)
            CM.vcmd(cmd)

        pcs = PC.parse(ssfile)
        return pcs

    def merge(self, depthss):
        """
        Merge PC's info into symbolic states sd[loc][depth]
        """
        assert isinstance(depthss, list) and depthss, depthss
        assert all(depth >= 1 and isinstance(ss, list)
                   for depth, ss in depthss), depthss

        symstates = {}
        ssd = {}  # symb:string -> symbols:sage_expr
        for depth, ss in depthss:
            for (loc, vs, pcs, slocals) in ss:
                sst = OrderedDict((s, t)
                                  for t, s in vs)  # symb:str -> types:str
                for _, s in vs:
                    if s not in ssd:
                        ssd[s] = sage.all.var(s)
                pc = PC(loc, depth, pcs, slocals, sst, ssd, self.use_reals)

                if loc not in symstates:
                    symstates[loc] = {}
                if depth not in symstates[loc]:
                    symstates[loc][depth] = PCs(loc, depth)
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
            mlog.warn(
                "{}: depth {}: no symbolic states found".format(loc, depth))
            symstates[loc].pop(depth)

        empties = [loc for loc in symstates if not symstates[loc]]
        for loc in empties:
            mlog.warn("{}: no symbolic states found".format(loc))
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

        self.ss = symstates

    # prover stuff

    def getInps(self, dinvs, inps, pathIdx=None):
        """call verifier on each inv"""

        def check(loc, inv): return self.mcheckD(
            loc, pathIdx, inv.expr(self.use_reals), inps, ncexs=1)

        def wprocess(tasks, Q):
            rs = [(loc, str(inv), check(loc, inv)) for loc, inv in tasks]
            if Q is None:
                return rs
            else:
                Q.put(rs)

        tasks = [(loc, inv) for loc in dinvs for inv in dinvs[loc]
                 if inv.stat is None]
        refsD = {(loc, str(inv)): inv for loc, inv in tasks}
        wrs = Miscs.runMP("prove", tasks, wprocess, chunksiz=1,
                          doMP=settings.doMP and len(tasks) >= 2)

        mCexs, mdinvs, depths = [], DInvs(), []
        for loc, str_inv, (depth, cexs, isSucc) in wrs:
            depths.append(depth)
            inv = refsD[(loc, str_inv)]

            if cexs:
                stat = Inv.DISPROVED
                mCexs.append({loc: {str(inv): cexs}})
            else:
                stat = Inv.PROVED if isSucc else Inv.UNKNOWN
            inv.stat = stat

            if loc not in mdinvs:
                mdinvs[loc] = Invs()
            mdinvs[loc].add(inv)

        return merge(mCexs), mdinvs

    def check(self, dinvs, inps, pathIdx=None):
        """
        Check invs.
        Also update inps
        """
        assert isinstance(dinvs, DInvs), dinvs
        assert inps is None or (isinstance(inps, Inps) and inps), inps

        mlog.debug("checking {} invs:\n{}".format(dinvs.siz, dinvs))
        return self.getInps(dinvs, inps, pathIdx)

    def mkInpsConstr(self, inps):
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

    def mcheck(self, symstatesExpr, inv, inps, ncexs=1):
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
        iconstr = self.mkInpsConstr(inps)
        if iconstr is not None:
            f = z3.simplify(z3.And(iconstr, f))
        if inv is not None:
            f = z3.Not(z3.Implies(f, inv))

        models, stat = Z3.getModels(f, ncexs)
        cexs, isSucc = Z3.extract(models)
        return cexs, isSucc, stat

    def mcheckD(self, loc, pathIdx, inv, inps, ncexs=1):
        assert isinstance(loc, str), loc
        assert pathIdx is None or pathIdx >= 0
        assert inv is None or z3.is_expr(inv), inv
        assert inps is None or isinstance(inps, Inps), inps
        assert ncexs >= 1, ncexs

        if inv == z3.BoolVal(False):
            inv = None

        def f(depth):
            ss = self.ss[loc][depth]
            if inv == z3.BoolVal(False):
                ss = ss[pathIdx].exprPC if pathIdx else ss.exprPC
            else:
                ss = ss[pathIdx].expr if pathIdx else ss.expr
            return self.mcheck(ss, inv, inps, ncexs)

        depths = sorted(self.ss[loc].keys())
        depthIdx = 0

        cexs, isSucc, stat = f(depths[depthIdx])
        while(stat != z3.sat and depthIdx < len(depths) - 1):
            depthIdx = depthIdx + 1
            cexs_, isSucc_, stat_ = f(depths[depthIdx])

            if stat_ == stat:
                assert isSucc_ == isSucc, (isSucc_, isSucc)
                depthIdx = depthIdx - 1
                break
            else:
                mlog.debug("DepthDiff {}: {} @ depth {} vs {} @ depth {}"
                           .format(inv, stat_, depths[depthIdx],
                                   stat, depths[depthIdx-1]))
                cexs, isSucc, stat = cexs_, isSucc_, stat_

        return depths[depthIdx], cexs, isSucc

    def extractCexs(self, models):
        assert all(isinstance(m, z3.ModelRef)
                   for m in models) and models, models

        def f(model):
            cex = {str(s): sage.all.sage_eval(str(model[s])) for s in model}
            return cex

        cexs = [f(model) for model in models]
        return cexs

    def genRandInps(self, prog):
        def _f(irs): return tuple(random.randrange(ir[0], ir[1]) for ir in irs)

        try:
            validRanges = self._validRanges
            validInps = set()
        except AttributeError:  # compute rranges
            small = 0.10
            large = 1 - small
            maxV = DTraces.inpMaxV
            minV = -1 * maxV
            rinps = [(0, int(maxV * small)), (int(maxV * large), maxV),
                     (int(minV * small), 0), (minV, int(minV * large))]

            # [((0, 30), (0, 30)), ((0, 30), (270, 300)), ...]
            rinps = list(itertools.product(
                *itertools.repeat(rinps, len(self.inp_exprs))))

            validRanges, validInps = set(), set()
            for rinp in rinps:
                inp = _f(rinp)
                myinps = Inps()
                _ = myinps.myupdate(set([inp]), self.inp_decls.names)
                tcs = prog.getTraces(myinps)
                if tcs:
                    validRanges.add(rinp)
                    validInps.add(inp)
                else:
                    mlog.debug("inp range {} invalid".format(inp))

            self._validRanges = validRanges

        # gen inps
        if not validInps:
            validInps = set(_f(vr) for vr in validRanges)
        return validInps


def merge(ds):
    newD = {}
    for d in ds:
        for loc in d:
            assert d[loc]
            if loc not in newD:
                newD[loc] = {}
            for inv in d[loc]:
                assert d[loc][inv]
                if inv not in newD[loc]:
                    newD[loc][inv] = []
                for e in d[loc][inv]:
                    newD[loc][inv].append(e)
    return newD

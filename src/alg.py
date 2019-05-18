import settings
from abc import ABCMeta
import os.path
from time import time
import sage.all
import vcommon as CM
from miscs import Miscs
import srcJava
from ds import Inps, Traces, DTraces, Inv, EqtInv, Invs, DInvs, Prog
from symstates import SymStates
from cegir import Cegir
import pdb
trace = pdb.set_trace

mlog = CM.getLogger(__name__, settings.logger_level)


class Dig(object):
    __metaclass__ = ABCMeta

    def __init__(self, filename):
        assert os.path.isfile(filename), filename
        mlog.info("analyze '{}'".format(filename))

        import tempfile
        self.tmpdir = tempfile.mkdtemp(dir=settings.tmpdir, prefix="Dig_")
        self.filename = filename

    def start(self, seed, maxdeg):
        assert maxdeg is None or maxdeg >= 1, maxdeg

        import random
        random.seed(seed)
        sage.all.set_random_seed(seed)
        mlog.debug("set seed to: {} (test {})".format(
            seed, sage.all.randint(0, 100)))

        # determine degree
        maxvars = max(self.inv_decls.itervalues(), key=lambda d: len(d))
        self.deg = Miscs.get_auto_deg(maxdeg, len(maxvars), settings.MAX_TERM)


class DigCegir(Dig):
    def __init__(self, filename):
        super(DigCegir, self).__init__(filename)

        # call ASM to obtain
        (inp_decls, inv_decls, clsName, mainQName, jpfDir, jpfFile,
         traceDir, traceFile) = srcJava.parse(filename, self.tmpdir)

        self.inp_decls = inp_decls
        self.inv_decls = inv_decls
        self.useRandInit = True

        exeCmd = "{} -ea -cp {} {}".format(settings.JAVA_CMD,
                                           traceDir, clsName)
        self.prog = Prog(exeCmd, inv_decls)

        self.symstates = SymStates(inp_decls, inv_decls)
        self.symstates.compute(self.filename, mainQName, clsName, jpfDir)
        invalidLocs = [
            loc for loc in inv_decls if loc not in self.symstates.ss]
        for loc in invalidLocs:
            self.inv_decls.pop(loc)

    def str_of_locs(self, locs):
        return '; '.join("{} ({})".format(l, self.inv_decls[l]) for l in locs)

    def start(self, seed, maxdeg, do_eqts, do_ieqs, do_preposts):
        super(DigCegir, self).start(seed, maxdeg)

        st = time()
        solver = Cegir(self.symstates, self.prog)
        mlog.debug("check reachability")
        dinvs, traces, inps = solver.check_reach()
        if not traces:
            return dinvs, traces, self.tmpdir

        def _infer(typ, f):
            mlog.info("gen {} at {} locs".format(typ, len(traces)))
            mlog.debug(self.str_of_locs(traces.keys()))

            st = time()
            invs = f()
            if not invs:
                mlog.warn("infer no {}".format(typ))
            else:
                mlog.info("infer {} in {}s".format(invs.siz, typ, time() - st))
                dinvs.merge(invs)
                mlog.debug("{}".format(dinvs.__str__(print_stat=True)))

        if do_eqts:
            _infer('eqts', lambda: self.infer_eqts(self.deg, traces, inps))
        if do_ieqs:
            _infer('ieqs', lambda: self.infer_ieqs(traces, inps))
        if do_preposts:
            _infer('preposts', lambda: self.infer_preposts(dinvs, traces))

        # post procesing
        if dinvs.siz:
            mlog.info("test {} invs on {} traces".format(
                dinvs.siz, traces.siz))
            dinvs = dinvs.test(traces)

            if dinvs.siz:
                mlog.info("uniqify {} invs".format(dinvs.siz))
                mlog.debug("{}".format(dinvs.__str__(print_stat=True)))
                dinvs = dinvs.uniqify(self.symstates.use_reals)

        result = ("*** '{}', {} locs, invs {} ({} eqts), inps {} "
                  "time {:02f} s, rand {}:\n{}")
        print(result.format(self.filename, len(dinvs),
                            dinvs.siz, dinvs.n_eqs, len(inps),
                            time() - st, sage.all.randint(0, 100),
                            dinvs.__str__(print_stat=True)))

        return dinvs, traces, self.tmpdir

    def infer_eqts(self, deg, traces, inps):
        from cegirEqts import CegirEqts
        solver = CegirEqts(self.symstates, self.prog)
        solver.useRandInit = self.useRandInit
        dinvs = solver.gen(self.deg, traces, inps)
        return dinvs

    def infer_ieqs(self, traces, inps):
        from cegirIeqs import CegirIeqs
        solver = CegirIeqs(self.symstates, self.prog)
        dinvs = solver.gen(traces, inps)
        return dinvs

    def infer_preposts(self, dinvs, traces):
        from cegirPrePosts import CegirPrePosts
        solver = CegirPrePosts(self.symstates, self.prog)
        dinvs = solver.gen(dinvs, traces)
        return dinvs


class DigTraces(Dig):
    def __init__(self, filename):
        super(DigTraces, self).__init__(filename)
        from srcTcs import Src
        self.src = Src(filename)
        self.inv_decls = self.src.getInv_decls()

    def start(self, seed, maxdeg, do_eqts, do_ieqs):

        super(DigTraces, self).start(seed, maxdeg, do_eqts, do_ieqs)

        st = time()
        loc = self.inv_decls.keys()[0]
        dinvs = DInvs()
        dinvs[loc] = Invs()

        vs = tuple(self.inv_decls[loc].keys())
        assert vs, vs

        from ds import Trace
        traces = [l.split()
                  for loc_, l in self.src.contentsd.iteritems()
                  if str(loc_) != loc]
        traces = [[t[i] for i in range(len(vs))] for t in traces]
        traces = [Trace.parse(vs, t) for t in traces]
        traces = Traces(set(traces))

        terms, template, uks, nEqtsNeeded = Miscs.initTerms(
            vs, self.deg, settings.EQT_RATE)

        exprs = list(traces.instantiate(template, nEqtsNeeded))
        eqts = Miscs.solveEqts(exprs, uks, template)
        for inv in eqts:
            dinvs[loc].add(EqtInv(inv))

        dtraces = DTraces()
        dtraces[loc] = traces
        inps = Inps()
        self.check(dinvs, dtraces, inps, st)

        return dinvs, None, self.tmpdir

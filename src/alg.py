import settings
from abc import ABCMeta
import os.path
from time import time
import sage.all
import vcommon as CM
from miscs import Miscs, Z3
import srcJava
from ds import Inps, Traces, DTraces, Inv, Invs, DInvs, Prog
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
        deg = Miscs.get_auto_deg(maxdeg, len(maxvars), settings.MAX_TERM)
        return deg

    # def uniqify(self, dinvs):
    #     assert isinstance(dinvs, DInvs) and dinvs, dinvs

    #     mlog.info("uniqify {} invs".format(dinvs.siz))
    #     st = time()
    #     mlog.debug("{}".format(dinvs.__str__(print_stat=True)))
    #     oldSiz = dinvs.siz

    #     # save stats info
    #     statsd = {
    #         loc: {inv.inv: inv.stat for inv in dinvs[loc]} for loc in dinvs}

    #     def wprocess(tasks, Q):
    #         rs = [(loc, Z3.reduceSMT(invs, self.symstates.use_reals))
    #               for loc, invs in tasks]
    #         if Q is None:
    #             return rs
    #         else:
    #             Q.put(rs)

    #     tasks = [(loc, [inv.inv for inv in dinvs[loc]]) for loc in dinvs]
    #     wrs = Miscs.runMP("uniqify", tasks, wprocess, chunksiz=1,
    #                       doMP=settings.doMP and len(tasks) >= 2)

    #     dinvs = DInvs((
    #         loc, Invs(Inv(inv, stat=statsd[loc][inv]) for inv in invs)
    #     ) for loc, invs in wrs if invs)

    #     mlog.debug("uniqify: remove {} redundant invs ({}s)"
    #                .format(oldSiz - dinvs.siz, time() - st))
    #     return dinvs


class DigCegir(Dig):
    OPT_EQTS = "eqts"
    OPT_IEQS = "ieqs"
    OPT_PREPOSTS = "preposts"

    def __init__(self, filename):
        super(DigCegir, self).__init__(filename)

        # call ASM to obtain
        (inp_decls, inv_decls, clsName, mainQName, jpfDir, jpfFile,
         traceDir, traceFile) = srcJava.parse(filename, self.tmpdir)

        self.inp_decls = inp_decls
        self.inv_decls = inv_decls
        self.useRandInit = True

        exeCmd = "java -ea -cp {} {}".format(traceDir, clsName)
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
        deg = super(DigCegir, self).start(seed, maxdeg)
        st = time()
        solver = Cegir(self.symstates, self.prog)
        mlog.debug("check reachability")
        dinvs, traces, inps = solver.check_reach()
        if not traces:
            return dinvs, traces, self.tmpdir

        def _gen(typ):

            st_gen = time()

            if typ == self.OPT_EQTS:
                from cegirEqts import CegirEqts
                cls = CegirEqts
            elif typ == self.OPT_IEQS:
                from cegirIeqs import CegirIeqs
                cls = CegirIeqs
            else:
                assert typ == self.OPT_PREPOSTS
                from cegirPrePosts import CegirPrePosts
                cls = CegirPrePosts

            solver = cls(self.symstates, self.prog)
            if typ == self.OPT_PREPOSTS:
                mlog.info("gen {} from invs ".format(typ, len(traces)))
                invs = solver.gen(dinvs, traces)
            else:
                mlog.info("gen {} at {} locs".format(typ, len(traces)))
                mlog.debug(self.str_of_locs(traces.keys()))
                solver.useRandInit = self.useRandInit
                invs = solver.gen(deg, traces, inps)

            if not invs:
                mlog.warn("found no {}".format(typ))
                return False

            mlog.info("infer {} {} in {}s"
                      .format(invs.siz, typ, time() - st_gen))
            if invs:
                dinvs.merge(invs)
                mlog.debug("{}".format(dinvs.__str__(print_stat=True)))

            return True

        if do_eqts:
            _gen(self.OPT_EQTS)
        if do_ieqs:
            _gen(self.OPT_IEQS)
        if do_preposts:
            _gen(self.OPT_PREPOSTS)

        # post procesing
        mlog.info("check {} invs on {} traces".format(dinvs.siz, traces.siz))
        dinvs = dinvs.test_traces(traces)
        mlog.info("uniqify {} invs".format(dinvs.siz))
        mlog.debug("{}".format(dinvs.__str__(print_stat=True)))
        dinvs = dinvs.uniqify(self.symstates.use_reals)

        result = ("*** '{}', {} locs, invs {} ({} eqts), inps {} "
                  "time {:02f} s, rand {}:\n{}")
        print(result.format(self.filename, len(dinvs),
                            dinvs.siz, dinvs.n_eqs, len(inps),
                            time() - st, sage.all.randint(0, 100),
                            dinvs.__str__(print_stat=False)))

        return dinvs, traces, self.tmpdir


class DigTraces(Dig):
    def __init__(self, filename):
        super(DigTraces, self).__init__(filename)
        from srcTcs import Src
        self.src = Src(filename)
        self.inv_decls = self.src.getInv_decls()

    def start(self, seed, maxdeg, do_eqts, do_ieqs):

        deg = super(DigTraces, self).start(
            seed, maxdeg, do_eqts, do_ieqs)

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
            vs, deg, settings.EQT_RATE)

        exprs = list(traces.instantiate(template, nEqtsNeeded))
        eqts = Miscs.solveEqts(exprs, uks, template)
        for inv in eqts:
            dinvs[loc].add(Inv(inv))

        dtraces = DTraces()
        dtraces[loc] = traces
        inps = Inps()
        self.check(dinvs, dtraces, inps, st)

        return dinvs, None, self.tmpdir

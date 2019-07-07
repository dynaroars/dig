from abc import ABCMeta, abstractmethod
import functools
import pdb
import random
import os.path
import time

import sage.all

import settings
from helpers.miscs import Miscs
import helpers.vcommon as CM
import helpers.src_java

DBG = pdb.set_trace

mlog = CM.getLogger(__name__, settings.logger_level)


class Dig(object):
    __metaclass__ = ABCMeta

    def __init__(self, filename):
        assert os.path.isfile(filename), filename
        mlog.info("analyze '{}'".format(filename))
        self.filename = filename

    @abstractmethod
    def start(self, seed, maxdeg):
        assert maxdeg is None or maxdeg >= 1, maxdeg

        self.seed = seed
        random.seed(seed)
        sage.all.set_random_seed(seed)
        mlog.debug("set seed to: {} (test {} {})".format(
            seed, random.randint(0, 100), sage.all.randint(0, 100)))

        # determine degree
        maxvars = max(self.inv_decls.itervalues(), key=lambda d: len(d))
        self.deg = Miscs.get_auto_deg(maxdeg, len(maxvars), settings.MAX_TERM)

    def sanitize(self, dinvs, dtraces):
        if not dinvs.siz:
            return dinvs

        msg = "test {} invs using {} traces".format(
            dinvs.siz, dtraces.siz)
        mlog.debug(msg)
        st = time.time()
        dinvs = dinvs.test(dtraces)
        mlog.info("{} in {:.2f}s".format(msg, time.time() - st))

        if not dinvs.siz:
            return dinvs

        msg = "uniqify {} invs".format(dinvs.siz)
        mlog.debug(msg)
        mlog.debug("{}".format(dinvs.__str__(
            print_stat=True, print_first_n=20)))
        st = time.time()
        dinvs = dinvs.uniqify(self.inv_decls.use_reals)
        mlog.info("{} in {:.2f}s".format(msg, time.time() - st))
        return dinvs

    def print_results(self, dinvs, dtraces, inps, st):
        result = ("*** '{}', {} locs, "
                  "invs {} ({}), traces {}, inps {}, "
                  "time {:.2f}s, rand seed {}, test {} {}:\n{}")
        print(result.format(
            self.filename, len(dinvs),
            dinvs.siz,
            ', '.join('{}: {}'.format(t, c)
                      for t, c in dinvs.typ_ctr.iteritems()),
            dtraces.siz,
            len(inps) if inps else 0,
            time.time() - st,
            self.seed,
            random.randint(0, 100),
            sage.all.randint(0, 100),
            dinvs.__str__(print_stat=True)))

    @property
    def tmpdir(self):
        try:
            return self._tmpdir
        except AttributeError:
            import tempfile
            self._tmpdir = tempfile.mkdtemp(
                dir=settings.tmpdir, prefix="Dig_")
            return self._tmpdir


class DigSymStates(Dig):
    def __init__(self, filename):
        super(DigSymStates, self).__init__(filename)

        # call ASM to obtain
        (inp_decls, inv_decls, clsname, mainQ_name, jpfdir, jpffile,
         tracedir, traceFile) = helpers.src_java.parse(filename, self.tmpdir)

        self.inp_decls = inp_decls
        self.inv_decls = inv_decls
        self.use_rand_init = True

        import data.miscs
        exe_cmd = settings.JAVA_RUN(tracedir=tracedir, clsname=clsname)
        self.prog = data.miscs.Prog(exe_cmd, inp_decls, inv_decls)

        import data.symstates
        self.symstates = data.symstates.SymStates(inp_decls, inv_decls)
        self.symstates.compute(self.filename, mainQ_name, clsname, jpfdir)

        # remove locations with no symbolic states
        invalid_locs = [loc for loc in inv_decls
                        if loc not in self.symstates.ss]

        for loc in invalid_locs:
            mlog.warn("{}: no symbolic states. Skipping".format(loc))
            self.inv_decls.pop(loc)

        self.locs = self.inv_decls.keys()
        mlog.info("infer invs at {} locs: {}".format(
            len(self.locs), ', '.join(self.locs)))

    def start(self, seed, maxdeg):
        super(DigSymStates, self).start(seed, maxdeg)

        st = time.time()

        from data.traces import Inps, DTraces
        from data.inv.invs import DInvs

        dinvs = DInvs()
        dtraces = DTraces.mk(self.locs)
        inps = Inps()

        mlog.debug("inferring: eqts {}, ieqs {}, min/max {}, preposts {}"
                   .format(settings.DO_EQTS, settings.DO_IEQS,
                           settings.DO_MINMAXPLUS, settings.DO_PREPOSTS))

        if settings.DO_EQTS:
            self.infer('eqts', dinvs, lambda: self.infer_eqts(dtraces, inps))

        if settings.DO_IEQS or settings.DO_MINMAXPLUS:
            self.infer('ieqs', dinvs, lambda: self.infer_ieqs(dtraces, inps))

        dinvs = self.sanitize(dinvs, dtraces)

        if dinvs.n_eqs and settings.DO_PREPOSTS:
            self.infer('preposts', dinvs,
                       lambda: self.infer_preposts(dinvs, dtraces))

        self.print_results(dinvs, dtraces, inps, st)

        tracefile = os.path.join(self.tmpdir, settings.TRACE_DIR, 'all.tcs')
        dtraces.vwrite(self.inv_decls, tracefile)

        return dinvs, dtraces, self.tmpdir

    def infer(self, typ, dinvs, f):
        mlog.debug("infer '{}' at {} locs".format(typ, len(self.locs)))

        st = time.time()
        new_invs = f()
        if not new_invs.siz:
            mlog.warn("found no {}".format(typ))
        else:
            mlog.info("found {} {} in {:.2f}s".format(
                new_invs.siz, typ, time.time() - st))

            dinvs.merge(new_invs)
            mlog.debug('{}'.format(dinvs.__str__(
                print_stat=True, print_first_n=20)))

    def infer_eqts(self, dtraces, inps):
        from cegir.eqt import CegirEqt
        solver = CegirEqt(self.symstates, self.prog)
        solver.use_rand_init = self.use_rand_init
        return solver.gen(self.deg, dtraces, inps)

    def infer_ieqs(self, dtraces, inps):
        from cegir.binsearch import CegirBinSearch
        solver = CegirBinSearch(self.symstates, self.prog)
        return solver.gen(dtraces, inps)

    def infer_preposts(self, dinvs, dtraces):
        from cegir.prepost import CegirPrePost
        solver = CegirPrePost(self.symstates, self.prog)
        return solver.gen(dinvs, dtraces)

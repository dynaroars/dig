from abc import ABCMeta, abstractmethod
import vcommon as CM
from ds import Inps, Prog
from invs import DInvs

import settings
mlog = CM.getLogger(__name__, settings.logger_level)


class Cegir(object):
    __metaclass__ = ABCMeta

    def __init__(self, symstates, prog):
        assert isinstance(prog, Prog), prog

        self.symstates = symstates
        self.inv_decls = symstates.inv_decls
        self.inp_decls = symstates.inp_decls
        self.prog = prog

    def getTracesAndUpdate(self, inps, traces):
        assert isinstance(inps, Inps) and inps, inps
        newTraces = self.prog.get_traces(inps)
        newTraces = newTraces.update(traces)
        return newTraces

    def check_reach(self):
        """
        check if inv location is reachable
        by using inv False (0)
        """

        dinvs = DInvs.mk_false_invs(self.inv_decls)
        inps = Inps()
        # use some initial inps first
        rinps = self.symstates.genRandInps(self.prog)

        mlog.debug("gen {} random inps".format(len(rinps)))
        _ = inps.myupdate(rinps, self.inp_decls.names)
        traces = self.prog.get_traces(inps)
        unreachLocs = [loc for loc in dinvs if loc not in traces]

        if unreachLocs:
            mlog.debug("use RT to generate traces for {} locs: {}".format(
                len(unreachLocs), ','.join(map(str, unreachLocs))))
            unreachInvs = DInvs.mk_false_invs(unreachLocs)
            cexs, _ = self.symstates.check(unreachInvs, inps)
            newInps = inps.myupdate(cexs, self.inp_decls.names)
            mlog.debug(newInps.__str__(printDetails=True))
            self.getTracesAndUpdate(newInps, traces)

        # remove FALSE invs indicating unreached locs
        for loc in traces:
            assert traces[loc]
            dinvs[loc].clear()
        return dinvs, traces, inps

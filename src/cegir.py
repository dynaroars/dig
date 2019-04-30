from abc import ABCMeta, abstractmethod
import vcommon as CM
from ds import Inps, Traces, Inv, Invs, DInvs, Prog

import settings
mlog = CM.getLogger(__name__, settings.logger_level)


class Cegir(object):
    __metaclass__ = ABCMeta

    def __init__(self, symstates, prog):
        assert isinstance(prog, Prog), prog

        self.symstates = symstates
        self.invDecls = symstates.invDecls
        self.inpDecls = symstates.inpDecls
        self.prog = prog

    def getTracesAndUpdate(self, inps, traces):
        assert isinstance(inps, Inps) and inps, inps
        newTraces = self.prog.getTraces(inps)
        newTraces = newTraces.update(traces)
        return newTraces

    def checkReach(self):
        # check for reachability using inv False (0)
        dinvs = DInvs.mkFalses(self.invDecls)
        inps = Inps()

        # use some initial inps first
        rinps = self.symstates.genRandInps(self.prog)

        mlog.debug("gen {} random inps".format(len(rinps)))
        _ = inps.myupdate(rinps, self.inpDecls.names)
        traces = self.prog.getTraces(inps)
        unreachLocs = [loc for loc in dinvs if loc not in traces]

        if unreachLocs:
            mlog.debug("use RT to generate traces for {} locs: {}".format(
                len(unreachLocs), ','.join(map(str, unreachLocs))))
            unreachInvs = DInvs.mkFalses(unreachLocs)
            cexs, _ = self.symstates.check(unreachInvs, inps)
            newInps = inps.myupdate(cexs, self.inpDecls.names)
            mlog.debug(newInps.__str__(printDetails=True))
            _ = self.getTracesAndUpdate(newInps, traces)

        # remove FALSE invs indicating unreached locs
        for loc in traces:
            assert traces[loc]
            dinvs[loc].clear()
        return dinvs, traces, inps

"""
CEGIR algorithm
"""

from abc import ABCMeta, abstractmethod
import pdb

import helpers.vcommon as CM
import settings

from data.miscs import Prog
from data.traces import Inps, DTraces
from data.inv.base import DInvs


DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


class Cegir(object):
    __metaclass__ = ABCMeta

    def __init__(self, symstates, prog):
        assert isinstance(prog, Prog), prog

        self.symstates = symstates
        self.inv_decls = symstates.inv_decls
        self.inp_decls = symstates.inp_decls
        self.prog = prog

    @abstractmethod
    def gen(self):
        pass

    def get_traces(self, inps, traces):
        """
        run inps to get new traces (and update them)
        """
        assert isinstance(inps, Inps) and inps, inps
        assert isinstance(traces, DTraces), traces

        new_traces = self.prog.get_traces(inps)
        new_traces = new_traces.update(traces)
        return new_traces


class CegirReachability(Cegir):
    def gen(self):
        """
        check if inv location is reachable
        by using inv False (0)
        """

        dinvs = DInvs.mk_false_invs(self.inv_decls)
        inps = Inps()

        # use some initial inps first
        rinps = self.prog.gen_rand_inps()

        mlog.debug("gen {} random inps".format(len(rinps)))
        _ = inps.myupdate(rinps, self.inp_decls.names)
        traces = self.prog.get_traces(inps)
        unreach_locs = [loc for loc in dinvs if loc not in traces]

        if unreach_locs:
            mlog.debug("use RT to generate traces for {} locs: {}".format(
                len(unreach_locs), ','.join(map(str, unreach_locs))))
            unreach_invs = DInvs.mk_false_invs(unreach_locs)
            cexs, _ = self.symstates.check(unreach_invs, inps)
            newInps = inps.myupdate(cexs, self.inp_decls.names)
            mlog.debug(newInps.__str__(printDetails=True))
            self.get_traces(newInps, traces)

        # remove FALSE invs indicating unreached locs
        for loc in traces:
            assert traces[loc]
            dinvs[loc].clear()
        return dinvs, traces, inps

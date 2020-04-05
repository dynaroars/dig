"""
CEGIR algorithm
"""

from abc import ABCMeta, abstractmethod
import pdb

import helpers.vcommon as CM
import settings

import data.prog
from data.traces import Inps, DTraces
from data.inv.base import Inv
from data.inv.invs import DInvs
import data.symstates

DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


class Cegir(metaclass=ABCMeta):
    def __init__(self, symstates, prog):
        assert isinstance(symstates, data.symstates.SymStates), symstates
        assert isinstance(prog, data.prog.Prog), prog

        self.symstates = symstates
        self.inv_decls = prog.inv_decls
        self.inp_decls = prog.inp_decls
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
        new_traces = traces.merge(new_traces)
        return new_traces

    def check(self, dinvs, inps, check_mode=data.symstates.SymStates.check_validity):
        if self.symstates:
            cexs, dinvs, stats = self.symstates.check(dinvs, inps, check_mode)
        else:
            # no symbolic states, not performing checking
            for loc in dinvs:
                for inv in dinvs[loc]:
                    inv.stat = Inv.UNKNOWN
            cexs = {}
            stats = []
        return cexs, dinvs, stats

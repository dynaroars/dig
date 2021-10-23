import abc
import pdb

import helpers.vcommon as CM
import settings

import prog
import traces
import inv.inv
import symstates

DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


class Infer(metaclass=abc.ABCMeta):
    def __init__(self, symstates, prog):
        assert symstates is None or \
            isinstance(symstates, symstates.SymStates), symstates
        assert isinstance(prog, prog.Prog), prog

        self.symstates = symstates
        self.inv_decls = prog.inv_decls
        self.inp_decls = prog.inp_decls
        self.prog = prog

    @abc.abstractmethod
    def gen(self):
        pass

    @classmethod
    @abc.abstractmethod
    def gen_from_traces(cls, traces, symbols):
        pass

    def get_traces(self, inps, dtraces):
        """
        run inps to get new traces (and update them)
        """
        assert isinstance(inps, traces.Inps) and inps, inps
        assert isinstance(dtraces, traces.DTraces), dtraces

        new_dtraces = self.prog.get_traces(inps)
        new_dtraces = dtraces.merge(new_dtraces)
        return new_dtraces

    def check(self, dinvs, inps):
        if self.symstates:
            cexs, dinvs = self.symstates.check(dinvs, inps)
        else:
            # no symbolic states, not performing checking
            for loc in dinvs:
                for inv in dinvs[loc]:
                    inv.stat = inv.inv.Inv.UNKNOWN
            cexs = {}
        return cexs, dinvs

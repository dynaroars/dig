import pdb
from time import time

import vcommon as CM
import settings
from helpers.miscs import Miscs

import invs
import invs_eqts
import invs_ieqs
import alg

dbg = pdb.set_trace

mlog = CM.getLogger(__name__, settings.logger_level)


class DigTraces(alg.Dig):
    def __init__(self, tracefile):
        super(DigTraces, self).__init__(tracefile)

        import ds_traces
        self.inv_decls, self.dtraces = ds_traces.DTraces.vread(tracefile)

    def start(self, seed, maxdeg,
              do_eqts, do_ieqs, do_maxminplus, do_preposts):

        super(DigTraces, self).start(seed, maxdeg)

        st = time()
        dinvs = invs.DInvs()
        for loc in self.dtraces:
            symbols = self.inv_decls[loc]
            dinvs[loc] = invs.Invs()
            traces = self.dtraces[loc]

            if do_eqts:
                terms, template, uks, n_eqts_needed = Miscs.init_terms(
                    symbols.names, self.deg, settings.EQT_RATE)
                exprs = list(traces.instantiate(template, n_eqts_needed))
                eqts = Miscs.solve_eqts(exprs, uks, template)
                for eqt in eqts:
                    dinvs[loc].add(invs_eqts.EqtInv(eqt))

            if do_ieqs:
                maxV = settings.OCT_MAX_V
                minV = -1*maxV

                oct_siz = 2
                terms = Miscs.get_terms_fixed_coefs(symbols.sageExprs, oct_siz)
                for t in terms:
                    upperbound = max(traces.myeval(t))
                    if upperbound > maxV or upperbound < minV:
                        continue

                    ieq = t <= upperbound
                    dinvs[loc].add(invs_ieqs.IeqInv(ieq))

        dinvs = self.sanitize(dinvs, self.dtraces)
        self.print_results(dinvs, self.dtraces, None, st)
        return dinvs, None, self.tmpdir

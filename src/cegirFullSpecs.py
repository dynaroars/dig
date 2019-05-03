import vcommon as CM
from cegir import Cegir
from ds import Inps, Traces, DTraces, Inv, Invs, DInvs
import sage.all
from miscs import Miscs
import settings
import pdb
trace = pdb.set_trace

mlog = CM.getLogger(__name__, settings.logger_level)


class CegirFullSpecs(Cegir):
    def __init__(self, symstates, prog):

        super(CegirFullSpecs, self).__init__(symstates, prog)

    def gen(self, dinvs, traces):
        assert isinstance(dinvs, DInvs), dinvs
        assert isinstance(traces, DTraces), traces

        eqts = {}  # eqt -> set([locs])
        for loc in dinvs:
            if settings.POST_LOC not in loc:
                continue
            for inv in dinvs[loc]:
                myinv = inv.inv
                if myinv.operator() == sage.all.operator.eq:
                    if myinv not in eqts:
                        eqts[myinv] = set()
                    eqts[myinv].add(loc)

        if not eqts:
            mlog.warn("no eqt postconds, skip full specs generation")
            return

        dinvs_ = {}
        for eqt in eqts:
            disjss = self.getDisjs(eqt)
            if not disjss:
                continue

            trace()

    def getDisjs(self, eqt):
        symbols = Miscs.getVars(eqt)  # x,y,z

        # if symbols contains a special symbol, e.g., 'tCtr', then only consider that
        symbols_ = [s for s in symbols if settings.CTR_VAR in str(s)]
        if symbols_:
            assert len(symbols_) == 1
            symbols = symbols_

        disjss = [sage.all.solve(eqt, s) for s in symbols]
        # len(disjs) >= 2 indicate disj, e.g., x^2 = 1 -> [x=1,x=-1]
        disjss = [disjs for disjs in disjss if len(disjs) >= 2]
        return disjss


# fs_analysis = FullSpecsAnalysis(
#     dinvs, traces, self.inpDecls, self.symstates)
# fs_analysis.go()

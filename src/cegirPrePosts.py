import vcommon as CM
from cegir import Cegir
from ds import Inps, Traces, DTraces, Inv, Invs, DInvs, PrePostInv
import sage.all
import z3
from miscs import Miscs, Z3
import settings
import pdb
trace = pdb.set_trace

mlog = CM.getLogger(__name__, settings.logger_level)


class CegirPrePosts(Cegir):
    def __init__(self, symstates, prog):
        super(CegirPrePosts, self).__init__(symstates, prog)

    def gen(self, dinvs, traces):
        assert isinstance(dinvs, DInvs), dinvs
        assert isinstance(traces, DTraces), traces

        dinvs_ = DInvs()
        cache = {}
        for loc in dinvs:
            if settings.POST_LOC not in loc:
                continue

            for inv in dinvs[loc]:
                if not inv.isEq:
                    continue
                if inv in cache:
                    preposts = cache[inv]
                else:
                    disjss = self.getDisjs(inv.inv)
                    preposts = self.getPrePosts(loc, disjss, traces)
                    cache[inv] = preposts

                if preposts:
                    if loc not in dinvs_:
                        dinvs_[loc] = Invs()
                    for prepost in preposts:
                        dinvs_[loc].add(prepost)

        return dinvs_

    def getPrePosts(self, loc, disjss, traces):
        mydisjs = [disj for disjs in disjss for disj in disjs]

        def toZ3(x):
            return Z3.toZ3(x, self.symstates.useReals, useMod=False)

        preposts = []  # results
        for disj in mydisjs:
            tcs = [t for t in traces[loc] if t.test(disj)]
            preconds = [c for c in self.preconds
                        if all(t.test(c) for t in tcs)]

            if not preconds:
                continue

            precond = z3.And([toZ3(pc) for pc in
                              Z3.reduceSMT(preconds, self.symstates.useReals)])
            inv = z3.Implies(precond, toZ3(disj))

            _, cexs, isSucc = self.symstates.mcheckD(
                loc, pathIdx=None, inv=inv, inps=None)

            if cexs or not isSucc:
                mlog.warn("{}: remove spurious result {}".format(loc, inv))

            preconds = [Inv(c) for c in preconds]
            prepost = PrePostInv(disj, Invs.mk(preconds))
            preposts.append(prepost)

        return preposts

    @property
    def preconds(self):
        symbols = self.symstates.inpDecls.sageExprs
        import itertools
        ssSiz = 2
        ts1 = [t == 0 for t in symbols]  # M=0, N=0
        ts2 = [x == y for x, y in
               itertools.combinations(symbols, ssSiz)]  # M==N
        ts3 = [t > 0 for t in
               Miscs.getTermsFixedCoefs(symbols, ssSiz)]  # +/M+/-N >0
        return ts1 + ts2 + ts3

    def getDisjs(self, eqt):
        symbols = Miscs.getVars(eqt)  # x,y,z

        # if special symbols, e.g., tCtr, exist, then only consider those
        symbols_ = [s for s in symbols if settings.CTR_VAR in str(s)]
        if symbols_:
            assert len(symbols_) == 1
            symbols = symbols_

        disjss = [sage.all.solve(eqt, s) for s in symbols]
        # len(disjs) >= 2 indicate disj, e.g., x^2 = 1 -> [x=1,x=-1]
        disjss = [disjs for disjs in disjss if len(disjs) >= 2]
        return disjss

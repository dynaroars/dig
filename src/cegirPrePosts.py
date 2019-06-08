import itertools
import operator
import pdb
import z3

import sage.all

import vcommon as CM
import settings
from miscs import Miscs, Z3

from cegir import Cegir
from ds import DTraces, Traces
from invs import Inv, PrePostInv, EqtInv, IeqInv, Invs, DInvs


dbg = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


class CegirPrePosts(Cegir):
    def __init__(self, symstates, prog):
        super(CegirPrePosts, self).__init__(symstates, prog)
        self.use_reals = symstates.use_reals

    @property
    def preconds(self):
        symbols = self.symstates.inp_decls.sageExprs
        siz = 2
        t1 = [EqtInv(t == 0) for t in symbols]  # M=0, N=0
        t2 = [EqtInv(x == y)
              for x, y in itertools.combinations(symbols, siz)]  # M==N
        t3 = [IeqInv(t < 0)  # +/M+/-N >0
              for t in Miscs.get_terms_fixed_coefs(symbols, siz)]
        t4 = [IeqInv(t <= 0)
              for t in Miscs.get_terms_fixed_coefs(symbols, siz)]
        return t1 + t2 + t3 + t4

    def gen(self, dinvs, traces):
        assert isinstance(dinvs, DInvs), dinvs
        assert isinstance(traces, DTraces), traces

        dinvs_ = DInvs()
        cache = {}
        for loc in dinvs:
            if settings.POST_LOC not in loc:
                continue

            for inv in dinvs[loc]:
                if not isinstance(inv, EqtInv):
                    continue

                if inv in cache:
                    preposts = cache[inv]
                else:
                    disjss = self.get_disjs(inv.inv)
                    print(disjss)
                    preposts = self.get_preposts(loc, disjss, traces[loc])
                    print(preposts)
                    cache[inv] = preposts

                if preposts:
                    if loc not in dinvs_:
                        dinvs_[loc] = Invs()
                    for prepost in preposts:
                        dinvs_[loc].add(prepost)

        return dinvs_

    def get_preposts(self, loc, disjss, traces):
        assert isinstance(loc, str), loc
        assert disjss, disjss
        assert isinstance(traces, Traces), traces

        mydisjs = [disj for disjs in disjss for disj in disjs]
        assert all(disj.operator() == operator.eq for disj in mydisjs), mydisjs
        mydisjs = [EqtInv(disj) for disj in mydisjs]
        disjs_traces = {disj: traces.get_satisfying_traces(disj)
                        for disj in mydisjs}

        common_traces = set.intersection(*disjs_traces.values())
        if common_traces:
            # print 'common traces', i_traces.__str__(True)
            for disj in mydisjs:
                disjs_traces[disj] = disjs_traces[disj] - common_traces
                if not disjs_traces[disj]:
                    del disjs_traces[disj]

        print 'preconds', self.preconds
        preposts = []  # results
        for disj in disjs_traces:
            # print 'disj', disj
            # print disjs_traces[disj].__str__(True)
            preconds = [pc for pc in self.preconds
                        if pc.test(disjs_traces[disj])]
            preconds = self.strengthen_preconds(loc, preconds, disj)
            preconds = Invs(preconds)
            if not preconds:
                continue
            prepost = PrePostInv(preconds, disj, stat=Inv.PROVED)
            # print 'prepost', prepost
            preposts.append(prepost)

        return preposts

    def strengthen_preconds(self, loc, preconds, postcond):
        """
        preconds  =>  post  can be strengthened by removing some preconds
        e.g., a&b => post is stronger than a&b&c => post
        """
        assert all(isinstance(p, Inv) for p in preconds), preconds

        if not preconds:
            return []

        d = {p.expr(self.use_reals): p for p in preconds}
        postcond_expr = postcond.expr(self.use_reals)

        def check(fs):
            inv = z3.Implies(z3.And(fs), postcond_expr)
            _, cexs, isSucc = self.symstates.mcheckD(
                loc, pathIdx=None, inv=inv, inps=None)

            if cexs or not isSucc:
                mlog.warn("{}: discard spurious result {}".format(loc, inv))
                return False
            return True

        preconds_exprs = [c.expr(self.use_reals) for c in preconds]
        if not check(preconds_exprs):
            return []
        preconds_exprs = sorted(preconds_exprs, cmp=Z3._mycmp_, reverse=True)
        results = range(len(preconds_exprs))

        for i, _ in enumerate(preconds_exprs):
            if i not in results:
                continue
            xclude = [j for j in results if j != i]
            if check([preconds_exprs[j] for j in xclude]):
                results = xclude

        results = [d[preconds_exprs[j]] for j in results]
        return results

    def get_disjs(self, eqt):
        assert eqt.operator() == operator.eq, eqt

        symbols = Miscs.getVars(eqt)  # x,y,z

        # if special symbols, e.g., tCtr, exist, then only consider those
        symbols_ = [s for s in symbols if settings.CTR_VAR in str(s)]
        if symbols_:
            assert len(symbols_) == 1, "should only have 1 special symbol"
            symbols = symbols_

        disjss = [sage.all.solve(eqt, s) for s in symbols]

        # len(disjs) >= 2 indicate disj, e.g., x^2 = 1 -> [x=1,x=-1]
        disjss = [disjs for disjs in disjss if len(disjs) >= 2]
        return disjss

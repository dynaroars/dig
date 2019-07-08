import operator
import pdb

import z3
import sage.all
import helpers.vcommon as CM
from helpers.miscs import Miscs

import settings
from cegir.base import Cegir
from data.traces import DTraces, Traces
from data.inv.base import Inv
from data.inv.invs import Invs, DInvs
from data.inv.eqt import Eqt
from data.inv.oct import Oct
from data.inv.prepost import PrePost

DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


class CegirPrePost(Cegir):
    def __init__(self, symstates, prog):
        super(CegirPrePost, self).__init__(symstates, prog)
        self.use_reals = symstates.use_reals

    @property
    def preconds(self):
        symbols = self.symstates.inp_decls.sageExprs
        return self._preconds(symbols, term_siz=2)

    @classmethod
    def _preconds(cls, symbols, term_siz):
        """
        sage: x,y,z = sage.all.var('x y z')
        sage: sorted(CegirPrePosts._preconds([x,y], 2), key=str) #doctest: +NORMALIZE_WHITESPACE
        [-x + y < 0,
         -x + y <= 0,
         -x - y < 0,
         -x - y <= 0,
         -x < 0,
         -x <= 0,
         -y < 0,
         -y <= 0,
         x + y < 0,
         x + y <= 0,
         x - y < 0,
         x - y <= 0,
         x < 0,
         x <= 0,
         x == 0,
         y < 0,
         y <= 0,
         y == 0]

        """
        t1 = [Eqt(t == 0) for t in symbols]  # M=0, N=0
        t2 = [Oct(t < 0)  # +/M+/-N >0
              for t in Miscs.get_terms_fixed_coefs(symbols, term_siz)]
        t3 = [Oct(t <= 0)  # +/M+/-N >=0
              for t in Miscs.get_terms_fixed_coefs(symbols, term_siz)]
        return t1 + t2 + t3

    def gen(self, dinvs, traces):
        assert isinstance(dinvs, DInvs), dinvs
        assert isinstance(traces, DTraces), traces

        dinvs_ = DInvs()
        for loc in dinvs:
            if settings.POST_LOC not in loc:
                continue

            disjs = [self.get_disjs(inv.inv) for inv in dinvs[loc]
                     if isinstance(inv, Eqt)]
            disjs = [disj for disj in disjs if disj]
            disjs = [d for disj in disjs for d in disj]
            preposts = self.get_preposts(loc, set(disjs), traces[loc])
            if preposts:
                dinvs_[loc] = Invs(preposts)

        return dinvs_

    def get_preposts(self, loc, disjs, traces):
        assert isinstance(loc, str), loc
        assert disjs, disjs
        assert all(disj.operator() == operator.eq for disj in disjs), disjs
        assert isinstance(traces, Traces), traces

        mydisjs = [Eqt(disj) for disj in disjs]
        mytraces = {d: Traces([t for t in traces if d.test_single_trace(t)])
                    for d in mydisjs}
        preposts = []  # results
        for disj in mytraces:
            preconds = [pc for pc in self.preconds if pc.test(mytraces[disj])]
            preconds = self.strengthen(loc, preconds, disj)
            if not preconds:
                continue
            prepost = PrePost(Invs(preconds), disj, stat=Inv.PROVED)
            preposts.append(prepost)
        return preposts

    def strengthen(self, loc, preconds, postcond):
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
            cexs, isSucc = self.symstates._mcheck_d(
                loc, path_idx=None, inv=inv, inps=None)

            if cexs or not isSucc:
                mlog.warn("{}: discard spurious result {}".format(loc, inv))
                return False
            return True

        preconds_exprs = list(d.keys())
        if not check(preconds_exprs):
            return []
        results = range(len(preconds_exprs))
        for i, _ in enumerate(preconds_exprs):
            if i not in results:
                continue
            xclude = [j for j in results if j != i]
            xclude_exprs = [preconds_exprs[j] for j in xclude]
            #print 'exclude exprs', preconds_exprs[i], xclude_exprs
            if xclude_exprs and check(xclude_exprs):
                #print 'exclude', preconds_exprs[i]
                results = xclude
            # else:
            #     print 'cannot exclude', preconds_exprs[i]

        results = [d[preconds_exprs[j]] for j in results]
        return results

    @classmethod
    def get_disjs(cls, eqt):
        assert Miscs.is_expr(eqt), eqt
        assert eqt.operator() == operator.eq, eqt

        symbols = [s for s in Miscs.getVars(eqt)
                   if settings.CTR_VAR in str(s)]
        assert len(symbols) == 1, "should only have 1 special symbol"
        ct_symbol = symbols[0]

        disjs = sage.all.solve(eqt, ct_symbol)
        if len(disjs) >= 2:
            # len(disjs) >= 2 indicate disj, e.g., x^2 = 1 -> [x=1,x=-1]
            return disjs
        else:
            return None

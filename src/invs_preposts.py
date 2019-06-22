import operator
import pdb
import z3

import sage.all

import vcommon as CM
import settings
from miscs import Miscs

from cegir import Cegir
from ds_traces import DTraces, Traces
from invs import Inv, Invs, DInvs
from invs_eqts import EqtInv
from invs_ieqs import IeqInv


dbg = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


class PrePostInv(Inv):
    """
    Set of Preconds  -> PostInv
    """

    def __init__(self, preconds, postcond, stat=None):
        assert isinstance(preconds, Invs), preconds
        assert postcond.is_eqt, postcond

        super(PrePostInv, self).__init__(
            (frozenset(preconds), postcond), stat)

        self.preconds = preconds
        self.postcond = postcond

    @property
    def is_prepost(self):
        return True

    def expr(self, use_reals):
        """
        And(preconds) -> postcond
        """
        pre = z3.And([c.expr(use_reals) for c in self.preconds])
        post = c.expr(use_reals)
        return z3.Implies(pre, post)

    def __str__(self, print_stat=False):
        return "{} => {} {}".format(
            self.preconds.__str__(delim=" & "), self.postcond, self.stat)


class CegirPrePosts(Cegir):
    def __init__(self, symstates, prog):
        super(CegirPrePosts, self).__init__(symstates, prog)
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
        t1 = [EqtInv(t == 0) for t in symbols]  # M=0, N=0
        t2 = [IeqInv(t < 0)  # +/M+/-N >0
              for t in Miscs.get_terms_fixed_coefs(symbols, term_siz)]
        t3 = [IeqInv(t <= 0)  # +/M+/-N >=0
              for t in Miscs.get_terms_fixed_coefs(symbols, term_siz)]
        return t1 + t2 + t3

    def gen(self, dinvs, traces):
        assert isinstance(dinvs, DInvs), dinvs
        assert isinstance(traces, DTraces), traces

        dinvs_ = DInvs()
        for loc in dinvs:
            if settings.POST_LOC not in loc:
                continue

            mydisjs = []
            for inv in dinvs[loc]:
                if not isinstance(inv, EqtInv):
                    continue

                disjss = self.get_disjs(inv.inv)
                mydisjs.extend([disj for disjs in disjss for disj in disjs])

            preposts = self.get_preposts(loc, set(mydisjs), traces[loc])
            if preposts:
                dinvs_[loc] = Invs(preposts)

        return dinvs_

    def get_preposts(self, loc, disjs, traces):
        assert isinstance(loc, str), loc
        assert disjs, disjs
        assert all(disj.operator() == operator.eq for disj in disjs), disjs
        assert isinstance(traces, Traces), traces
        print 'orig', disjs
        mydisjs = [EqtInv(disj) for disj in disjs]
        disjs_traces = {d: traces.get_satisfying_traces(d) for d in mydisjs}
        print disjs_traces

        # for k1, k2 in itertools.combinations(disjs_traces.keys(), 2):
        #     common_traces = disjs_traces[k1] & disjs_traces[k2]
        #     if common_traces:
        #         disjs_traces[k1] = disjs_traces[k1] - common_traces
        #         disjs_traces[k2] = disjs_traces[k2] - common_traces
        # disjs_traces = {d: disjs_traces[d]
        #                 for d in disjs_traces if disjs_traces[d]}

        preposts = []  # results
        for disj in disjs_traces:
            print 'disj', disj

            preconds = []
            for pc in self.preconds:
                if pc.test(disjs_traces[disj]):
                    preconds.append(pc)
                else:
                    print 'discard', pc

            print disjs_traces[disj].__str__(True)
            print 'preconds', preconds
            preconds = self.strengthen_preconds(loc, preconds, disj)
            print 'preconds simplified', preconds
            preconds = Invs(preconds)
            if not preconds:
                continue
            prepost = PrePostInv(preconds, disj, stat=Inv.PROVED)
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
            cexs, isSucc = self.symstates._mcheck_d(
                loc, path_idx=None, inv=inv, inps=None)

            if cexs or not isSucc:
                mlog.warn("{}: discard spurious result {}".format(loc, inv))
                return False
            return True

        preconds_exprs = [c.expr(self.use_reals) for c in preconds]
        if not check(preconds_exprs):
            return []
        #preconds_exprs = sorted(preconds_exprs, cmp=Z3._mycmp_, reverse=True)
        print preconds_exprs
        results = range(len(preconds_exprs))

        for i, _ in enumerate(preconds_exprs):
            if i not in results:
                continue
            xclude = [j for j in results if j != i]
            xclude_exprs = [preconds_exprs[j] for j in xclude]
            print 'exclude exprs', preconds_exprs[i], xclude_exprs
            if xclude_exprs and check(xclude_exprs):
                print 'exclude', preconds_exprs[i]
                results = xclude
            else:
                print 'cannot exclude', preconds_exprs[i]

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

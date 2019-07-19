import operator
import pdb

import z3
import sage.all
import helpers.vcommon as CM
from helpers.miscs import Miscs

import settings
import cegir.base
import data.traces
import data.inv.base
import data.inv.invs
import data.inv.eqt
from data.inv.oct import Oct
from data.inv.prepost import PrePost

DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


class CegirPrePost(cegir.base.Cegir):
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
        #doctest: +NORMALIZE_WHITESPACE
        sage: sorted(CegirPrePosts._preconds([x,y], 2), key=str)
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
        t1 = [data.inv.eqt.Eqt(t == 0) for t in symbols]  # M=0, N=0
        t2 = [Oct(t < 0)  # +/M+/-N >0
              for t in Miscs.get_terms_fixed_coefs(symbols, term_siz)]
        t3 = [Oct(t <= 0)  # +/M+/-N >=0
              for t in Miscs.get_terms_fixed_coefs(symbols, term_siz)]
        return t1 + t2 + t3

    def gen(self, dinvs, traces):
        assert isinstance(dinvs, data.inv.invs.DInvs), dinvs
        assert isinstance(traces, data.traces.DTraces), traces
        dinvs_ = data.inv.invs.DInvs()

        post_locs = [loc for loc in dinvs if settings.POST_LOC in loc]
        for loc in post_locs:
            disjs = [self.get_postconds(inv.inv) for inv in dinvs[loc]
                     if isinstance(inv, data.inv.eqt.Eqt)]
            disjs = [disj for disj in disjs if disj]
            disjs = sorted(set(d for disj in disjs for d in disj),
                           key=lambda d: len(str(d)))
            preposts = self.get_preposts(loc, disjs, traces[loc])
            if preposts:
                dinvs_[loc] = data.inv.invs.Invs(preposts)

        return dinvs_

    def get_preposts(self, loc, postconds, traces):
        assert isinstance(loc, str), loc
        assert isinstance(postconds, list), postconds
        assert all(disj.operator() ==
                   operator.eq for disj in postconds), postconds
        assert isinstance(traces, data.traces.Traces), traces

        mypostconds = [data.inv.eqt.Eqt(disj) for disj in postconds]
        mytraces = {d: data.traces.Traces([t for t in traces if d.test_single_trace(t)])
                    for d in mypostconds}
        mypostconds = sorted(
            mypostconds, key=lambda d: len(mytraces[d]), reverse=True)

        preposts = []  # results
        idxs = range(len(mypostconds))

        for idx in idxs:
            other_idxs = idxs[:idx] + idxs[idx+1:]
            curr_post = mypostconds[idx]
            other_posts = [mypostconds[i] for i in other_idxs]

            mytraces_ = [t for t in mytraces[curr_post]
                         if all(t not in mytraces[other_post]
                                for other_post in other_posts)]

            mytraces_ = data.traces.Traces(mytraces_)
            preconds = [pc for pc in self.preconds if pc.test(mytraces_)]
            preconds = self.get_conj_preconds(loc, preconds, curr_post)
            #print '{}: preconds {}'.format(curr_post, preconds)
            if preconds:
                prepost = PrePost(data.inv.invs.Invs(preconds),
                                  curr_post, stat=data.inv.invs.Inv.PROVED)
                preposts.append(prepost)
            else:
                preconds = self.get_disj_preconds(loc, curr_post, traces)
                if preconds:
                    prepost = PrePost(data.inv.invs.Invs(preconds),
                                      curr_post, stat=data.inv.invs.Inv.PROVED)
                    prepost.is_conj = False
                    preposts.append(prepost)

        preposts = data.inv.invs.Invs(preposts)
        return preposts

    def check(self, pcs, postcond_expr, loc):
        precond_expr = z3.And(pcs) if isinstance(pcs, list) else pcs
        inv = z3.Implies(precond_expr, postcond_expr)
        cexs, isSucc = self.symstates._mcheck_d(
            loc, path_idx=None, inv=inv, inps=None)

        if cexs or not isSucc:
            mlog.warn("{}: discard spurious result {}".format(loc, inv))
            return False
        return True

    def get_disj_preconds(self, loc, postcond, traces):
        postcond_expr = postcond.expr(self.use_reals)
        preconds = []

        def isOK(pre, post):
            ret = False
            for t in traces:
                if pre.test_single_trace(t):
                    ret = True
                    if not post.test_single_trace(t):
                        return False
            return ret

        for pc in self.preconds:
            # pc => postcond    ~>   ~pc or postcond
            if isOK(pc, postcond):
                if self.check(pc.expr(self.use_reals), postcond_expr, loc):
                    preconds.append(pc)

        if len(preconds) >= 2:
            is_conj = False
            preconds = data.inv.invs.Invs._simplify(
                preconds, is_conj, self.use_reals)
        return preconds

    def get_conj_preconds(self, loc, preconds, postcond):
        """
        preconds  =>  post  can be strengthened by removing some preconds
        e.g., a&b => post is stronger than a&b&c => post
        """
        assert all(isinstance(p, data.inv.base.Inv)
                   for p in preconds), preconds

        if not preconds:
            return []

        d = {p.expr(self.use_reals): p for p in preconds}
        postcond_expr = postcond.expr(self.use_reals)

        preconds_exprs = list(d.keys())
        if not self.check(preconds_exprs, postcond_expr, loc):
            return []
        results = range(len(preconds_exprs))
        for i, _ in enumerate(preconds_exprs):
            if i not in results:
                continue
            xclude = [j for j in results if j != i]
            xclude_exprs = [preconds_exprs[j] for j in xclude]
            if xclude_exprs and self.check(xclude_exprs, postcond_expr, loc):
                results = xclude

        results = [d[preconds_exprs[j]] for j in results]
        return results

    @classmethod
    def get_postconds(cls, eqt):
        assert Miscs.is_expr(eqt), eqt
        assert eqt.operator() == operator.eq, eqt

        symbols = [s for s in Miscs.getVars(eqt)
                   if settings.CTR_VAR in str(s)]

        if not symbols:
            return

        assert len(symbols) == 1, \
            "should only have 1 special symbol: {}".format(symbols)

        ct_symbol = symbols[0]

        postconds = sage.all.solve(eqt, ct_symbol)
        if len(postconds) >= 1:
            # len(postconds) >= 2 indicate disj, e.g., x^2 = 1 -> [x=1,x=-1]
            return postconds
        else:
            return

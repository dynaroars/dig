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

    def gen(self, dinvs, traces):
        assert isinstance(dinvs, data.inv.invs.DInvs), dinvs
        assert isinstance(traces, data.traces.DTraces), traces
        dinvs_ = data.inv.invs.DInvs()

        post_locs = [loc for loc in dinvs if settings.POST_LOC in loc]
        for loc in post_locs:
            postconds = [self.get_postconds(inv.inv) for inv in dinvs[loc]
                         if isinstance(inv, data.inv.eqt.Eqt)]
            postconds = [pcs for pcs in postconds if pcs]
            postconds = set(p for postconds_ in postconds
                            for p in postconds_)
            preposts = self.get_preposts(loc, postconds, traces[loc])
            if preposts:
                dinvs_[loc] = data.inv.invs.Invs(preposts)

        return dinvs_

    @property
    def preconds(self):
        try:
            return self._preconds
        except AttributeError:
            symbols = self.symstates.inp_decls.sageExprs
            self._preconds = self.get_preconds(symbols, term_siz=2)
            return self._preconds

    def get_preposts(self, loc, postconds, traces):
        assert isinstance(loc, str), loc
        assert isinstance(postconds, set) and postconds, postconds
        assert all(p.operator() == operator.eq for p in postconds), postconds
        assert isinstance(traces, data.traces.Traces), traces

        postconds = sorted(postconds, key=lambda d: len(str(d)))
        postconds = [data.inv.eqt.Eqt(p) for p in postconds]

        # find all traces satifies each postcond
        mytraces = {p: data.traces.Traces([
            t for t in traces if p.test_single_trace(t)])
            for p in postconds}

        preposts = []  # results

        def myappend(preconds, is_conj):
            prepost = PrePost(data.inv.invs.Invs(preconds),
                              postcond, stat=data.inv.invs.Inv.PROVED)
            prepost.is_conj = is_conj
            preposts.append(prepost)

        postconds = sorted(
            postconds, key=lambda d: len(mytraces[d]), reverse=True)

        idxs = range(len(postconds))
        for idx in idxs:
            postcond = postconds[idx]
            others = [postconds[i] for i in idxs[:idx] + idxs[idx+1:]]
            traces_ = [t for t in mytraces[postcond]
                       if all(t not in mytraces[other] for other in others)]
            traces_ = data.traces.Traces(traces_)

            conj_preconds = [pc for pc in self.preconds if pc.test(traces_)]
            conj_preconds = self.get_conj_preconds(
                loc, conj_preconds, postcond)
            if conj_preconds:
                myappend(conj_preconds, is_conj=True)

            disj_preconds = self.get_disj_preconds(loc, postcond, traces)
            if disj_preconds:
                myappend(disj_preconds, is_conj=False)

        preposts = data.inv.invs.Invs(preposts)
        preposts = preposts.simplify(self.use_reals)
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
            # if isOK(pc, postcond):
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
        assert isinstance(postcond, data.inv.eqt.Eqt), postcond

        if not preconds:
            return []

        postcond_expr = postcond.expr(self.use_reals)

        preconds = sorted(preconds, key=lambda p: len(Miscs.getVars(p.inv)))
        preconds_exprs = [pc.expr(self.use_reals) for pc in preconds]
        if not self.check(preconds_exprs, postcond_expr, loc):
            return []

        def _imply(js, _):
            jexprs = [preconds_exprs[j] for j in js]
            return self.check(jexprs, postcond_expr, loc)

        results = Miscs.simplify_idxs(range(len(preconds)), _imply)
        results = [preconds[i] for i in results]
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
            "should only have 1 {} symbol: {}".format(
                symbols, settings.CTR_VAR)

        postconds = sage.all.solve(eqt, symbols[0])
        return postconds if len(postconds) >= 1 else None

    # PRIVATE METHODS

    @classmethod
    def get_preconds(cls, symbols, term_siz):
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

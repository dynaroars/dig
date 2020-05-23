# QUITE BROKEN, DO NOT USE

import operator
import pdb

import z3
import sage.all
import helpers.vcommon as CM
from helpers.miscs import Miscs

import settings
import infer.base
from data.traces import Traces, DTraces
from data.inv.base import Inv
from data.inv.invs import Invs, DInvs
from data.inv.eqt import Eqt
from data.inv.oct import Oct
from data.inv.prepost import PrePost

DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


class Infer(infer.base.Infer):
    def __init__(self, symstates, prog):
        super().__init__(symstates, prog)
        self.use_reals = self.symstates.use_reals

    def gen(self, dinvs, traces):
        assert isinstance(dinvs, DInvs), dinvs
        assert isinstance(traces, DTraces), traces

        dinvs_ = DInvs()
        post_locs = [loc for loc in dinvs if settings.POST_LOC in loc]
        for loc in post_locs:

            postconds = [self.get_postconds(inv.inv) for inv in dinvs[loc]
                         if isinstance(inv, Eqt)]
            postconds = [pcs for pcs in postconds if pcs]
            postconds = set(p for pcs in postconds for p in pcs)

            preposts = []
            for postcond in postconds:
                prepost = self.get_preposts1(loc, postcond)
                if prepost:
                    preposts.append(prepost)

            if preposts:
                dinvs_[loc] = Invs(preposts)
            # preposts = self.get_preposts(loc, postconds, traces[loc])
            # if preposts:
            #     dinvs_[loc] = Invs(preposts)

        return dinvs_

    @property
    def preconds(self):
        try:
            return self._preconds
        except AttributeError:
            symbols = self.prog.inp_decls.sageExprs
            self._preconds = self.get_preconds(symbols, term_siz=2)
            return self._preconds

    def get_preposts1(self, loc, postcond):
        assert isinstance(loc, str), loc
        assert postcond.operator() == operator.eq, postcond

        import infer.opt
        solver = infer.opt.Ieq(self.symstates, self.prog)
        postcond_expr = Eqt(postcond).expr(self.use_reals)
        preconds = solver.gen([loc], postcond_expr)
        preconds = list(preconds[loc]) if loc in preconds else []
        #conj_preconds = self.get_conj_preconds(loc, preconds, postcond)
        if preconds:
            precond_expr = z3.And([pc.expr(self.use_reals) for pc in preconds])
            inv = z3.Implies(precond_expr, postcond_expr)
            cexs, isSucc = self.symstates.mcheck_d(loc, inv, None, 1)
            if not cexs and isSucc:
                prepost = PrePost(Invs(preconds), postcond, stat=Inv.PROVED)
                prepost.is_conj = True
                return prepost
            else:
                return None
        return None

    def get_preposts(self, loc, postconds, traces):
        assert isinstance(loc, str), loc
        assert isinstance(postconds, set) and postconds, postconds
        assert all(p.operator() == operator.eq for p in postconds), postconds
        assert isinstance(traces, Traces), traces

        preconds = [pc for pc in self.preconds]
        # preconds = [pc for pc in self.preconds
        #             if self._check(pc.expr(self.use_reals), loc, check_consistency=True)]
        #print("preconds", preconds)
        postconds = sorted(postconds, key=lambda d: len(str(d)))
        postconds = [Eqt(p) for p in postconds]

        # find traces satifies each postcond
        ptraces = {p: Traces([t for t in traces if p.test_single_trace(t)])
                   for p in postconds}

        preposts = []  # results

        def myappend(mypreconds, is_conj):
            # TODO: check, stat=Inv.PROVED ?
            prepost = PrePost(Invs(mypreconds), postcond, stat=Inv.PROVED)
            prepost.is_conj = is_conj
            preposts.append(prepost)

        postconds = sorted(
            postconds, key=lambda d: len(ptraces[d]), reverse=True)
        idxs = list(range(len(postconds)))
        for idx in idxs:
            print('gh1')
            postcond = postconds[idx]
            try:
                postcond_expr = postcond.expr(self.use_reals)
            except NotImplementedError as ex:
                # cannot parse something like sqrt(x)
                continue

            #print("postcond", postcond)
            print('gh1a')
            others = [postconds[i] for i in idxs[:idx] + idxs[idx+1:]]
            traces_ = [t for t in ptraces[postcond]
                       if all(t not in ptraces[other] for other in others)]
            traces_ = Traces(traces_)

            conj_preconds = [pc for pc in preconds if pc.test(traces_)]
            #print(conj_preconds, conj_preconds)

            conj_preconds = self.get_conj_preconds(
                loc, conj_preconds, postcond_expr)
            #print('cpreconds', conj_preconds)
            if conj_preconds:
                myappend(conj_preconds, is_conj=True)
            print('gh1b')
            disj_preconds = self.get_disj_preconds(
                loc, preconds, postcond_expr, traces)
            print('gh1b@@@')
            #print('dpreconds', disj_preconds)
            if disj_preconds:
                myappend(disj_preconds, is_conj=False)
            print('gh1c')

        print('gh2')
        preposts = Invs(preposts)
        print('gh3')
        print(preposts)
        #preposts = preposts.simplify(self.use_reals)
        return preposts

    def check(self, pcs, postcond_expr, loc):
        precond_expr = z3.And(pcs) if isinstance(pcs, list) else pcs
        inv = z3.Implies(precond_expr, postcond_expr)
        return self._check(inv, loc, check_consistency=False)

    def _check(self, inv, loc, check_consistency):
        cexs, isSucc = self.symstates.mcheck_d(loc, inv, None, 1)

        if check_consistency:
            if cexs:  # satisfies
                return True
            return False
        else:
            if cexs or not isSucc:
                # mlog.debug("{}: discard {}".format(loc, inv))
                return False
            return True

    def get_disj_preconds(self, loc, preconds, postcond_expr, traces):
        assert all(isinstance(p, Inv) for p in preconds), preconds
        assert z3.is_expr(postcond_expr), postcond_expr

        preconds_ = []
        for pc in preconds:
            if self.check(pc.expr(self.use_reals), postcond_expr, loc):
                #print("hello: {} => {}".format(pc, postcond_expr))
                preconds_.append(pc)

        if len(preconds_) >= 2:
            is_conj = False
            preconds_ = Invs._simplify(preconds_, is_conj, self.use_reals)

        return preconds_

    def get_conj_preconds(self, loc, preconds, postcond_expr):
        """
        preconds  =>  post can be strengthened by removing some preconds
        e.g., a&b => post is stronger than a&b&c => post
        """
        assert all(isinstance(p, Inv) for p in preconds), preconds
        assert z3.is_expr(postcond_expr), postcond_expr

        if not preconds:
            return []

        preconds = sorted(preconds, key=lambda p: len(Miscs.get_vars(p.inv)))
        preconds_exprs = [pc.expr(self.use_reals) for pc in preconds]
        if not self.check(preconds_exprs, postcond_expr, loc):
            return []

        def _imply(js, _):
            jexprs = [preconds_exprs[j] for j in js]
            return self.check(jexprs, postcond_expr, loc)

        results = Miscs.simplify_idxs(list(range(len(preconds))), _imply)
        results = [preconds[i] for i in results]
        return results

    @classmethod
    def get_postconds(cls, eqt):
        assert Miscs.is_expr(eqt), eqt
        assert eqt.operator() == operator.eq, eqt

        # tCtr
        symbols = [s for s in Miscs.get_vars(eqt)
                   if settings.CTR_VAR in str(s)]

        if not symbols:
            return

        assert len(symbols) == 1, \
            "should only have 1 tCtr symbol: {}, {}".format(
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
        t1 = [Eqt(t == 0) for t in symbols]  # M=0, N=0
        ts = Miscs.get_terms_fixed_coefs(symbols, term_siz, settings.ICOEFS)
        t2 = [Oct(t < 0) for t in ts]  # +/M+/-N >0
        t3 = [Oct(t <= 0) for t in ts]  # +/M+/-N >=0
        return t1 + t2 + t3

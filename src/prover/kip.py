import pdb
import time
import z3

import settings

import helpers.vcommon as CM
from helpers.z3utils import Z3

from prover.miscs import Miscs

DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


class Prog:
    def __init__(self, init_conds, defs, input_vars, assumes):
        """
        This class models a program using
        1. initial condition
        2. transition (definitions of updated variables)
        3. assumptions

        Input variables:
        - init_cond: list of initial conditions
        e.g. [Block == Off,Reset == On,WaterPres == wp_init_val,
        Overridden == False,SafetyInjection == On,Pressure == TooLow]

        - defs: a dictionary consisting variables being updated by
        the transition

        - input_vars: variables that are INDEPDENT.
        SCR programs don't have these, because input (monitored) vars
        are dependent due to OIA

        - assumes: list of assumptions
        Two types of assumptions:
        (1) state assumes: those for each *state*
        e.g.
        And(0 <= WaterPres,WaterPres < 2000): WaterPres is in range 0,2000
        at any state

        (2) trans assumes: those for each *transition*
        e.g.
        One Input Assumption asserts only 1 var can changed at a time
        or
        And(pre(WaterPres) - 10 <= WaterPres,
        WaterPres <= pre(WaterPres) + 10)
        """

        assert (isinstance(init_conds, list) and
                all(Miscs.is_state(c) for c in init_conds)), init_conds

        assert (isinstance(defs, dict) and
                all(z3.is_expr(v) for v in defs.values())), defs

        assert (isinstance(input_vars, list) and
                all(Z3.is_var(v) for v in input_vars)), input_vars

        assert (isinstance(assumes, list) and
                all(z3.is_expr(a) for a in assumes)), assumes

        self.defs = defs
        self.init_conds = init_conds
        self.input_vars = input_vars

        self.assumes_state = []
        self.assumes_trans = []

        for a in assumes:
            if Miscs.is_trans(a):
                self.assumes_trans.append(a)
            else:
                self.assumes_state.append(a)

        # Known invariants (lemmas). Use add_inv() to add an inv as lemma
        self.invs_state = []
        self.invs_trans = []

    def __str__(self, show_details=False):
        s = []
        if show_details:
            s = [f"init_conds: {self.init_conds}",
                 f"asumes_state: {self.assumes_state}",
                 f"asumes_trans: {self.assumes_trans}",
                 f"invs_state: {self.invs_state}",
                 f"invs_trans: {self.invs_trans}",
                 f"defs: {self.defs}"]
        else:
            s = [f"|init_conds|: {len(self.init_conds)}",
                 f"|asumes_state|: {len(self.assumes_state)}",
                 f"|asumes_trans|: {len(self.assumes_trans)}",
                 f"|invs_state|: {len(self.invs_state)}",
                 f"|invs_trans|: {len(self.invs_trans)}",
                 f"|defs|: {len(self.defs)}"]
        s = '\n'.join(s)
        return s

    def add_inv(self, inv):
        """
        Add an inv as a known lemma, which can be useful to prove
        other properties. Note that invs and assumptions are treated
        slightly differently by KIP because invs are *proved*
        properties and thus can be exploited differently !
        """
        mlog.debug("Add as lemma the inv\n'{}'".format(inv))

        if Miscs.is_trans(inv):
            self.invs_trans.append(inv)
        else:
            self.invs_state.append(inv)

    def reset_invs(self):
        """
        Remove all known invs (lemmas)
        """
        mlog.debug("Remove all invs (lemmas) (state: {}, trans: {})"
                   .format(len(self.invs_state), len(self.invs_trans)))
        self.invs_state = []
        self.invs_trans = []

    def prove(self, prop, k,
              do_trans=False,
              do_base_case=True,
              do_induction=True,
              do_pcompress=True,
              do_term_check=True,
              do_abstraction=True):
        """
        Prove a property using KIP.
        """

        assert z3.is_expr(prop), prop
        assert k >= 0, k
        assert isinstance(do_base_case, bool), do_base_case
        assert isinstance(do_induction, bool), do_induction
        assert isinstance(do_pcompress, bool), do_pcompress
        assert isinstance(do_term_check, bool), do_term_check
        assert isinstance(do_abstraction, bool), do_abstraction

        mlog.debug(f'Original program:{self}')

        if do_abstraction:
            prog = self.gen_abstraction(prop)
            mlog.info(f'Abstract program:{prog}')
        else:
            prog = self

        kip = KIP(prop,
                  prog,
                  k=k,
                  do_base_case=do_base_case,
                  do_induction=do_induction,
                  do_pcompress=do_pcompress,
                  do_term_check=do_term_check)

        if do_trans:
            raise AssertionError("trans: not implemented")

        r, m, k_ = kip.k_ind()

        # time_elapsed = time.time() - stime
        # mlog.warn('Time elapsed: %.4f s'%time_elapsed)
        return r, m, k_

    def prove_props(self,
                    props,
                    k,
                    do_trans,
                    do_base_case,
                    do_induction,
                    do_pcompress,
                    do_term_check,
                    do_abstraction,
                    nreprove,
                    do_parallel):
        """
        Proves the given properties.
        Attempt to re-prove unproven ones using lemmas.

        do_soft_reprove: checks if the proved properties imply the unknown ones.
        This does not add proved properties as lemmas and re-invoke prover

        nreprove: times we attempt to fully reprove props

        do_parallel performs the task in parallel if
        multiprocessing is available

        """

        def f(tasks):
            rs = []
            for (idx, p) in tasks:
                mlog.info(f"{idx}. Checking '{p}'")
                r, m, k_ = self.prove(p,
                                      k=k,
                                      do_base_case=do_base_case,
                                      do_abstraction=do_abstraction,
                                      do_pcompress=do_pcompress,
                                      do_term_check=do_term_check)

                # cannot explicitly store p and m
                # b/c they contain pointers and cannot be pickled
                rs.append((idx, r, m if m is None else Z3.model_str(m), k_))
            return rs

        nreprove_ = 0
        unchecked_idxs = range(len(props))
        rs = [None]*len(unchecked_idxs)

        while True:
            new_invs = []
            unchecked_idxs_ = []
            tasks = list(zip(unchecked_idxs,
                             [props[idx] for idx in unchecked_idxs]))
            wrs = CM.run_mp(
                "checking {len(tasks)} ps", tasks, f, settings.DO_MP)

            for idx, r, m, k_ in wrs:
                p = props[idx]
                # 9/10: bug if not make a list copy since these things change!
                rs[idx] = (p, r, m, k_,
                           list(self.invs_state),
                           list(self.assumes_state + self.assumes_trans))

                if r is True:
                    new_invs.append(p)
                if r is None:
                    unchecked_idxs_.append(idx)

            if not (new_invs and unchecked_idxs_):
                break

            if nreprove_ >= nreprove:
                break

            nreprove_ = nreprove_ + 1

            mlog.info(f"Re-prove {len(unchecked_idxs_)} prop(s) "
                      "using {len(new_invs)} new invs "
                      "(attempt {nreprove}/{nreprove})")

            for inv in new_invs:
                self.add_inv(inv)

            unchecked_idxs = sorted(unchecked_idxs_)

        return rs

    def tprove(self, prop,
               expected,
               msg,
               do_trans=False,
               do_term_check=True,
               do_pcompress=True,
               do_induction=True,
               do_base_case=True,
               do_abstraction=True,
               do_assert=True,
               k=10):
        """
        Shortcut to prove properties.
        Raise errors if the result of the proof is not as expected.
        """

        assert z3.is_expr(prop), prop
        assert expected in set([True, False, None]), expected
        assert isinstance(msg, str), msg
        assert k >= 0, k
        assert all(isinstance(c, bool) for c in
                   [do_term_check, do_pcompress, do_induction,
                    do_base_case, do_assert, do_abstraction])

        mlog.info('*****')

        (r, m, k_) = self.prove(prop, k=k,
                                do_trans=do_trans,
                                do_abstraction=do_abstraction,
                                do_base_case=do_base_case,
                                do_induction=do_induction,
                                do_term_check=do_term_check,
                                do_pcompress=do_pcompress)

        mlog.info(msg)

        if r is True:
            mlog.info('proved')
        elif r is False:
            mlog.info('disproved')
            mlog.debug(Z3.model_str(m))
        else:
            mlog.info('unproved')

        if r != expected:
            mlog.warn(
                f"*** UNEXPECTED RESULT: output={r}, expected={expected} ***")

            if do_assert:
                raise AssertionError('unexpected result !!!')

        mlog.info('*****\n')

    def gen_abstraction(self, prop):
        """
        Generate a simpler program containing information
        just to prove 'prop'

        The main method is slicing variable definitions.
        If proving a prop P doesn't require the definition of
        variable v, then we remove v.

        IMPORTANT: We do not slice assumptions, init conditions etc.
        The reason is that if those assumptions or initial conditions
        contradict, then P is always proved. But if we slice these
        information, we might inadvertently slice those contradictions
        and disprove P.

        For example, False is proved under the contradicting assumption
        (x and not x).  But if we slice (x and not x), then 'False' is disproved.
        """

        assert z3.is_expr(prop), prop

        defs_ = self.slice_defs(prop)
        # prop, prog.defs, prog.assumes_state, prog.assumes_trans)

        prog_ = Prog(list(self.init_conds), defs_,
                     list(self.input_vars),
                     list(self.assumes_state + self.assumes_trans))

        for inv in self.invs_state + self.invs_trans:
            prog_.add_inv(inv)

        return prog_

    def slice_defs(self, prop):
        """
        Return a new (potentially empty) def dictionary from the old one
        consisting of only necessary variable definitions to prove property
        """

        fs = [prop] + self.assumes_state + self.assumes_trans
        fs = [f for f in fs if z3.is_expr(f)]

        vs = [Z3.get_vars(f) for f in fs]
        vs = [Miscs.cur(v) if Miscs.is_pre(v) else v
              for vs_ in vs for v in vs_]
        vs = set(vs)

        vs_ = [Prog.get_influence_vs(v, self.defs, set()) for v in vs]
        vs_ = [v for vs__ in vs_ for v in vs__]
        vs = set.union(vs, vs_)

        defs_ = {v: self.defs[v] for v in vs if v in self.defs}
        return defs_

    @staticmethod
    def get_influence_vs(v, defs, rs):
        """
        Return a list of variables that influences v
        (i.e. the definition of v depends on these variables)

        >>> from z3 import Bools, BoolVal
        >>> from scr_miscs import mk_OIA

        >>> s,t = Bools('s t')
        >>> x,y,z = Bools('x y z')
        >>> vs = [x,y,z]
        >>> o = mk_OIA(vs)
        >>> vv = [o,o,And(o,s)]
        >>> vs2 = [t]
        >>> vv2 = [BoolVal(True)]
        >>> vs_k = map(fhash,vs + vs2)
        >>> vs_v =vv + vv2
        >>> defs = OrderedDict(zip(vs_k,vs_v))
        >>> print Prog.get_influence_vs(x,defs,rs=[])
        [s, y, z]

        # >>> print Prog.get_influence_vs(x,defs,assumes=[x==s],rs=[])
        # [s, y, z]

        # >>> print Prog.get_influence_vs(x,defs,assumes=[y==t],rs=[])
        # [s, y, z, t]


        """
        assert Z3.is_var(v), v
        assert isinstance(defs, dict), defs
        assert isinstance(rs, set), rs

        if Miscs.is_pre(v):
            v = Miscs.cur(v)

        # return if already in the result set
        if v in rs:
            return rs

        try:
            vs = Z3.get_vars(defs[v])
            # print vs
        except KeyError:
            return rs

        rs.add(v)

        # convert v_pre to v
        vs = set(Miscs.cur(v_) if Miscs.is_pre(v_) else v_ for v_ in vs)

        for v_ in vs:
            rs_ = Prog.get_influence_vs(v_, defs, rs)  # rec call
            rs = set.union(rs, rs_)

        rs = set.union(rs, vs)

        # remove myself
        rs.remove(v)
        return sorted(rs, key=str)


# ##############################
# #
# # The KIP Theorem PRover
# #
# ##############################


class KIP:
    """
    The prover based on K-Induction to prove program properties.
    """
    atstate_cache = {}

    def __init__(self,
                 prop,
                 prog,
                 k=100,
                 do_base_case=True,
                 do_induction=True,
                 do_pcompress=True,
                 do_term_check=True):

        assert z3.is_expr(prop), prop
        assert isinstance(prog, Prog), prog
        assert k >= 0, k
        assert isinstance(do_base_case, bool), do_base_case
        assert isinstance(do_induction, bool), do_induction
        assert isinstance(do_pcompress, bool), do_pcompress
        assert isinstance(do_term_check, bool), do_term_check

        self.k = k

        self.prop = prop
        self.is_prop_state = Miscs.is_state(self.prop)

        self.init_conds = prog.init_conds
        self.assumes_state = prog.assumes_state
        self.assumes_trans = prog.assumes_trans
        self.invs_state = prog.invs_state
        self.invs_trans = prog.invs_trans
        self.input_vars = prog.input_vars
        self.defs_vals = list(prog.defs.values())

        f = Z3._and(self.defs_vals + self.assumes_state + self.assumes_trans)
        self.state_vars = self.get_state_vars(f, set(self.input_vars))

        mlog.debug("KIP (k={})".format(k))
        mlog.debug("prop: '{}'".format(self.prop))
        mlog.debug("|state_vars|: {}".format(len(self.state_vars)))
        mlog.debug(self.state_vars)

        if len(self.state_vars) == 0:
            mlog.warn("No state vars")
            if do_pcompress:
                mlog.warn("Disable path compression")
                do_pcompress = False
            if do_term_check:
                mlog.warn("Disable termination check")
                do_term_check = False

        self.do_base_case = do_base_case
        self.do_induction = do_induction
        self.do_pcompress = do_pcompress
        self.do_term_check = do_term_check

    def k_ind(self):
        """
        Starts with k=0 instead of 2

        Proving property using k-induction.
        Return a tuple (r, ce), where r represent the prover
        result and ce is the counterexample (model).

        r has 3 possible values True,False,None,unkonwn.
        True: property is proved.
        False: property is disproved.
        None: property cannot be proven (e.g. exceed the number of k
        iterations or that the theory is not supported by the SMT solver)
        unknown: error from the SMT solver.

        """
        if not self.is_prop_state:
            raise AssertionError('trans: not implemented')

        P = self.P
        I = self.I
        T = self.T
        A_S = self.A_S
        A_T = self.A_T
        I_S = self.I_S
        I_T = self.I_T
        D = self.D

        solver_timeout = 1*1000  # timeout
        S_base = z3.Solver()
        S_base.set(timeout=solver_timeout)
        S_step = z3.Solver()
        S_step.set(timeout=solver_timeout)

        def add_base(f):
            if f is not None:
                S_base.add(f)

        def add_step(f):
            if f is not None:
                S_step.add(f)

        _sbase = None
        _sstep = 'n'

        def _term_check(k):
            c = [D(k_, _sbase) for k_ in range(2, k+1)]  # 2..k
            c = Z3._and(c)

            # Term check
            mlog.debug('* Term Check ({})'.format(k))
            if c is None:
                mlog.warn('skipping term check')
                return None, None

            r_t, cex_t = KIP.entails(S_base, z3.Not(c))
            if r_t is True:
                mlog.info(f"** proved (cycle found) ({k}): {self.prop}")

            return r_t, cex_t

        def _base_case(k, f=None):
            assert f is None or z3.is_expr(f), f

            mlog.debug(f"* Base Case state ({k})")

            if f is None:
                f = P(k, _sbase)

            r_b, cex_b = KIP.entails(S_base, f)  # P(k,_sbase),

            if r_b is False:
                mlog.info(f"** disproved (Base case) ({k}): {self.prop}")

                # mlog.trace3(model_str(cex_b))

            return r_b, cex_b

        def _induction(k):
            # mlog.trace1('* Inductive Step state ({})'.format(k))

            if k >= 2 and self.do_pcompress:
                if k == 2:  # first time
                    add_step(I(0, _sbase))
                    add_step(A_S(0, _sbase))

                add_step(D(k, _sstep))

            r_s, cex_s = KIP.entails(S_step, P(k+1, _sstep))

            if r_s is True:
                mlog.info('** proved (Induction step) ({}): {}'
                          .format(k, self.prop))
            else:
                mlog.debug('IS {} cannot prove'.format(k))
                # print(model_str(cex_s))

            return r_s, cex_s

        # Begin k-induction

        for k in range(0, self.k + 1):

            # Base case
            if k == 0:
                add_base(I(k, _sbase))
                add_base(A_S(k, _sbase))
            else:
                add_base(T(k, _sbase))
                add_base(A_S(k, _sbase))
                add_base(A_T(k, _sbase))

            if k >= 2 and self.do_term_check:
                r_t_s, cex_t_s = _term_check(k)
                if r_t_s is True:
                    return True, cex_t_s, k
                if r_t_s == z3.unknown:
                    return z3.unknown, None, k

            if self.do_base_case:
                r_b, cex_b = _base_case(k, P(k, _sbase))
                if r_b is False:
                    return False, cex_b, k

                if r_b == z3.unknown:
                    return z3.unknown, None, k

            # Induction step
            add_step(P(k, _sstep))
            add_step(T(k+1, _sstep))

            add_step(A_S(k+1, _sstep))
            add_step(I_S(k+1, _sstep))

            add_step(A_T(k+1, _sstep))
            add_step(I_T(k+1, _sstep))

            if self.do_induction:
                r_s, cex_s = _induction(k)
                if r_s is True:
                    return True, cex_s, k

                if r_s == z3.unknown:
                    return z3.unknown, None, k

        # out of k-loop
        if self.do_induction:
            mlog.info('** Not able to prove with k={}: {}'
                      .format(self.k, self.prop))
            return None, None, k
        else:
            mlog.debug('** No induction performed, all base cases passed')
            return True, None, k

    # Methods to obtain formulas at different state i

    def P(self, i, s):
        """
        Return the formula for prop at state i
        """
        assert z3.is_expr(self.prop), self.prop
        if self.is_prop_state:
            assert i >= 0, i
        else:
            assert i >= 1, i

        return self._at_state(self.prop, i, s)

    def I(self, i, s):
        """
        Return the formula for init condition at state i
        """
        assert (isinstance(self.init_conds, list) and
                all(Miscs.is_state(a) for a in self.init_conds)), self.init_conds
        assert i >= 0, i

        init_cond = Z3._and([self._at_state(a, i, s) for a in self.init_conds])
        return init_cond

    def T(self, i, s):
        """
        Return the formula for trans at state i.
        I.e. the transaction from state i-1 to state i

        T(i=0) is by default initial state (condition)
        T(i=1) is the trans from state 0 to state 1, and so on

        """
        assert (isinstance(self.defs_vals, list) and
                all(z3.is_expr(a) for a in self.defs_vals)), self.defs_vals
        assert i >= 1, i

        trans = Z3._and([self._at_state(a, i, s) for a in self.defs_vals])
        return trans

    def I_S(self, i, s):
        """
        Return the formula for (state) invariant at state i.
        """
        assert (isinstance(self.invs_state, list) and
                all(Miscs.is_state(a) for a in self.invs_state)), \
            self.invs_state
        assert i >= 0, i

        inv_state = Z3._and([self._at_state(a, i, s) for a in self.invs_state])
        return inv_state

    def I_T(self, i, s):
        """
        Return the formula for (trans) invariant at state i
        """
        assert (isinstance(self.invs_trans, list) and
                all(Miscs.is_trans(a) for a in self.invs_trans)), \
            self.invs_trans
        assert i >= 1, i

        inv_trans = Z3._and([self._at_state(a, i, s) for a in self.invs_trans])
        return inv_trans

    def A_S(self, i, s):
        """
        Return the formula for (state) assume at state i
        """
        assert (isinstance(self.assumes_state, list) and
                all(Miscs.is_state(a) for a in self.assumes_state)), \
            self.assumes_state

        assert i >= 0, i

        assume_state = Z3._and([self._at_state(a, i, s)
                                for a in self.assumes_state])
        return assume_state

    def A_T(self, i, s):
        """
        Return the formula for (trans) assume at state i
        """

        assert (isinstance(self.assumes_trans, list) and
                all(Miscs.is_trans(a) for a in self.assumes_trans)), \
            self.assumes_trans

        assert i >= 1, i

        assume_trans = Z3._and([self._at_state(a, i, s)
                                for a in self.assumes_trans])

        return assume_trans

    def D(self, i, s):
        """
        Return a formula expressing state s_i is different
        than states [0, s_0, s_1, ..., s_(i-1)].

        If s is None then the returned formula expresses
        state i different than states [0 ... i-1]
        """
        assert i >= 2, f"i ({i}) must start from 2!"

        if not self.state_vars:
            return None

        def S(i, s):
            """
            Return a set (list) consisting of the variables at state i.
            I.e. x_1i, x_2i, ...
            """
            return [self._at_state(v, i, s) for v in self.state_vars]

        cur_state = S(i, s)
        # states s_0 ... s_(j-1)
        pre_states = [S(i_, s) for i_ in range(i)]

        if s:
            # D(s,s+i) = s_i #  [0,s_0,s_1,..,s_(i-1)]
            pre_states = [S(0, None)] + pre_states

        fs = [z3.Not(self.state_eq(cur_state, pre_state))
              for pre_state in pre_states]

        return Z3._and(fs)


#     ### Helper methods

    @classmethod
    def _at_state(cls, f, i, s):
        """
        Returns formula at state i
        """
        assert f is None or z3.is_expr(f), f

        if f is None:
            return None
        else:
            k = (f, i, s)
            try:
                return cls.atstate_cache[k]
            except KeyError:
                cls.atstate_cache[k] = Miscs.substitute_f(f=f, i=i, s=s)
                return cls.atstate_cache[k]

    @staticmethod
    def state_eq(vs1, vs2):
        """
        Generate a formula expressing the variables in vs1,vs2 are the same
        """
        assert isinstance(vs1, list) and all(Z3.is_var(v) for v in vs1), vs1
        assert isinstance(vs2, list) and all(Z3.is_var(v) for v in vs2), vs2
        assert len(vs1) == len(vs2)

        eqts = [v1 == v2 for v1, v2 in zip(vs1, vs2)]
        return Z3._and(eqts)

    @staticmethod
    def get_state_vars(f, exclude_vars):
        """
        f: a formula, e.g. the transition formula
        exclude_vars: variables that are not considered as state vars,
        e.g. independent variables

        From Verifying Safety Property of Lustre Programs:
        Temporal Induction

        Let L be a Lustre program, S be the tuple of L's state
        variables, non-input variables that occur within a pre.

        Then only non-input variables that occur within a pre are considered
        program states

        node test( X: bool ) returns ( P : bool );
        var A, B, C : bool;
        let
        A = X -> pre A;
        B = not (not X -> pre(C));
        C = not B;
        P = A = B;  #property to be proved, not important, not part of input

        >>> from z3 import Bools, Implies, Ints, If, Or


        # states variables = [A,C]
        >>> A,A_pre,B,B_pre,C,C_pre,X = Bools('A A_pre B B_pre C C_pre X')
        >>> af = A == A_pre
        >>> bf = B == Not(Not(Implies(X,C_pre)))
        >>> cf = C == Not(B)
        >>> trans = And(af,bf,cf)
        >>> exclude_vars = [X]
        >>> KIP.get_state_vars(trans, exclude_vars)
        [A, C]

        >>> af = A == Implies(X,A_pre)
        >>> bf = B == Not(Implies(Not(X),C_pre))
        >>> cf = C == Not(B)
        >>> trans = And(af,bf,cf)
        >>> exclude_vars = [X]
        >>> KIP.get_state_vars(trans, exclude_vars)
        [A, C]

        # state variables = c , R is not included because R_pre is not used
        >>> R,c_pre,c = Ints('R c_pre c')
        >>> trans = If(Or(R == 100, c_pre == 2), c == 0, c == c_pre + 1)
        >>> KIP.get_state_vars(trans, exclude_vars=[])
        [c]

        # this algorithm would return [], instead of [C]
        # this is by design because it doesn't make sense to have
        # C_pre without C in trans
        >>> KIP.get_state_vars(A == C_pre,[])
        []
        """

        assert f is None or z3.is_expr(f), f
        assert isinstance(exclude_vars, set), exclude_vars

        if f is None:
            return []

        # start with state_vars being all vars in trans
        state_vars = Z3.get_vars(f)

        # keep those that not being excluded
        state_vars = set(v for v in state_vars if v not in exclude_vars)

        # keep those v that are not pre but v's pre is part of the f
        state_vars = [v for v in state_vars
                      if not Miscs.is_pre(v) and Miscs.pre(v) in state_vars]

        assert all(not Miscs.is_pre(v) for v in state_vars)

        return state_vars

    @staticmethod
    def entails(S, claim):
        """
        Checking the validity of S => claim
        """
        assert isinstance(S, z3.Solver), S
        assert z3.is_expr(claim), claim

        mlog.debug(f"premise:\n{S}\n")
        mlog.debug(f"claim:\n{claim}\n")
        # print 'entail'
        # print S
        # print claim
        S.push()
        S.add(z3.Not(claim))

        check_rs = S.check()
        if check_rs == z3.sat:
            r = False, S.model()
        elif check_rs == z3.unsat:
            r = True, None  # unsat, no model
        elif check_rs == z3.unknown:
            mlog.warn(f"unknown for {s}")
            r = z3.unknown, None  # unknown, error
        else:
            raise AssertionError(f"result: {check_rs} for\n{S}")

        S.pop()
        return r

# ##############################
# #
# # A small example
# #
# ##############################


def example():
    """
    A simple example to demonstrate how KIP works.
    The program has a single variable x, initialized with x = 2.
    Then it enters an infinite loop that updates the value of x as
    x = (2*x) - 1.
    We want to prove the property x > 0 from this program using KIP.
    """
    from z3 import Real

    # Given this program
    x = Real('x')
    I = x == 2
    T = x == 2 * Miscs.pre(x) - 1

    # We want to prove this property
    P = x > 0

    # First, we create a representation of the program

    prog = Prog(init_conds=[I],  # Initial condition
                defs={x: T},  # Definitions of variables being updated
                input_vars=[],  # Input variables
                assumes=[])
    print(prog.__str__(True))

    # Now, we can call KIP to prove P
    max_k = 5  # this is the max k iteration

    mlog.info(f"We can't prove {P} here yet")
    r, m, k = prog.prove(P, k=max_k)
    mlog.debug(f"proved: {r}, k: {k}")
    mlog.debug(f"cex: {m}")
    assert not r and not m, (r, m)

    P_stronger = x > 1
    mlog.info("But we can prove a stronger property '{}'".
              format(P_stronger))
    r, m, k = prog.prove(P_stronger, k=max_k)
    mlog.debug(f"proved: {r}, k: {k}")
    mlog.debug(f"cex: {m}")
    assert r and not m, (r, m)

    mlog.info("Adding the stronger prop '{}' as known inv "
              "allows us to prove the orig prop '{}'"
              .format(P_stronger, P))
    prog.add_inv(P_stronger)
    r, m, k = prog.prove(P, k=max_k)
    mlog.debug(f"proved: {r}, k: {k}")
    mlog.debug(f"cex: {m}")
    assert r and not m, (r, m)

    mlog.info(f"After removing the stronger prop '{P_stronger}',"
              "we can't prove the orig 'P' anymore")

    prog.reset_invs()
    r, m, k = prog.prove(P, k=max_k)
    mlog.debug(f"proved: {r}, k: {k}")
    mlog.debug(f"cex: {m}")
    assert not r and not m, (r, m)


# #run this with using the command $python kip.py
if __name__ == "__main__":

    # perform doctest
    # import doctest
    # doctest.testmod()

    # run the example
    # mlog.setLevel(logging.DEBUG)
    example()

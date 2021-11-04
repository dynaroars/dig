import pdb
import time
import z3
import settings

import helpers.vcommon as CM
from helpers.z3utils import Z3


DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.LOGGER_LEVEL)


class Miscs:
    pre_kw = '_pre'
    pre_d = {}  # v -> pre_v
    cur_d = {}  # pre_v -> v

    @classmethod
    def is_trans(cls, f):
        return cls.pre_kw in str(f)

    @classmethod
    def is_state(cls, f):
        """
        Check if f has no pre variables
        """
        return not cls.is_trans(f)

    @classmethod
    def pre(cls, v):
        """
        Return a new variable of the same sort as v called v_pre

        >>> from z3 import *
        >>> x = Bool('x')
        >>> pre(x)
        x_pre

        """
        try:
            return cls.pre_d[v]
        except KeyError:
            name = str(v) + cls.pre_kw
            pre_v = cls.mk_var(name, v.sort())
            cls.pre_d[v] = pre_v
            cls.cur_d[pre_v] = v
            return pre_v

    @classmethod
    def is_pre(cls, v):
        """
        Return if the variable v is a pre variable,
        i.e. if v ends with pre_kw
        """
        return str(v).endswith(cls.pre_kw)

    @classmethod
    def is_cur_f(cls, f):
        """
        Check if all variables in f are cur (not pre)

        Examples:

        >>> from z3 import *
        >>> x,y = Ints('x y')
        >>> is_cur_f(x)
        True
        >>> is_cur_f(pre(x))
        False
        >>> is_cur_f(Or(x==10, y==3))
        True
        >>> is_cur_f(Or(pre(x)==10, y==3))
        False
        >>> is_cur_f(Or(pre(x)==10, pre(y)==3))
        False
        """
        assert z3.is_expr(f), f

        return all(not cls.is_pre(v) for v in Z3.get_vars(f))

    @classmethod
    def pre_f(cls, f):
        """
        Convert a formula f with cur vars to a formula with pre vars

        >>> from z3 import *
        >>> x,y,z = Ints('x y z')

        >>> pre_f(z == 9)
        z_pre == 9

        >>> pre_f(And(y == 4, z == 9) )
        And(y_pre == 4, z_pre == 9)

        """
        assert f is None or cls.is_cur_f(f), f

        if f is None:
            return None
        elif Z3.is_var(f):
            return cls.pre(f)
        else:
            vss = [(v, cls.pre(v)) for v in Z3.get_vars(f)]
            return z3.substitute(f, *vss)

    @classmethod
    def mk_var(cls, name, vsort):
        """
        Create a variable of type vsort.

        Examples:

        >>> from z3 import *
        >>> v = mk_var('real_v', Real('x').sort())
        >>> print v
        real_v
        """

        assert isinstance(name, str) and name, name

        if vsort.kind() == z3.Z3_INT_SORT:
            v = z3.Int(name)
        elif vsort.kind() == z3.Z3_REAL_SORT:
            v = z3.Real(name)
        elif vsort.kind() == z3.Z3_BOOL_SORT:
            v = z3.Bool(name)
        elif vsort.kind() == z3.Z3_DATATYPE_SORT:
            v = z3.Const(name, vsort)

        else:
            raise AssertionError(
                f'Cannot handle this sort (s: {vsort}, {vsort.kind()})')

        return v

    @classmethod
    def cur(cls, pre_v):
        """
        Given a pre variable v, return the non-pre version of.
        For example, if v  =  myvar_pre, then cur(v) gives myvar
        """
        assert Z3.is_var(pre_v) and cls.is_pre(pre_v), pre_v

        return cls.cur_d[pre_v]

    @classmethod
    def substitute_f(cls, f, i, s=None):
        """
        Replaces all variables v in f with v_(i*_)

        s = a symbol string, e.g. n (so we will have the variable
        x_n_1 instead of x_1

        Examples:

        >>> from z3 import *
        >>> x,x_pre,y,y_pre = Ints('x x_pre y y_pre')

        >>> substitute_f(Implies(x==10,y==5),i=0)
        Or(Not(x_0 == 10), y_0 == 5)

        >>> substitute_f(Implies(x==10,y==5),i=1)
        Or(Not(x_1 == 10), y_1 == 5)

        >>> substitute_f(Implies(x==10,pre(y)==5),i=1)
        Or(Not(x_1 == 10), y_0 == 5)

        >>> substitute_f(Implies(x==10,pre(y)==5),1,s='m')
        Or(Not(x_m_1 == 10), y_m_0 == 5)

        >>> substitute_f(Implies(x==10,pre(y)==5),10,s='m')
        Or(Not(x_m_10 == 10), y_m_9 == 5)

        >>> substitute_f(BoolVal(False),i=10)
        False

        >>> substitute_f(IntVal(100),i=10)
        100

        """

        assert z3.is_expr(f)
        assert i >= 0, i
        assert i != 0 or cls.is_state(f), (i, f)  # v_pre => i!=0
        assert not s or isinstance(s, str) and len(s) >= 1, s

        vs = Z3.get_vars(f)

        if not vs:  # e.g. True, 5, etc  has no variables so return as is
            return f
        else:
            vss = cls.gen_vars(vs, i, s)
            f_ = f
            for vs in vss:
                f_ = z3.substitute(f_, vs)
            return f_

    @classmethod
    def gen_vars(cls, vs, i, s):
        """
        Generates variables at state s_i. See examples for details.

        v ->  v_i
        v_pre -> v_(i-1)

        Examples:

        >>> from z3 import *
        >>> x,y = Ints('x y')

        >>> gen_vars([x,y],10,s=None)
        [(y, y_10), (x, x_10)]

        >>> gen_vars([x,pre(y)],10,s=None)
        [(y_pre, y_9), (x, x_10)]

        >>> gen_vars([x,pre(y)],1,s=None)
        [(y_pre, y_0), (x, x_1)]

        >>> gen_vars([x,pre(y)],0,s=None)
        Traceback (most recent call last):
        ...
        AssertionError: cannot generate pre(var) with i=0

        >>> gen_vars([x,pre(y)],9,s='i')
        [(y_pre, y_i_8), (x, x_i_9)]

        >>> gen_vars([x,pre(y)],1,s='n')
        [(y_pre, y_n_0), (x, x_n_1)]

        """
        assert len(vs) > 0, vs
        assert i >= 0, i
        assert (not i == 0) or all(not cls.is_pre(v) for v in vs), \
            'cannot generate pre(var) with i=0'

        def mk_name(i, v):
            s_ = '_'
            if s is not None:
                s_ = s_ + s + '_'

            if str(v).endswith(cls.pre_kw):
                d = i - 1
                name = str(v)[:-len(cls.pre_kw)] + s_ + str(d)
            else:
                name = str(v) + s_ + str(i)
            return name

        # so that the longest one is replaced first
        old_vars = sorted(vs, key=str, reverse=True)

        new_names = [mk_name(i, v) for v in old_vars]
        new_vars = [cls.mk_var(ns, v.sort())
                    for ns, v in zip(new_names, old_vars)]

        vss = zip(old_vars, new_vars)

        return vss

    """
    short cuts to verify invs
    """
    @classmethod
    def verify(cls, loc, assumes, I, T, ps,
               show_disproved=False,
               show_model=False,
               show_redundant=True,
               nreprove=1,
               do_parallel=True):

        import prover.kip
        prog = prover.kip.Prog(init_conds=[I],
                               defs={None: T},
                               input_vars=[],
                               assumes=assumes)

        max_formula_siz = 15000
        lI = len(str(I))
        lT = len(str(T))
        mlog.debug("|I|={lI}, |T|={lT}")
        if lI >= max_formula_siz or lT >= max_formula_siz:
            mlog.warning("skipping reprove !!!")
            reprove = 0

        mlog.debug(
            f"Verify {len(ps)} invs at loc {loc} (parallel {do_parallel})")

        start_time = time.time()
        rs = prog.prove_props(ps, k=5,
                              do_trans=False,
                              do_base_case=True,
                              do_induction=True,
                              do_pcompress=False,
                              do_term_check=False,
                              do_abstraction=False,
                              nreprove=nreprove,
                              do_parallel=do_parallel)

        highest_k = -1
        Ts_total, Fs, Us, Es = [], [], [], []
        mTs_total, mFs, mUs, mEs = [], [], [], []
        k_ge_1 = 0
        lemmas_ge_1 = 0
        assumes_ge_1 = 0

        for (p, r, m, k, lemmas, assumes) in rs:
            if (r is True or r is False) and highest_k < k:
                highest_k = k

            if r is None:
                details = ''
            elif r == z3.unknown:
                details = ', smt solver error'
            else:
                k_ = 'k {}'.format(k)
                l_ = 'lemmas {}'.format(lemmas) if lemmas else None
                a_ = 'assumes {}'.format(assumes) if assumes else None

                details = ' ({})'.format(
                    ', '.join([d for d in [k_, l_, a_] if d]))

            s = ("{}: {}{}".format(p, r, details))

            if r is True or r is False:
                if k >= 1:
                    k_ge_1 = k_ge_1 + 1
                if lemmas and len(lemmas) >= 1:
                    lemmas_ge_1 = lemmas_ge_1 + 1
                if assumes and len(assumes) >= 1:
                    assumes_ge_1 = assumes_ge_1 + 1

            if r is True:
                Ts_total.append(p)
                mTs_total.append(s)

            elif r is False:
                Fs.append(p)
                mFs.append(s+('\n'+m if show_model else ''))
            elif r == z3.unknown:
                Es.append(p)
                mEs.append(s)
            else:
                Us.append(p)
                mUs.append(s)

        # so that the redundancy checking will attempt to remove longer
        # properties first
        Ts_total, mTs_total = zip(
            *sorted(zip(Ts_total, mTs_total),
                    key=lambda x: len(str(x[0])), reverse=True))
        Ts_total = list(Ts_total)
        mTs_total = list(mTs_total)

        mlog.debug(f"Check redundancy over {len(Ts_total)} proved props")
        Ts_idxs = cls.rinfer(Ts_total, ret_idxs=True)
        Ts = []
        mTs = []
        Ts_dep = []
        mTs_dep = []
        for i, (p, m) in enumerate(zip(Ts_total, mTs_total)):
            if i in Ts_idxs:  # indep, good ones
                Ts.append(p)
                mTs.append(m)
            else:
                Ts_dep.append(p)
                mTs_dep.append(m + " *redundant*")

        if Ts_dep:
            mlog.debug(f"Identify {len(Ts_dep)} *redundant* ps")

        if Us and Ts:
            mlog.debug(
                f"Soft reprove {len(Us)} unproved ps using {len(Ts)} proved ps")
            Us_ = []
            mUs_ = []
            proved_ps = Z3._and(Ts)
            for idx, (p, m) in enumerate(zip(Us, mUs)):
                if Z3.is_proved(z3.Not(z3.Implies(proved_ps, p))):
                    Ts_dep.append(p)
                    mTs_dep.append(
                        f"{p}: implied by proved ones **redundant**")
                else:
                    Us_.append(p)
                    mUs_.append(m)
            if Us_:
                mlog.debug(f"Prove {len(Us_)} **redundant** props")
                Us = Us_
                mUs = mUs_

        etime = time.time() - start_time

        ms = (mTs + (mTs_dep if show_redundant else []) +
              mUs + (mFs if show_disproved else []) +
              mEs)

        ms = '\n'.join(f"{i}. {m}" for i, m in enumerate(ms))

        time_str = '{0:.1f}'.format(etime)
        msg = (f"Loc '{loc}', k {highest_k}, "
               f"total {len(rs)} (p {len(Ts)} (k>0 {k_ge_1}, "
               f"lem>0 {lemmas_ge_1}, assumes>0, {assumes_ge_1} redun {len(Ts_dep)}), "
               f"d {len(Fs)}, u {len(Us)}, e {len(Es)}) {time_str}\n{ms}")

        mlog.debug(msg)

        d = {'loc': loc,
             'Ts': Ts, 'Fs': Fs, 'Us': Us, 'Es': Es,
             'Ts_dep': Ts_dep,
             'len_rs': len(rs),
             'highest_k': highest_k,
             'k_ge_1': k_ge_1,
             'lemmas_ge_1': lemmas_ge_1,
             'assumes_ge_1': assumes_ge_1,
             'etime': etime,
             'msg': msg}
        return d

    @classmethod
    def print_summary(cls, ds):

        highest_k = max(d['highest_k'] for d in ds)
        nTotal = sum(d['len_rs'] for d in ds)
        nTime = sum(d['etime'] for d in ds)
        nTs = sum(len(d['Ts']) for d in ds)
        nTs_dep = sum(len(d['Ts_dep']) for d in ds)
        nk_ge_1 = sum((d['k_ge_1']) for d in ds)
        nlemmas_ge_1 = sum((d['lemmas_ge_1']) for d in ds)
        nassumes_ge_1 = sum((d['assumes_ge_1']) for d in ds)

        nFs = sum(len(d['Fs']) for d in ds)
        nUs = sum(len(d['Us']) for d in ds)
        nEs = sum(len(d['Es']) for d in ds)
        msgs = [d['msg'] for d in ds]
        locs = [d['loc'] for d in ds]

        print('*** Summary ***')
        print('\n\n'.join('{}. {}'.format(i, m) for i, m in enumerate(msgs)))

        time_str = '{0:.1f}'.format(nTime)

        print("* nlocs {} '{}', invs {} (p {} (k>0 {}, lem>0 {}, assumes>0 {} redun {}), d {}, u {} e {}), k {}, time {}"
              .format(len(locs), ', '.join(locs),
                      nTotal, nTs, nk_ge_1, nlemmas_ge_1, nassumes_ge_1,
                      nTs_dep, nFs, nUs, nEs,
                      highest_k, time_str))

    @classmethod
    def rinfer(cls, ps, ret_idxs=False):
        """
        Remove the indices of the weak/redundant properties
        >>> from z3 import Real, Reals
        >>> x, a, y, b, q, k, s, t, z = Reals('x a y b q k s t z')

        >>> rinfer([a*y-b==0,q*y+k-x==0,a*x-a*k-b*q==0])
        [q*y + k - x == 0, a*y - b == 0]

        >>> rinfer([a*y-b==0,a*z-a*x+b*q==0,q*y+z-x==0])
        [q*y + z - x == 0, a*y - b == 0]

        >>> rinfer([x-7>=0, x + y -2>=0, y+5 >= 0])
        [x - 7 >= 0, y + 5 >= 0]

        >>> rinfer([x+y==0,x-y==1])
        [x + y == 0, x - y == 1]

        >>> rinfer([x*x-1>=0,x-1>=0])
        [x - 1 >= 0]


        # >>> rinfer([a*a - s + t == 0, t*t - 4*s + 2*t + 1 == 0,a*s - Real('1/2')*s*t + Real('1/2')*s == 0,  a*x - Real('1/2')*x*t + Real('1/2')*x == 0,a - Real('1/2')*t + 1/2 == 0, a*t - 2*s + Real('3/2')*t + Real('1/2') == 0])
        # [t*t - 4*s + 2*t + 1 == 0, a - 1/2*t + 1/2 == 0]

        >>> rinfer([x*x-y*y==0,x-y==0,x*x-y*y==0,2*x*y-2*y*y==0])
        [x - y == 0]

        >>> rinfer([x-1>=0 , t*y - 6 >= 0, t - 1 >= 0, y - 6 >= 0, t*y - y >= 0, t*x - x >= 0, y*x - 6*x>=0 , y*y - 36 >= 0, t*t - 3*t + 2 >= 0, t*t - 5*t + 6 >= 0 , t*y - 6*t - y + 6 >= 0])
        [x - 1 >= 0, t - 1 >= 0, y - 6 >= 0, t*t - 3*t + 2 >= 0, t*t - 5*t + 6 >= 0]


        >>> rinfer([x*y==6, y-2==0, x-3==0])
        [y - 2 == 0, x - 3 == 0]

        >>> rinfer([x*x==4,x==2])
        [x == 2]
        >>> rinfer([x==2,x*x==4])
        [x == 2]
        >>> rinfer([x==2,x*x==4,x==-2])
        [x == 2, x == -2]
        >>> rinfer([x==2,x==-2,x*x==4])
        [x == 2, x == -2]
        >>> rinfer([x*x==4,x==2,x==-2])
        [x == 2, x == -2]
        """
        # DO NOT USE THE BELOW 2 COMMENT LINES
        # as they screw up the original indices
        # ps = vset(ps,idfun=str)

        # ps = sorted(ps,reverse=True,key=lambda p: len(get_vars(p)))
        rs_idxs = list(range(len(ps)))
        for i in range(len(ps)):
            assert i in rs_idxs

            idx = rs_idxs.index(i)
            xclude_idxs = rs_idxs[:idx] + rs_idxs[idx+1:]
            if xclude_idxs:
                xclude_ps = Z3._and([ps[i_] for i_ in xclude_idxs])
                if Z3.is_proved(z3.Not(z3.Implies(xclude_ps, ps[i]))):
                    rs_idxs = xclude_idxs

        if ret_idxs:
            return rs_idxs
        else:
            return [ps[i] for i in rs_idxs]

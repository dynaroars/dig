import time
from vu_common import pause, is_empty, vset
from z3util import model_str, get_vars
from z3 import And, Implies, unknown, Solver, unsat, Not
import logging
import kip
Prog = kip.Prog

kip.logger.setLevel(logging.INFO)

def verify(loc,assumes,I,T,ps,
           show_disproved=False,
           show_model=False,
           show_redundant=True,
           nreprove=1,
           do_parallel=True):

    prog = Prog(init_conds=[I],
                defs = {None:T},
                input_vars=[],
                assumes=assumes)

    max_formula_siz = 15000
    lI = len(str(I))
    lT = len(str(T))
    print  '|I|={},|T|={}'.format(lI,lT)
    if lI >= max_formula_siz or lT >= max_formula_siz:
        print 'W: skipping reprove !!!'
        reprove = 0

    print('Verify {} invs at loc {} (parallel {})'
          .format(len(ps),loc,do_parallel))

    
    start_time = time.time()
    rs = prog.prove_props(ps,k=5,
                          do_trans=False,
                          do_base_case=True,
                          do_induction=True,
                          do_pcompress=False,
                          do_term_check=False,
                          do_abstraction=False,
                          nreprove=nreprove,
                          do_parallel=do_parallel)
    

    highest_k = -1
    Ts_total,Fs,Us,Es = [],[],[],[]
    mTs_total,mFs,mUs,mEs = [],[],[],[]
    k_ge_1 = 0
    lemmas_ge_1 = 0
    assumes_ge_1 = 0

    for (p,r,m,k,lemmas,assumes) in rs:
        if (r == True or r==False) and highest_k < k:
            highest_k = k
        
        if r is None:
            details = ''
        elif r == unknown:
            details = ', smt solver error'
        else:
            k_ = 'k {}'.format(k)
            l_ = 'lemmas {}'.format(lemmas) if lemmas else None
            a_ = 'assumes {}'.format(assumes) if assumes else None

            details = ' ({})'.format(
                ', '.join([d for d in [k_,l_,a_] if d]))
                           
        s = ("{}: {}{}".format(p,r,details))

        if r == True or r == False:
            if k >= 1: k_ge_1 = k_ge_1 + 1
            if lemmas and len(lemmas) >= 1: lemmas_ge_1 = lemmas_ge_1 + 1
            if assumes and len(assumes) >= 1: assumes_ge_1 = assumes_ge_1 + 1

        if r == True:
            Ts_total.append(p)
            mTs_total.append(s)

        elif r == False:
            Fs.append(p)
            mFs.append(s+('\n'+m if show_model else ''))
        elif r == unknown:
            Es.append(p)
            mEs.append(s)
        else:
            Us.append(p)
            mUs.append(s)


    #so that the redundancy checking will attempt to remove longer
    #properties first
    Ts_total,mTs_total = zip(*sorted(zip(Ts_total,mTs_total),
                                     key=lambda (t,_): len(str(t)),reverse=True))
    Ts_total = list(Ts_total)
    mTs_total = list(mTs_total)

    print 'Check redundancy over {} proved props'.format(len(Ts_total))
    Ts_idxs = rinfer(Ts_total,ret_idxs=True)
    Ts = []
    mTs = []
    Ts_dep = []
    mTs_dep = []
    for i,(p,m) in enumerate(zip(Ts_total,mTs_total)):
        if i in Ts_idxs: #indep, good ones
            Ts.append(p)
            mTs.append(m)
        else:
            Ts_dep.append(p)
            mTs_dep.append(m+' *redundant*')

    if Ts_dep:
        print 'Identify {} *redundant* ps'.format(len(Ts_dep))
        
    if Us and Ts:
        print('Soft reprove {} unproved ps using {} proved ps'
              .format(len(Us),len(Ts)))
        Us_ = []
        mUs_ = []
        proved_ps = And(*Ts)
        for idx,(p,m) in enumerate(zip(Us,mUs)):
            is_proved = myprove(Not(Implies(proved_ps,p)))
            if is_proved:
                Ts_dep.append(p)
                mTs_dep.append('{}: implied by proved ones **redundant**'
                               .format(p))
            else:
                Us_.append(p)
                mUs_.append(m)
        if Us_:
            print 'Prove {} **redundant** props'.format(len(Us_))
            Us = Us_
            mUs = mUs_
            

    etime = time.time() - start_time    
            

    ms = (mTs + (mTs_dep if show_redundant else []) + 
          mUs + (mFs if show_disproved else []) + 
          mEs)
    
    ms = '\n'.join('{}. {}'.format(i,m) for i,m in enumerate(ms))

    time_str =  '{0:.1f}'.format(etime)
    msg= ("Loc '{}', k {}, "\
          "total {} (p {} (k>0 {}, lem>0 {}, assumes>0, {} redun {}), "\
          "d {}, u {}, e {}) {}\n{}"
          .format(loc,highest_k,len(rs),
                  len(Ts),k_ge_1,lemmas_ge_1,assumes_ge_1,len(Ts_dep),len(Fs),len(Us),len(Es),
                  time_str,ms))
                  
    print msg

    d = {'loc': loc,
         'Ts':Ts,'Fs':Fs, 'Us':Us, 'Es':Es,
         'Ts_dep': Ts_dep,
         'len_rs': len(rs),
         'highest_k':highest_k,
         'k_ge_1': k_ge_1,
         'lemmas_ge_1': lemmas_ge_1,
         'assumes_ge_1': assumes_ge_1,
         'etime': etime,
         'msg': msg}
    return d



def print_summary(ds):

    highest_k = max(d['highest_k'] for d in ds)
    nTotal  = sum(d['len_rs'] for d in ds)
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
    print('\n\n'.join('{}. {}'.format(i,m) for i, m in enumerate(msgs)))

    time_str = '{0:.1f}'.format(nTime)

    print("* nlocs {} '{}', invs {} (p {} (k>0 {}, lem>0 {}, assumes>0 {} redun {}), d {}, u {} e {}), k {}, time {}"
          .format(len(locs), ', '.join(locs), 
                  nTotal, nTs, nk_ge_1, nlemmas_ge_1, nassumes_ge_1, 
                  nTs_dep, nFs, nUs, nEs,
                  highest_k, time_str))

   



def rinfer(ps,ret_idxs=False):
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
    #DO NOT USE THE BELOW 2 COMMENT LINES
    #as they screw up the original indices
    # ps = vset(ps,idfun=str)


    # ps = sorted(ps,reverse=True,key=lambda p: len(get_vars(p)))
    rs_idxs = range(len(ps))
    for i in range(len(ps)):
        assert i in rs_idxs

        idx = rs_idxs.index(i)
        xclude_idxs = rs_idxs[:idx] + rs_idxs[idx+1:]
        if xclude_idxs:
            xclude_ps = And([ps[i_] for i_ in xclude_idxs])
            is_proved = myprove(Not(Implies(xclude_ps,ps[i])))
            if is_proved:
                rs_idxs = xclude_idxs

    if ret_idxs:        
        return rs_idxs
    else:
        return [ps[i] for i in rs_idxs]
    
def myprove(claim):
    s = Solver()
    s.set(timeout=1*1000) 
    s.add(claim)
    rs = s.check()
    if rs == unsat:
        return True
    else:
        return False


if __name__ == "__main__":
    import doctest
    doctest.testmod()


from z3 import *
from vu_common import pause, get_cur_time
from z3util import is_even, is_odd
from scr_miscs import pre_f

from kip_test_common import verify, print_summary

def cavf1a():
    from invs_mpp_dig import x,y, cavf1a_LI0
    
    #loop
    I = And(x <= 5, y == 5)

    T = And(pre_f(x<11),
            If(pre_f(x>=5),y==pre_f(y+1),y==pre_f(y)),
            x == pre_f(x+1))

    LI0 = cavf1a_LI0
    LI_d = verify('cavf1a LI0', [], I, T, LI0, 
                  show_disproved=True,show_model=True,show_redundant=True)
    
    print_summary([LI_d])

def vumemcopy_abstract():
    from invs_mpp_dig import i,d,s,n,siz, vumemcopy_abstract_LI0
    I = And(n<=siz,0<=n,n<=siz-1,0<=s,s<=siz,0<=d,d<=siz,i==0)
    T = And(pre_f(i<=n),
            If(pre_f(i+1>=s),
               d==pre_f(s),
               If(pre_f(d>=i+1),
                  d==pre_f(d),
                  d==pre_f(i+1))),
            i==pre_f(i+1),
            s==pre_f(s),
            n==pre_f(n),
            siz==pre_f(siz))

    """
    Yep, got it 
    """ 
    LI0 = vumemcopy_abstract_LI0
    LI_d = verify('vumemcopy_abstract LI0', [], I, T, LI0, show_disproved=False,show_model=True)

    print_summary([LI_d])

def bubblesort(n):
    c = 0
    for i in range(n):
        for j in range(i+1,n):
            print(i,j)
            c=c+1
    print '#swaps {}'.format(c)


def bubble3():
    
    from invs_mpp_bubble import (t0,t1,t2,x0,x1,x2,bubble3_I,bubble3_LP)
    
    T = And(t0==pre_f(t0), t1==pre_f(t1), t2==pre_f(t2),
            x0==pre_f(x0), x1==pre_f(x1), x2==pre_f(x2))
    
    LP_d = verify('bubble3', [],bubble3_I,T,bubble3_LP)
    print_summary([LP_d])


def bubble4():
    from invs_mpp_bubble import (t0,t1,t2,t3,x0,x1,x2,x3,bubble4_I,bubble4_LP)

    T = And(t0==pre_f(t0), t1==pre_f(t1), t2==pre_f(t2), t3==pre_f(t3),
            x0==pre_f(x0), x1==pre_f(x1), x2==pre_f(x2), x3==pre_f(x3))

    LP_d = verify('bubble4', [],bubble4_I,T,bubble4_LP)
    print_summary([LP_d])


def bubble5():
    from invs_mpp_bubble import (t0,t1,t2,t3,t4,x0,x1,x2,x3,x4,bubble5_I,bubble5_LP)

    T = And(t0==pre_f(t0), t1==pre_f(t1), t2==pre_f(t2), t3==pre_f(t3), t4==pre_f(t4),
            x0==pre_f(x0), x1==pre_f(x1), x2==pre_f(x2), x3==pre_f(x3), x4==pre_f(x4))


    LP_d = verify('bubble5', [],bubble5_I,T,bubble5_LP)
    print_summary([LP_d])





# def oddeven2():
#     from ktp_test_mpp_oddeven2 import (t0,t1,x0,x1,I,LP)

#     T = And(t0==pre_f(t0), t1==pre_f(t1),
#             x0==pre_f(x0), x1==pre_f(x1))

#     LP_d = verify('oddeven2',[],I,T,LP)
#     print_summary([LP_d])


def oddeven3():
    """ I is generated using vcgen (see vcgen.py doctest) """
    
    from invs_mpp_oddeven import (t0,t1,t2,x0,x1,x2,oddeven3_I,oddeven3_LP)
    

    T = And(t0==pre_f(t0), t1==pre_f(t1), t2==pre_f(t2),
            x0==pre_f(x0), x1==pre_f(x1), x2==pre_f(x2))
    
    LP_d = verify('oddeven3', [],oddeven3_I,T,oddeven3_LP)
    print_summary([LP_d])


def oddeven4():
    from invs_mpp_oddeven import (t0,t1,t2,t3,x0,x1,x2,x3,oddeven4_I,oddeven4_LP)

    T = And(t0==pre_f(t0), t1==pre_f(t1), t2==pre_f(t2), t3==pre_f(t3),
            x0==pre_f(x0), x1==pre_f(x1), x2==pre_f(x2), x3==pre_f(x3))

    LP_d = verify('oddeven4', [],oddeven4_I,T,oddeven4_LP)
    print_summary([LP_d])


def oddeven5():
    from invs_mpp_oddeven import (t0,t1,t2,t3,t4,x0,x1,x2,x3,x4,oddeven5_I,oddeven5_LP)

    T = And(t0==pre_f(t0), t1==pre_f(t1), t2==pre_f(t2), t3==pre_f(t3), t4==pre_f(t4),
            x0==pre_f(x0), x1==pre_f(x1), x2==pre_f(x2), x3==pre_f(x3), x4==pre_f(x4))


    LP_d = verify('oddeven5', [],oddeven5_I,T,oddeven5_LP)
    print_summary([LP_d])

# def oddeven6():
#     from ktp_test_mpp_oddeven5 import (t0,t1,t2,t3,t4,t5,x0,x1,x2,x3,x4,x5,I,LP)

#     T = And(t0==pre_f(t0), t1==pre_f(t1), t2==pre_f(t2), t3==pre_f(t3), t4==pre_f(t4),
#             x0==pre_f(x0), x1==pre_f(x1), x2==pre_f(x2), x3==pre_f(x3), x4==pre_f(x4))


#     LP_d = verify('oddeven5', [],I,T,LP)
#     print_summary([LP_d])

# def vusearch3():
#     """
#     9/10:  seems like I can't obtain invariants from traces for this 
#     """
#     from ktp_test_mpp_vusearch3 import (t0,t1,t2,x,r,I,LP)
#     T = And(t0==pre_f(t0),t1==pre_f(t1),t2==pre_f(t2),
#             x==pre_f(x),r==pre_f(r))

#     LP_test = [And(Implies(t0==x,r==1),
#                    Implies(t1==x,r==1),
#                    Implies(t2==x,r==1)),
#                Implies(Not(Or(t0==x,t1 == x,t2==x)),r==0)]
#     LP_d = verify('vusearch3', [],I,T,LP_test)
#     print_summary([LP_d]) 

# def partial_decr0():
#     from ktp_test_mpp_decr0 import i,n,decr0_li0,decr0_LP

#     #loop 1
#     I = i==0
#     T = And(pre_f(i>n),
#             i == pre_f(i - 1),
#             n == pre_f(n))

#     LI0 = decr0_li0

#     LI0_d = verify("partial_decr0 LI0",[],I,T,LI0,
#                    show_disproved=False,show_model=True)

#     #post
#     I = And(LI0_d['Ts'] + [Not(i>n)])
#     T = And(i == pre_f(i), n == pre_f(n))
#     LP = decr0_LP

#     LP_d = verify("partial_decr0 LP",[],I,T,LP,
#                   show_disproved=False,
#                   show_model=True)
    
#     print_summary([LI0_d, LP_d])

# def partial_decr1():
#     from ktp_test_mpp_decr1 import (i,p,q,decr1_li0,decr1_LP)

#     #loop 1
#     I = i == p
#     T = And(pre_f(i > q), 
#             i == pre_f(i - 1), 
#             p == pre_f(p),
#             q == pre_f(q))

#     LI0 = decr1_li0

#     LI0_d = verify("partial_decr1 LI0",[],I,T,LI0)
    
#     #post
#     I = And(LI0_d['Ts'] + [Not(i>q)])
#     T = And(i == pre_f(i), p == pre_f(p), q == pre_f(q))
#     LP = decr1_LP

#     LP_d = verify("partial_decr1 LP",[],I,T,LP)
    
#     print_summary([LI0_d, LP_d])


# def partial_decr2():
#     from ktp_test_mpp_decr2 import i,p,q,r,decr2_li0,decr2_li1,decr2_LP

#     common_body = [i == pre_f(i - 1), 
#                    p == pre_f(p),
#                    q == pre_f(q),
#                    r == pre_f(r)]
#     #loop0
#     I = i == p
#     T = And(pre_f(i > q), *common_body)
#     LI0 = decr2_li0

#     LI0_d = verify("partial_decr2 LI0",[],I,T,LI0)

#     #loop1
#     I = And(LI0_d['Ts'] + [Not(i > q)])
#     T = And(pre_f(i > r), *common_body) 
#     LI1 = decr2_li1

#     LI1_d = verify("partial_decr2 LI1",[],I,T,LI1)

#     #post
#     I = And(LI1_d['Ts'] + [Not(i > r)])
#     T = And(i == pre_f(i),
#             p == pre_f(p),
#             q == pre_f(q),
#             r == pre_f(r))
#     LP = decr2_LP
          
#     LP_d = verify("partial_decr2 LP",[],I,T,LP)

#     print_summary([LI0_d, LI1_d, LP_d])

def partial_decr3():
    from invs_mpp_partial import (i,p,q,r,s,
                                  decr3_LI0,decr3_LI1,
                                  decr3_LI2,decr3_LP)
                                    
    common_body = [i == pre_f(i - 1), 
                   p == pre_f(p),
                   q == pre_f(q),
                   r == pre_f(r),
                   s == pre_f(s)]

    #loop0
    I = i == p
    T = And(pre_f(i > q), *common_body)
    LI0 = decr3_LI0

    LI0_d = verify("partial_decr3 LI0",[],I,T,LI0)

    #loop1
    I = And(LI0_d['Ts'] + [Not(i > q)])
    T = And(pre_f(i > r), *common_body)
    LI1 = decr3_LI1

    LI1_d = verify("partial_decr3 LI1",[],I,T,LI1)

    #loop2
    I = And(LI1_d['Ts'] + [Not(i > r)])
    T = And(pre_f(i > s), *common_body)
    LI2 = decr3_LI2

    LI2_d = verify("partial_decr3 LI2",[],I,T,LI2)

    #post
    I = And(LI2_d['Ts'] + [Not(i > s)])
    T = And(i == pre_f(i),
            p == pre_f(p),
            q == pre_f(q),
            r == pre_f(r),
            s == pre_f(s))
    LP = decr3_LP

    LP_d = verify("partial_decr3 LP",[],I,T,LP)

    print_summary([LI0_d, LI1_d, LI2_d, LP_d])

def partial_decr4():
    from invs_mpp_partial import (i,p,q,r,s,t,
                                  decr4_LI0,decr4_LI1,
                                  decr4_LI2,decr4_LI3,
                                  decr4_LP)

    common_body = [i == pre_f(i - 1), 
                   p == pre_f(p),
                   q == pre_f(q),
                   r == pre_f(r),
                   s == pre_f(s),
                   t == pre_f(t)]

    #loop0
    I = i == p
    T = And(pre_f(i > q), *common_body)
    LI0 = decr4_LI0

    LI0_d = verify("partial_decr4 LI0",[],I,T,LI0)

    #loop1
    I = And(LI0_d['Ts'] + [Not(i > q)])
    T = And(pre_f(i > r), *common_body)
    LI1 = decr4_LI1

    LI1_d = verify("partial_decr4 LI1",[],I,T,LI1)

    #loop2
    I = And(LI1_d['Ts'] + [Not(i > r)])
    T = And(pre_f(i > s), *common_body)
    LI2 = decr4_LI2

    LI2_d = verify("partial_decr4 LI2",[],I,T,LI2)

    #loop3
    I = And(LI2_d['Ts'] + [Not(i > s)])
    T = And(pre_f(i > t), *common_body)
    LI3 = decr4_LI3

    LI3_d = verify("partial_decr4 LI3",[],I,T,LI3)

    #post
    I = And(LI3_d['Ts'] + [Not(i > t)])
    T = And(i == pre_f(i),
            p == pre_f(p),
            q == pre_f(q),
            r == pre_f(r),
            s == pre_f(s),
            t == pre_f(t))
    LP = decr4_LP

    LP_d = verify("partial_decr4 LP",[],I,T,LP)

    print_summary([LI0_d, LI1_d, LI2_d, LI3_d, LP_d])

def partial_decr5():
    from invs_mpp_partial import (i,p,q,r,s,t,u,
                                  decr5_LI0,decr5_LI1,
                                  decr5_LI2,decr5_LI3,decr5_LI4,
                                  decr5_LP)

    common_body = [i == pre_f(i - 1), 
                   p == pre_f(p),
                   q == pre_f(q),
                   r == pre_f(r),
                   s == pre_f(s),
                   t == pre_f(t),
                   u == pre_f(u)]

    #loop 0
    I = i == p
    T = And(pre_f(i > q), *common_body)
    LI0 = decr5_LI0

    LI0_d = verify("partial_decr5 LI0",[],I,T,LI0)

    #loop1
    I = And(LI0_d['Ts'] + [Not(i > q)])
    T = And(pre_f(i > r), *common_body)
    LI1 = decr5_LI1

    LI1_d = verify("partial_decr5 LI1",[],I,T,LI1)

    #loop2
    I = And(LI1_d['Ts'] + [Not(i > r)])
    T = And(pre_f(i > s), *common_body)
    LI2 = decr5_LI2

    LI2_d = verify("partial_decr5 LI2",[],I,T,LI2)

    #loop3
    I = And(LI2_d['Ts'] + [Not(i > s)])
    T = And(pre_f(i > t), *common_body)
    LI3 = decr5_LI3

    LI3_d = verify("partial_decr5 LI3",[],I,T,LI3)

    #loop4
    I = And(LI3_d['Ts'] + [Not(i > t)])
    T = And(pre_f(i > u), *common_body)
    LI4 = decr5_LI4

    LI4_d = verify("partial_decr5 LI4",[],I,T,LI4)

    #post
    I = And(LI4_d['Ts'] + [Not(i > u)])
    T = And(i == pre_f(i),
            p == pre_f(p),
            q == pre_f(q),
            r == pre_f(r),
            s == pre_f(s),
            t == pre_f(t),
            u == pre_f(u))
    LP = decr5_LP

    LP_d = verify("partial_decr5 LP",[],I,T,LP)

    print_summary([LI0_d, LI1_d, LI2_d, LI3_d, LI4_d, LP_d])

# def partial_incr0():
#     from ktp_test_mpp_incr0 import i,n,incr0_LI0,incr0_LP

#     #loop 1
#     I = i==0
#     T = And(pre_f(i<n), 
#             i == pre_f(i + 1), 
#             n == pre_f(n))

#     LI0 = incr0_LI0

#     LI0_d = verify("partial_incr0 LI0",[],I,T,LI0,
#                    show_disproved=False,show_model=True)

#     #post
#     I = And(LI0_d['Ts'] + [Not(i<n)])
#     T = And(i==pre_f(i), n == pre_f(n))
#     LP = incr0_LP

#     LP_d = verify("partial_incr0 LP",[],I,T,LP,
#                   show_disproved=False,
#                   show_model=True)
    
#     print_summary([LI0_d, LP_d])

# def partial_incr1():
#     from ktp_test_mpp_incr1 import (i,p,q,incr1_LI0,incr1_LP)
                                    
#     #loop 1
#     I = i == p
#     T = And(pre_f(i < q), 
#             i == pre_f(i + 1), 
#             p == pre_f(p),
#             q == pre_f(q))

#     LI0 = incr1_LI0

#     LI0_d = verify("partial_incr1 LI0",[],I,T,LI0)

#     #post
#     I = And(LI0_d['Ts'] + [Not(i<q)])
#     T = And(i == pre_f(i), p == pre_f(p), q == pre_f(q))
#     LP = incr1_LP
    
#     LP_d = verify("partial_incr1 LP",[],I,T,LP)
    
#     print_summary([LI0_d, LP_d])


# def partial_incr2():
#     from ktp_test_mpp_incr2 import i,p,q,r,incr2_LI0,incr2_LI1,incr2_LP

#     common_body = [i == pre_f(i + 1), 
#                    p == pre_f(p),
#                    q == pre_f(q),
#                    r == pre_f(r)]
#     #loop0
#     I = i == p
#     T = And(pre_f(i < q), *common_body)
#     LI0 = incr2_LI0

#     LI0_d = verify("partial_incr2 LI0",[],I,T,LI0)

#     #loop1
#     I = And(LI0_d['Ts'] + [Not(i < q)])
#     T = And(pre_f(i < r), *common_body) 
#     LI1 = incr2_LI1

#     LI1_d = verify("partial_incr2 LI1",[],I,T,LI1)

#     #post
#     I = And(LI1_d['Ts'] + [Not(i < r)])
#     T = And(i == pre_f(i),
#             p == pre_f(p),
#             q == pre_f(q),
#             r == pre_f(r))
#     LP = incr2_LP

#     LP_d = verify("partial_incr2 LP",[],I,T,LP)

#     print_summary([LI0_d, LI1_d, LP_d])

def partial_incr3():
    from invs_mpp_partial import (i,p,q,r,s,
                                  incr3_LI0,incr3_LI1,
                                  incr3_LI2,incr3_LP)

    common_body = [i == pre_f(i + 1), 
                    p == pre_f(p),
                    q == pre_f(q),
                    r == pre_f(r),
                    s == pre_f(s)]

    #loop0
    I = i == p
    T = And(pre_f(i < q), *common_body)
    LI0 = incr3_LI0

    LI0_d = verify("partial_incr3 LI0",[],I,T,LI0)

    #loop1
    I = And(LI0_d['Ts'] + [Not(i < q)])
    T = And(pre_f(i < r), *common_body)
    LI1 = incr3_LI1

    LI1_d = verify("partial_incr3 LI1",[],I,T,LI1)

    #loop2
    I = And(LI1_d['Ts'] + [Not(i < r)])
    T = And(pre_f(i < s), *common_body)
    LI2 = incr3_LI2

    LI2_d = verify("partial_incr3 LI2",[],I,T,LI2)

    #post
    I = And(LI2_d['Ts'] + [Not(i < s)])
    T = And(i == pre_f(i),
            p == pre_f(p),
            q == pre_f(q),
            r == pre_f(r),
            s == pre_f(s))
    LP = incr3_LP

    LP_d = verify("partial_incr3 LP",[],I,T,LP)

    print_summary([LI0_d, LI1_d, LI2_d, LP_d])

def partial_incr4():
    from invs_mpp_partial import (i,p,q,r,s,t,
                                  incr4_LI0,incr4_LI1,
                                  incr4_LI2,incr4_LI3,
                                  incr4_LP)
    
    common_body = [i == pre_f(i + 1), 
                    p == pre_f(p),
                    q == pre_f(q),
                    r == pre_f(r),
                    s == pre_f(s),
                    t == pre_f(t)]

    #loop0
    I = i == p
    T = And(pre_f(i < q), *common_body)
    LI0 = incr4_LI0

    LI0_d = verify("partial_incr4 LI0",[],I,T,LI0)

    #loop1
    I = And(LI0_d['Ts'] + [Not(i < q)])
    T = And(pre_f(i < r), *common_body)
    LI1 = incr4_LI1

    LI1_d = verify("partial_incr4 LI1",[],I,T,LI1)

    #loop2
    I = And(LI1_d['Ts'] + [Not(i < r)])
    T = And(pre_f(i < s), *common_body)
    LI2 = incr4_LI2

    LI2_d = verify("partial_incr4 LI2",[],I,T,LI2)

    #loop3
    I = And(LI2_d['Ts'] + [Not(i < s)])
    T = And(pre_f(i < t), *common_body)
    LI3 = incr4_LI3

    LI3_d = verify("partial_incr4 LI3",[],I,T,LI3)

    #post
    I = And(LI3_d['Ts'] + [Not(i < t)])
    T = And(i == pre_f(i),
            p == pre_f(p),
            q == pre_f(q),
            r == pre_f(r),
            s == pre_f(s),
            t == pre_f(t))
    LP = incr4_LP

    LP_d = verify("partial_incr4 LP",[],I,T,LP)

    print_summary([LI0_d, LI1_d, LI2_d, LI3_d, LP_d])

def partial_incr5():
    from invs_mpp_partial import (i,p,q,r,s,t,u,
                                  incr5_LI0,incr5_LI1,
                                  incr5_LI2,incr5_LI3,incr5_LI4,
                                  incr5_LP)
    
    common_body = [i == pre_f(i + 1), 
                   p == pre_f(p),
                   q == pre_f(q),
                   r == pre_f(r),
                   s == pre_f(s),
                   t == pre_f(t),
                   u == pre_f(u)]

    #loop 0
    I = i == p
    T = And(pre_f(i < q), *common_body)
    LI0 = incr5_LI0

    LI0_d = verify("partial_incr5 LI0",[],I,T,LI0)

    #loop1
    I = And(LI0_d['Ts'] + [Not(i < q)])
    T = And(pre_f(i < r), *common_body)
    LI1 = incr5_LI1

    LI1_d = verify("partial_incr5 LI1",[],I,T,LI1)

    #loop2
    I = And(LI1_d['Ts'] + [Not(i < r)])
    T = And(pre_f(i < s), *common_body)
    LI2 = incr5_LI2

    LI2_d = verify("partial_incr5 LI2",[],I,T,LI2)

    #loop3
    I = And(LI2_d['Ts'] + [Not(i < s)])
    T = And(pre_f(i < t), *common_body)
    LI3 = incr5_LI3

    LI3_d = verify("partial_incr5 LI3",[],I,T,LI3)

    #loop4
    I = And(LI3_d['Ts'] + [Not(i < t)])
    T = And(pre_f(i < u), *common_body)
    LI4 = incr5_LI4

    LI4_d = verify("partial_incr5 LI4",[],I,T,LI4)

    #post
    I = And(LI4_d['Ts'] + [Not(i < u)])
    T = And(i == pre_f(i),
            p == pre_f(p),
            q == pre_f(q),
            r == pre_f(r),
            s == pre_f(s),
            t == pre_f(t),
            u == pre_f(u))
    LP = incr5_LP
    LP_d = verify("partial_incr5 LP",[],I,T,LP)

    print_summary([LI0_d, LI1_d, LI2_d, LI3_d, LI4_d, LP_d])



def verify_mpp():
    print get_cur_time(time_only=False)
    cavf1a()
    # vumemcopy_abstract()
    # oddeven3()
    # oddeven4()
    # oddeven5()

    # bubble3()
    # bubble4()
    # bubble5()

    # # partial_decr0()
    # # partial_decr1()
    # # partial_decr2()
    # partial_decr3()
    # partial_decr4()
    # partial_decr5()


    # # partial_incr0()
    # # partial_incr1()
    # # partial_incr2()
    # partial_incr3()
    # partial_incr4()
    # partial_incr5()

if __name__  == "__main__":
    verify_mpp()
    

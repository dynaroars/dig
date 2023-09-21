from z3 import *

def atmostone(k):
    A = BoolVector('a',k)

    F1 = And([Not(A[i]) for i in range(k)])
    F2 = [And([Not(A[i_]) if i_!=i else A[i_] for i_ in range(k)])
          for i in range(k)]

    print F1
    print F2
    F3 = Or([F1] + F2)
    
    S = Solver()
    S.add(F3)
    print S
    print S.check()
    print S.model()




def constraint1_(p,H):
    rs = Or([Bool('P_%d_%d'%(p,h)) for h in range(H)])
    return rs

def constraint1(P,H):
    return And([constraint1_(p,H) for p in range(P)])

def constraint2(P,H):
    rs = []
    for h in range(H):
        for i in range(P):
            for j in range(i+1,P):
                f = Or(Not(Bool('P_%d_%d'%(i,h))),Not(Bool('P_%d_%d'%(j,h))))
                rs.append(f)
    return And(rs)



def vdecs(P,H):
    rs = '\n'.join(['P%d_%d'%(p,h) for p in range(P) for h in range(H)])
    return rs

def pigeon(P):
    H = P - 1
    assert P == H + 1

    vs = vdecs(P,H)
    c1 = constraint1(P,H)
    c2 = constraint2(P,H)
    cs = And(c1,c2)
    S = Solver()
    S.add(cs)
    print S.check()


from z3 import *
from vu_common import pause
from z3util import is_even, is_odd, get_z3_version
from scr_miscs import pre_f
from kip_test_common import verify, print_summary

def divbin():
    from invs_nla_dig import A,B,q,r,b, divbin_LI0, divbin_LI1
    
    #First loop LI0
    I = And(A>0, B>0, q == 0, r == A, b == B, r >= b)
    T = And(pre_f(r) >= pre_f(b),
            A == pre_f(A),
            B == pre_f(B),
            q == pre_f(q),
            r == pre_f(r),
            b == 2*pre_f(b))
    
    LI0 = divbin_LI0
    LI0_d = verify("divbin LI0",[],I,T,LI0)
    
    #Second while loop LI1
    
    #need the inv even(b) because b/2 uses int div
    #also note that when the assignment statement b = b/2 occurs, b is 
    #guarnteed to be even -- though we cannot automatically generate
    #this invariant so has to manually provide
    assumes = [is_even(b)]
    #q == 0, A == r, #LI0
    I = And(LI0_d['Ts'] + [Not(r>=b)])  #negation of 1st loop guard
    
    T = And(pre_f(b != B),
            If(pre_f(r >= b/2),
               And(q == pre_f(2 * q + 1), 
                   r == pre_f(r - b / 2),
                   b == pre_f(b / 2)),
               
               And(q == pre_f(2 * q), 
                   r == pre_f(r), 
                   b == pre_f(b / 2))),
            A==pre_f(A),
            B==pre_f(B))
    
    
    LI1 = divbin_LI1
    LI1_d = verify("divbin LI1",assumes,I,T,LI1)

    print_summary([LI0_d,LI1_d])


def cohendiv():
    #TODO: LI0_d
    from invs_nla_dig import q,x,r,y,a,b, cohendiv_LI0, cohendiv_LI1

    #inner loop
    I = And(x == r+q*y, r>=y,  #invs of outer loop & guard of outer loop 
            a==1, b==y)
        
    T =  And(pre_f(r >= 2*b),
             a == 2*pre_f(a), 
             b == 2*pre_f(b), 
             r == pre_f(r), 
             y == pre_f(y), 
             x == pre_f(x), 
             q == pre_f(q))

    LI1 = cohendiv_LI1
    LI1_d =verify("cohendiv LI1",[],I,T,LI1)
    
    #outer loop
    I = And(x>=1,y>=1,q==0,r==x)

    T = And(pre_f(a*y== b),  #invs of inner loop
            pre_f(q*y+r == x),
            pre_f(Not(r >= 2*b)),  #guard of inner loop
            x == pre_f(x),
            y == pre_f(y),
            q == pre_f(q + a),
            r == pre_f(r - b),
            a == pre_f(a),
            b == pre_f(b))

    LI0 = cohendiv_LI0
    LI0_d = verify("cohendiv LI0",[],I,T, LI0)

    print_summary([LI0_d,LI1_d])


def mannadiv():
    from invs_nla_dig import x1,x2,y1,y2,y3, mannadiv_LI0

    #loop
    I = And(y1 == 0,y2 == 0, y3 == x1)
    T = And(pre_f(y3 != 0),
            If(pre_f(y1 + 1 == x2),
               And(x1 == pre_f(x1), 
                   x2 == pre_f(x2),
                   y1 == pre_f(y1+1), 
                   y2 == 0,           
                   y3 == pre_f(y3 - 1)),
               
               And(x1 == pre_f(x1), 
                   x2 == pre_f(x2),
                   y1 == pre_f(y1),   
                   y2 == pre_f(y2 + 1), 
                   y3 == pre_f(y3 - 1))))


    LI0 = mannadiv_LI0
    LI0_d = verify('mannadiv LI0',[],I,T,LI0)
    print_summary([LI0_d])

def hard():
    from invs_nla_dig import A,B,r,d,p,q, hard_LI0, hard_LI1

    #first loop
    I = And(A >= 0, B >= 1,
            r == A, 
            d == B,
            p == 1, 
            q == 0)

    T = And(pre_f(r >= d),
            d  == pre_f(2 * d),
            p  == pre_f(2 * p),
            A  == pre_f(A),
            B  == pre_f(B),
            r  == pre_f(r),
            q  == pre_f(q))

    LI0 = hard_LI0
    LI0_d = verify("hard LI0",[],I,T,LI0)

    #second loop
    #these assumptionscannot be automatically generated
    #When p#1, then d and p are even
    assumes = [is_even(d), is_even(p)]
        
    #q==0 , A - r == 0, B*p == d,  #LI0             
    I = And(LI0_d['Ts'] + [Not(r>=d)])

    T = And(pre_f(p != 1),
            If(pre_f(r >= d/2),
               And(p  == pre_f(p / 2),
                   d == pre_f(d / 2),
                   r == pre_f(r - d / 2),
                   q == pre_f(q + p  / 2)),
               
               And(p == pre_f(p / 2),
                   d == pre_f(d / 2),
                   r == pre_f(r),
                   q == pre_f(q))),
            A  == pre_f(A),
            B  == pre_f(B))
    
    
    LI1 = hard_LI1
    LI1_d = verify("hard LI1",assumes,I,T,LI1)

    print_summary([LI0_d, LI1_d])

def sqrt1():
    from invs_nla_dig import a, n, t, s, sqrt1_LI0, sqrt1_LI0_annotated

    #Loop Invs
    I = And(t == 1, a == 0, s == 1)
    T = And(pre_f(s <= n),
            a == pre_f(a + 1),
            t == pre_f(t + 2),
            s == pre_f(s + t + 2),
            n == pre_f(n))


    LI0 = sqrt1_LI0 + sqrt1_LI0_annotated #so that consistent with paper
    LI0_d = verify('sqrt1 LI0',[],I,T,LI0)
    print_summary([LI0_d])


def dijkstra():
    from invs_nla_dig import n, r, p, q, h, dijkstra_LI0, dijkstra_LI1

    #first loop
    I = And(n>=0,p == 0, q==1,r==n,h==0)
    T = And(pre_f(q<=n),
            n == pre_f(n),
            r == pre_f(r),
            p == pre_f(p),
            q == pre_f(4*q),
            h == pre_f(h))


    LI0 = dijkstra_LI0
    LI0_d = verify('dijkstra LI0',[],I,T,LI0)

    
    #second loop
    assumes = [q%4==0]
    #h == 0 , n == r, p == 0, #LI0
    I = And(LI0_d['Ts'] + [Not(q<=n)])
    T = And(pre_f(q!=1),
            If(pre_f(r>=p+q/4),
               And(r == pre_f(r - (p+q/4)),
                   p == pre_f(p/2 + q/4),
                   q == pre_f(q/4),
                   h == pre_f(p+q/4)),
               
               And(r == pre_f(r),
                   p == pre_f(p/2),
                   q == pre_f(q/4),
                   h == pre_f(p+q/4))),
            n == pre_f(n))
                
    #n*q == p*p + q*r,  #proved only when declare vars as reals, ow. long time
           #h*h*p - 4*h*n*q + 4*h*q*r + 4*n*p*q - p*q*q - 4*p*q*r == 0, z3 long time
           #h*h*h - 12*h*n*q - h*q*q + 12*h*q*r + 16*n*p*q - 4*p*q*q - 16*p*q*r == 0, z3 long time
           #h*h*n - h*h*r - 4*h*n*p + 4*h*p*r + 4*n*n*q - n*q*q - 8*n*q*r + q*q*r + 4*q*r*r == 0, #z3 froze
    LI1 = dijkstra_LI1

    LI1_d = verify('dijkstra LI1',assumes,I,T,LI1)
    
    print_summary([LI0_d, LI1_d])


def freire1():
    from invs_nla_dig2 import a, x, r, freire1_LI0

    #loop
    I = And(x == a / 2.0, r == 0.0)
    T = And(pre_f(x > r),
            a == pre_f(a),
            x == pre_f(x - r),
            r == pre_f(r + 1))

    LI0 = freire1_LI0
    LI0_d = verify('freire1 LI0',[],I,T,LI0)
    print_summary([LI0_d])
    

def freire2():
    #z3 has problem doing integer arith with int and real so
    #just declare r as real instead of int
    #it doesn't get problem in this program since no int division involved
    from invs_nla_dig2 import a, x, s, r, freire2_LI0#, freire2_LI0_annotated

    I = And(x == a, r == 1, s == 3.25)
    T = And(pre_f(x-s > 0.0),
            a == pre_f(a),
            x == pre_f(x - s),
            s == pre_f(s + 6.0 * r + 3),
            r == pre_f(r + 1))

    LI0 = freire2_LI0 #+ freire2_LI0_annotated
    LI0_d = verify('freire2 LI0', [], I, T, LI0)
    print_summary([LI0_d])

    
def cohencu():
    #Good example to use in paper 
    from invs_nla_dig import a, n, x , y, z, cohencu_LI0#, cohencu_LI0_annotated

    #loop
    I = And(n==0, x==0, y==1, z==6)
    T = And(pre_f(n <= a),
            a == pre_f(a),
            n == pre_f(n + 1),
            x == pre_f(x + y),
            y == pre_f(y + z),
            z == pre_f(z + 6))

    LI0 = cohencu_LI0 #+ cohencu_LI0_annotated
    LI0_d = verify('cohencu LI0',[],I,T,LI0)

    print_summary([LI0_d])



def euclidex1():
    from invs_nla_dig import x, y, a, b, p, q, r, s, euclidex1_LI0

    I = And(a == x, b == y, p == 1, q == 0, r == 0, s == 1)
    T = And(pre_f(a != b),
            If(pre_f(a > b),
               And(x == pre_f(x),
                   y == pre_f(y),
                   a == pre_f(a - b),
                   b == pre_f(b),
                   p == pre_f(p - q),
                   q == pre_f(q),
                   r == pre_f(r - s),
                   s == pre_f(s)),
               And(x == pre_f(x),
                   y == pre_f(y),
                   a == pre_f(a),
                   b == pre_f(b - a),
                   p == pre_f(p),
                   q == pre_f(q - p),
                   r == pre_f(r),
                   s == pre_f(s - r))))

    LI0 = euclidex1_LI0
    LI0_d = verify('euclidex1 LI0',[],I,T,LI0)
    print_summary([LI0_d])


def euclidex2():
    from invs_nla_dig import  a, b, c, p, q, r, s, x, y, k, euclidex2_LI0, euclidex2_LI1

    #inner loop
    I = And(p*x+r*y==a, q*x+s*y==b, b!=0, #invs and guard of outer loop
            c==a,
            k==0)
    T = And(pre_f(c>=b),
            a==pre_f(a),
            b==pre_f(b),
            c==pre_f(c-b),
            p==pre_f(p),
            q==pre_f(q),
            r==pre_f(r),
            s==pre_f(s),
            x==pre_f(x),
            y==pre_f(y),
            k==pre_f(k+1))
    
    LI1 = euclidex2_LI1
    LI1_d = verify('euclidex2 LI1',[],I,T,LI1)
    
    #outer loop
    I = And(a == x,
            b == y,
            p == 1,
            q == 0,
            r == 0,
            s == 1)

    T = And(pre_f(p*x+r*y==a),
            pre_f(q*x+s*y==b),
            pre_f(b*k+c==a),
            pre_f(Not(c >= b)),
            a == pre_f(b),
            b == pre_f(c),
            c == pre_f(c),
            p == pre_f(q),
            q == pre_f(p-q*k),
            r == pre_f(s),
            s == pre_f(r-s*k),
            x == pre_f(x),
            y == pre_f(y),
            k == pre_f(k))

    LI0 = euclidex2_LI0
    LI0_d = verify('euclidex2 LI1', [], I, T, LI0)
    print_summary([LI1_d,LI0_d])

def euclidex3():
    from invs_nla_dig import a, b, y, r, x, p, q, s, d, v, k, c, euclidex3_LI0, euclidex3_LI1, euclidex3_LI2

    #inner most loop
    I =  And(b*k - a + c == 0,
             p*x + r*y - a == 0,
             q*x + s*y - b == 0,
             c>=b,
             d==1,
             v==b)

    T = And(pre_f(c >= 2*v),
            a == pre_f(a),
            b == pre_f(b),
            y == pre_f(y),
            r == pre_f(r),
            x == pre_f(x),
            p == pre_f(p),
            q == pre_f(q),
            s == pre_f(s),
            d == pre_f(2*d),
            v == pre_f(2*v),
            k == pre_f(k),
            c == pre_f(c))
        

    LI2 = euclidex3_LI2
    LI2_d = verify("euclidex3 LI2",[],I,T,LI2)

    #inner loop
    I = And(p*x + r*y - a == 0,
            q*x + s*y - b == 0,
            b!=0,
            c == a, k == 0)
    T = And(pre_f(p*x+r*y == a),
            pre_f(q*x+s*y == b),
            pre_f(b*k+c == a),
            pre_f(b*d == v),
            pre_f(Not(c>=b)),
            a == pre_f(a),
            b == pre_f(b),
            y == pre_f(y),
            r == pre_f(r),
            x == pre_f(x),
            p == pre_f(p),
            q == pre_f(q),
            s == pre_f(s),
            d == pre_f(d),
            v == pre_f(v),
            c == pre_f(c - v),
            k == pre_f(k + d))
    
    LI1 = euclidex3_LI1
    LI1_d = verify("euclidex3 LI1",[],I,T,LI1)


    #outer loop
    I = And(a == x,
            b == y,
            p == 1,
            q == 0,
            r == 0,
            s == 1)

    T = And(pre_f(p*x+r*y==a),
            pre_f(q*x+s*y==b),
            pre_f(b*k+c==a),
            pre_f(Not(c >= b)),
            a == pre_f(b),
            b == pre_f(c),
            c == pre_f(c),
            p == pre_f(q),
            q == pre_f(p-q*k),
            r == pre_f(s),
            s == pre_f(r-s*k),
            x == pre_f(x),
            y == pre_f(y),
            k == pre_f(k))


    LI0 = euclidex3_LI0
    LI0_d = verify("euclidex3 LI0",[],I,T,LI0)
    print_summary([LI2_d,LI1_d,LI0_d])


def lcm1():
    from invs_nla_dig import  a, b, x, y, u, v, lcm1_LI0, lcm1_LI1, lcm1_LI2

    #inner loop 1
    I = And(a*b - u*x - v*y == 0, x!=y)
    T = And(pre_f(x > y),
            a == pre_f(a),
            b == pre_f(b),
            x == pre_f(x - y),
            y == pre_f(y),
            u == pre_f(u),
            v == pre_f(v + u))

    LI1 = lcm1_LI1
    
    LI1_d = verify("lcm1 LI1",[],I,T,LI1)
    
    #inner loop 2
    I = And(a*b - u*x - v*y == 0, Not(x > y))
    T = And(pre_f(x < y),
            a == pre_f(a),
            b == pre_f(b),
            x == pre_f(x),
            y == pre_f(y - x),
            u == pre_f(u + v),
            v == pre_f(v))


    LI2 = lcm1_LI2
    LI2_d = verify("lcm1 LI2",[],I,T,LI2)

    #outer loop
    I = And(x == a, y == b , u == b, v == 0)
    T = And(pre_f(a*b - u*x - v*y == 0), 
            pre_f(Not(x < y)),
            a == pre_f(a),
            b == pre_f(b),
            x == pre_f(x),
            y == pre_f(y),
            u == pre_f(u),
            v == pre_f(v))
            
    LI0 = lcm1_LI0
    LI0_d = verify("lcm1 LI0", [],I,T,LI0)
    
    print_summary([LI0_d,LI1_d,LI2_d])

    
def lcm2():
    from invs_nla_dig import a, b, x, y, u, v, lcm2_LI0

    #loop
    I = And(x == a, y == b , u == b , v == a)
    T = And(pre_f(x != y),
            If(pre_f(x > y),
               And(a == pre_f(a),
                   b == pre_f(b),
                   y == pre_f(y),
                   x == pre_f(x - y),
                   u == pre_f(u),
                   v == pre_f(v + u)),
               And(a == pre_f(a),
                   b == pre_f(b),
                   y == pre_f(y - x),
                   x == pre_f(x),
                   u == pre_f(u + v),
                   v == pre_f(v))))

    LI0 = lcm2_LI0
    LI0_d = verify('lcm2 LI0',[],I,T,LI0)
    print_summary([LI0_d])

def prodbin():
    from invs_nla_dig import a, b, x, y, z, prodbin_LI0
    I = And(x == a, y == b, z == 0)

    T = And(pre_f(y != 0),
            If(pre_f(is_odd(y)),
               And(a == pre_f(a),
                   b == pre_f(b),
                   x == pre_f(2 *x),
                   y == pre_f((y - 1) / 2),
                   z == pre_f(z + x)),
               
               And(a == pre_f(a),
                   b == pre_f(b),
                   x == pre_f(2 * x),
                   y == pre_f(y / 2),
                   z == pre_f(z))))

    LI0 = prodbin_LI0
    LI0_d = verify('prodbin LI0', [], I, T, LI0)
    print_summary([LI0_d])


def prod4br():

    from invs_nla_dig import x,y,a,b,p,q, prod4br_LI0

    I = And(a == x, b == y, p == 1,q == 0)
    T = And(pre_f(And(a!=0, b!=0)),

            If(pre_f(And(a % 2 == 0, b % 2 ==0)),

                And(x == pre_f(x),
                    y == pre_f(y),
                    a == pre_f(a/2),
                    b == pre_f(b/2),
                    p == pre_f(4*p),
                    q == pre_f(q)),

                If(pre_f(And(a % 2 == 1, b % 2 ==0)),
                   And(x == pre_f(x),
                       y == pre_f(y),
                       a == pre_f(a-1),
                       b == pre_f(b),
                       p == pre_f(p),
                       q == pre_f(q+b*p)),

                   If(pre_f(And(a % 2 ==0, b % 2 == 1)),
                      And(x == pre_f(x),
                          y == pre_f(y),
                          a == pre_f(a),
                          b == pre_f(b-1),
                          p == pre_f(p),
                          q == pre_f(q+a*p)),

                      And(x == pre_f(x),
                          y == pre_f(y),
                          a == pre_f(a-1),
                          b == pre_f(b-1),
                          p == pre_f(p),
                          q == pre_f(q+(a-1+b-1+1)*p))))))

    LI0 = prod4br_LI0
    LI0_d = verify('prod4br LI0', [], I, T, LI0)
    print_summary([LI0_d])

def fermat1():
    from invs_nla_dig import A,R,u,v,r, fermat1_LI0, fermat1_LI1, fermat1_LI2

    #inner loop 1
    I = And(u*u - v*v - 4*A - 4*r - 2*u + 2*v == 0, r!=0)
    T = And(pre_f(r > 0),
            A == pre_f(A),
            R == pre_f(R),
            u == pre_f(u),
            r == pre_f(r - v),
            v == pre_f(v + 2))

    LI1 = fermat1_LI1
    LI1_d = verify('fermat1 LI1',[],I,T,LI1)
    
    #inner loop 2
    I = And(u*u - v*v - 4*A - 4*r - 2*u + 2*v == 0, Not(r > 0))
    T = And(pre_f(r < 0),
            A == pre_f(A),
            R == pre_f(R),
            u == pre_f(u + 2),
            r == pre_f(r + u),
            v == pre_f(v))

    LI2 = fermat1_LI2
    LI2_d = verify('fermat1 LI2',[],I,T,LI2)

    #outer loop
    I = And(u == 2*R+1, v == 1, r == R*R-A)
    T = And(pre_f(u*u - v*v - 4*A - 4*r - 2*u + 2*v == 0), 
            pre_f(Not(r < 0)),
            A == pre_f(A),
            R == pre_f(R),
            u == pre_f(u),
            r == pre_f(r),
            v == pre_f(v))

    LI0 = fermat1_LI0
    LI0_d = verify('fermat1 LI0',[],I,T,LI0)
    
    print_summary([LI1_d,LI2_d,LI0_d])


def fermat2():
    from invs_nla_dig import A, R, u, v, r, fermat2_LI0


    I = And(u == 2*R+1, v == 1, r == R*R-A)
    T = And(pre_f(r != 0),
            If(pre_f(r) > 0,
               And(A == pre_f(A),
                   R == pre_f(R),
                   u == pre_f(u),
                   v == pre_f(v + 2),
                   r == pre_f(r - v)),
               
               And(A == pre_f(A),
                   R == pre_f(R),
                   u == pre_f(u + 2),
                   v == pre_f(v),
                   r == pre_f(r) + pre_f(u))))

    LI0 = fermat2_LI0
     
    LI0_d = verify("fermat2 LI0",[],I,T,LI0)
    print_summary([LI0_d])


def geo1():
    from invs_nla_dig import x, y, z, c, k, geo1_LI0

    #loop
    I = And(x == 1, y == z, c == 1)
    T = And(pre_f(c < k),
            x == pre_f(x * z + 1),
            y == pre_f(y * z),
            z == pre_f(z),
            c == pre_f(c + 1),
            k == pre_f(k))

    LI0 = geo1_LI0
    LI0_d = verify("geo1 LI0", [], I, T, LI0)
    print_summary([LI0_d])


def geo2():
    from invs_nla_dig import x, y, z, c, k, geo2_LI0

    #loop
    I = And(x == 1, y == 1, c == 1)
    T = And(pre_f(c < k),
            x == pre_f(x * z + 1),
            y == pre_f(y * z),
            z == pre_f(z),
            c == pre_f(c + 1),
            k == pre_f(k))


    LI0 =  geo2_LI0
    LI0_d = verify('geo2 LI0', [], I, T, LI0)
    print_summary([LI0_d])


def geo3():

    from invs_nla_dig import x, y, z, a , c, k, geo3_LI0
    
    #loop
    I = And(x == a, y == 1, c == 1)
    T = And(c < k,
            x == pre_f(x * z) + a,
            y == pre_f(y * z),
            z == pre_f(z),
            a == pre_f(a),
            c == pre_f(c),
            k == pre_f(k))

    LI0 =  geo3_LI0
    LI0_d = verify("geo3 LI0", [], I, T, LI0)
    print_summary([LI0_d])


def ps2():
    from invs_nla_dig import x, y, c, k, ps2_LI0

    #loop
    I = And(y == 0, x == 0, c == 0)
    T = And(pre_f(c < k),
            x == pre_f(x + y + 1),
            y == pre_f(y + 1),
            c == pre_f(c + 1),
            k == pre_f(k))

    LI0 = ps2_LI0
    LI0_d = verify("ps2 LI0", [], I, T, LI0)
    print_summary([LI0_d])

def ps3():

    from invs_nla_dig import x, y, c, k, ps3_LI0

    #loop
    I = And(y == 0, x == 0, c == 0)
    T = And(pre_f(c < k),
            x == pre_f((y + 1) * (y + 1) + x),
            y == pre_f(y + 1),
            c == pre_f(c + 1),
            k == pre_f(k))

    LI0 = ps3_LI0
    LI0_d = verify("ps3 LI0", [], I, T, LI0)
    print_summary([LI0_d])

def ps4():
    from invs_nla_dig import x, y, c, k, ps4_LI0

    #loop
    I = And(y == 0, x == 0, c == 0)
    T = And(pre_f(c < k),
            x == pre_f((y + 1) * (y + 1) * (y + 1) + x),
            y == pre_f(y + 1),
            c == pre_f(c + 1),
            k == pre_f(k))

    LI0 = ps4_LI0
    LI0_d = verify("ps4 LI0", [], I, T, LI0)
    print_summary([LI0_d])

def ps5():

    from invs_nla_dig import x, y, c, k, ps5_LI0

    #loop
    I = And(y == 0, x == 0, c == 0)
    T = And(pre_f(c < k),
            x == pre_f((y + 1) * (y + 1) * (y + 1) * (y + 1)+ x),
            y == pre_f(y + 1),
            c == pre_f(c + 1),
            k == pre_f(k))

    LI0 = ps5_LI0
    LI0_d = verify("ps5 LI0", [], I, T, LI0)
    print_summary([LI0_d])
           
def ps6():
    from invs_nla_dig import x, y, c, k, ps6_LI0

    #loop
    I = And(k>=0, y == 0, x == 0, c == 0)
    T = And(pre_f(c < k),
            x == pre_f((y + 1) * (y + 1) * (y + 1) * (y + 1) * (y+1) +  x),
            y == pre_f(y + 1),
            c == pre_f(c + 1),
            k == pre_f(k))

    LI0 = ps6_LI0
    LI0_d = verify("ps6 LI0", [], I, T, LI0)
    print_summary([LI0_d])



    

def knuth():

    from invs_nla_dig import n,a,r,k,q,d,s,t, knuth_LI0#,knuth_LI0_annotated

    #note, since cannot encode s=sqrt(n),
    #still preserve soundness if can be proved (but if disproved, then
    #can be spurious)
    I = And(d == a, r == n % d, t == 0, d > 2, k == n % (d-2), 
            q == 4*(n/(d-2) - n/d)) 

    T = And(pre_f(And(s>=d, r!=0)),
            If(pre_f(2*r-k+q<0),
               And(n == pre_f(n),
                   a == pre_f(a),
                   r == pre_f(2*r-k+q+d+2),
                   k == pre_f(r),
                   q == pre_f(q + 4),
                   d == pre_f(d + 2),
                   
                   s == pre_f(s),
                   t == pre_f(r)),
               If(pre_f(And(2*r-k+q>=0, 2*r-k+q<d+2)),
                  And(n == pre_f(n),
                      a == pre_f(a),
                      r == pre_f(2*r-k+q),
                      k == pre_f(r),
                      q == pre_f(q),
                      d == pre_f(d + 2),
                      s == pre_f(s),
                      t == pre_f(r)),
                  If(pre_f(And(2*r-k+q>=0, 2*r-k+q>=d+2, 2*r-k+q<2*d+4)),
                     And(n == pre_f(n),
                         a == pre_f(a),
                         r == pre_f(2*r-k+q-d-2),
                         k == pre_f(r),
                         q == pre_f(q - 4),
                         d == pre_f(d + 2),
                         s == pre_f(s),
                         t == pre_f(r)),
                     And(n == pre_f(n),
                         a == pre_f(a),
                         r == pre_f(2*r-k+q-2*d-4),
                         k == pre_f(r),
                         q == pre_f(q - 8),
                         d == pre_f(d + 2),
                         s == pre_f(s),
                         t == pre_f(r))))))
    
    LI0 = knuth_LI0 #+ knuth_LI0_annotated
    LI0_d = verify('knuth LI0',[],I,T,LI0)
    print_summary([LI0_d])


def verify_nla():
    cohendiv()
    divbin()
    mannadiv()
    hard()
    sqrt1()
    dijkstra()
    freire1()
    freire2()
    cohencu()
    euclidex1()   #disproved correct ones ??
    euclidex2()
    euclidex3()
    lcm1()
    lcm2()
    prodbin()  #cannot prove
    prod4br()
    fermat1()
    fermat2()
    knuth()
    geo1()
    geo2()
    geo3()

    ps2()
    ps3()
    ps4()
    ps5()
    ps6()
    

if __name__  == "__main__":
    verify_nla()
    print 'z3 version ', '.'.join(map(str,get_z3_version()))
    

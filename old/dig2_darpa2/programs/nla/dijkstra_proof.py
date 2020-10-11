import z3
p,r,q,n,h = z3.Ints("p r q n h")

e1 = (p*p + r*q == n*q);
e2 = h*h*p - z3.IntVal("4")*h*n*q + z3.IntVal("4")*h*q*r + 4*n*p*q - p*q*q == z3.IntVal("4")*p*q*r 
e3 =h*h*n - h*h*r - z3.IntVal("4")*h*n*p + z3.IntVal("4")*h*p*r + z3.IntVal("4")*n*n*q - n*q*q - z3.IntVal("8")*n*q*r + q*q*r + z3.IntVal("4")*q*r*r == z3.IntVal("0")
e4 = h*h*h - z3.IntVal("12")*h*n*q - h*q*q + z3.IntVal("12")*h*q*r + z3.IntVal("16")*n*p*q - z3.IntVal("4")*p*q*q - z3.IntVal("16")*p*q*r == z3.IntVal("0")



e12 = z3.And(e1,e2)
z3.prove(z3.Implies(e12, e3))
#counterexample
#[h = -7, n = -2, r = -1, q = 0, p = 0]

e13 = z3.And(e1,e3)
z3.prove(z3.Implies(e13, e2))

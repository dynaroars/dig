
import z3

f = z3.Or(z3.And(x <= -2 , y==0), x== y -1)
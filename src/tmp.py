
import z3

from helpers.miscs import Miscs
from data.symstates import SymStates

x = z3.Int('x')
y = z3.Int('y')
f = z3.Or(z3.And(x <= -2 , y==0), x== y -1)

terms = Miscs.get_terms_fixed_coefs([x,y], 2, 2)

for t in terms:
    v,stat = SymStates.mmaximize(f, t, iupper=20)
    if v is not None:
        assert isinstance(v, int), v
        c = t <= v
        print(c)



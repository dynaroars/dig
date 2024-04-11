import sympy
import helpers.miscs
import pdb
DBG = pdb.set_trace


a,b,c,x = sympy.symbols('a b c x')
eqt = sympy.Eq(c**2-b,100)
print(helpers.miscs.Miscs.get_vars(eqt))
DBG()
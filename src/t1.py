from sage.all import *

var("c0, c1, c2, c3, x, y, z")


e1 = 4 * c2 + c0 == 0
e2 = 4 * c2 + c3 + c0 == 0
e3 = 4 * c2 + 2 * c3 + c0 == 0

print(solve([e1, e2, e3], [c0, c1, c2, c3]))

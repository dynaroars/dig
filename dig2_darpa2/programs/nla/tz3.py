import z3
x,y,z,n = z3.Ints("x y z n")

e1 = y*z - z3.Int("18")*x - z3.Int("12")*y + z3.Int("2")*z == z3.Int("6")
e2 =(z*z) - z3.Int("12")*y - z3.Int("6")*z == z3.Int("-12")
e3 = z3.Int("6")*n + z3.Int("6") == z

d1 =  z == z3.Int("6")*n + z3.Int("6")
d2 = y == z3.Int("3")*n*n + z3.Int("3")*n + z3.Int("1");
d3 = x == n*n*n

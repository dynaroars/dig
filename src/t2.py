

from z3 import *

n, p, m, a, t, s, n, k = Ints("n p m a t s n k")
zero = IntVal("0")
one = IntVal("1")

f = And(n - p <= zero,
        m <= IntVal("20"),
        m - n <= one,
        k - n <= IntVal("6"),
        a <= IntVal("10"),
        a - n <= zero,
        - t <= IntVal("-1"),
        - s <= IntVal("-1"),
        - n + t <= IntVal("2"),
        - m <= zero,
        - k <= IntVal("-2"),
        - a <= zero)


e1 = -p + t <= one
print(e1)
g1 = Implies(f, e1)
print(g1)
prove(Implies(f, e1))


def sqrt(n):
    assert(n >= 0)
    a = 0
    s = 1
    t = 1
    m = 2*a
    k = 2*t
    p = 2*n

    while 1:
        assert (t == 2*a + 1)
        assert (s == (a + 1)*(a + 1))
        assert (4*s == t*t + 2*t + 1)
        #vtrace1(a, n, t, s, m, k, p)
        assert -p + s <= 2

        if not (s <= n):
            break
        a = a+1
        t = t+2
        s = s+t
        m = 2*a
        k = 2*t
    return a


sqrt(1000)
sqrt(7)
sqrt(0)

from functools import reduce
from math import gcd


def check(X, n, b):
    for v in X:
        if v % n != b:
            raise RuntimeError(f'n={n} b={b} X={X}')


def found(X, n):
    b = X[0] % n
    print(f'n={n} b={b}')
    check(X, n, b)


def solve(X)->tuple:
    assert(X), X
    print(f'X={X}')
    Y = [X[0] - v for v in X]
    print('Y', Y)
    g = reduce(gcd, Y)
    print('g', g)
    found(X, g)


    
solve([4, 0, 8, 12, 16, 19])
# solve([6, 11, 16, 1, 21])

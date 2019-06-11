import z3
import pdb
trace = pdb.set_trace
q, y, r, x, a, b = z3.Ints('q y r x a b')


ps = [q*y + r - x == 0,
      a*y - b == 0,
      -a - q <= -1,
      -b + y <= 0,
      -b - y <= -2,
      a - x <= 0,
      -a - r <= -2,
      -x <= -1,
      a - r <= 0,
      -a <= -1,
      -r <= -1,
      a - b <= 0,
      -q <= 0,
      -r - y <= -2,
      r - x <= 0,
      -q - y <= -1,
      -b - r <= -2,
      -b - q <= -1,
      -r + y <= 0,
      -y <= -1,
      -a - b <= -2,
      b - x <= 0,
      q - x <= -1,
      -q - r <= -1,
      -b - x <= -2,
      -x - y <= -2,
      -a - x <= -2,
      -a - y <= -2,
      -x + y <= 0,
      -b <= -1,
      -r - x <= -2,
      b - r <= 0,
      -q - x <= -1]


def simplify(fs):
    assert fs, fs
    assert (z3.is_expr(f) for f in fs), fs

    simpl = z3.Tactic('ctx-solver-simplify')

    simplifies = simpl(z3.And(ps))
    simplifies = simplifies[0]
    assert len(simplifies) <= fs

    if len(simplifies) == len(fs):
        return fs

    fs_strs_d = {str(z3.simplify(f)): f for f in fs}
    simplifies_strs = [str(f) for f in simplifies]

    results, notdone = [], []
    for simplified in simplifies_strs:
        try:
            f = fs_strs_d[simplified]
            results.append(f)
            del fs_strs_d[simplified]
        except KeyError:
            notdone.append(simplified)

    assert not notdone, "not implemented, if this happens have to check individually"
    return results


results = simplify(ps)
trace()


print str(z3.simplify(b*-1 + y <= 0))

# {'-1*b + -1*x <= -2': -b - x <= -2, '-1*a + -1*y <= -2': -a - y <= -2, '-1*r + y <= 0': -r + y <= 0, '-1*b + -1*q <= -1': -b - q <= -1, 'x >= 1': -x <= -1, 'a + -1*b <= 0': a - b <= 0, 'b >= 1': -b <= -1, 'r + -1*x <= 0': r - x <= 0, '-1*a + -1*q <= -1': -a - q <= -1, 'a + -1*x <= 0': a - x <= 0, 'r >= 1': -r <= -1, '-1*a + -1*r <= -2': -a - r <= -2, 'b + -1*x <= 0': b - x <= 0, '-1*a + -1*x <= -2': -a - x <= -2, '-1*b + -1*r <= -2': -b - r <= -2, '-1*q + -1*x <= -1': -q - x <= -1, '-1*r + -1*y <= -2': -r - y <= -2, '-1*x + y <= 0': -x + y <= 0, 'a >= 1': -a <= -1, 'q + -1*x <= -1': q - x <= -1, '-1*a + -1*b <= -2': -a - b <= -2, '-1*r + -1*x <= -2': -r - x <= -2, 'a + -1*r <= 0': a - r <= 0, '-1*q + -1*y <= -1': -q - y <= -1, '-1*x + -1*y <= -2': -x - y <= -2, '-1*q + -1*r <= -1': -q - r <= -1, '-1*b + -1*y <= -2': -b - y <= -2, '-1*b + y <= 0': -b + y <= 0}


# (28, {'-1*b + -1*x <= -2': -b - x <= -2, '-1*r + y <= 0': -r + y <= 0, '-1*b + -1*q <= -1': -b - q <= -1, '-1*r + -1*x <= -2': -r - x <= -2, '-1*a + -1*y <= -2': -a - y <= -2, 'b >= 1': -b <= -1, 'r + -1*x <= 0': r - x <= 0, '-1*a + -1*q <= -1': -a - q <= -1, 'a + -1*x <= 0': a - x <= 0, 'r >= 1': -r <= -1, '-1*a + -1*r <= -2': -a - r <= -2, 'b + -1*x <= 0': b - x <= 0, '-1*a + -1*x <= -2': -a - x <= -2, '-1*b + -1*r <= -2': -b - r <= -2, '-1*q + -1*x <= -1': -q - x <= -1, '-1*r + -1*y <= -2': -r - y <= -2, '-1*x + y <= 0': -x + y <= 0, 'a >= 1': -a <= -1, 'q + -1*x <= -1': q - x <= -1, '-1*a + -1*b <= -2': -a - b <= -2, 'x >= 1': -x <= -1, 'a + -1*r <= 0': a - r <= 0, '-1*q + -1*y <= -1': -q - y <= -1, '-1*x + -1*y <= -2': -x - y <= -2, '-1*q + -1*r <= -1': -q - r <= -1, 'a + -1*b <= 0': a - b <= 0, '-1*b + y <= 0': -b + y <= 0, '-1*b + -1*y <= -2': -b - y <= -2})

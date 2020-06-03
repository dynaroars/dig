import operator
import helpers.miscs

import sage.all


sage.all.var('x y z s t u')
vs = [x, y]

print(vs, len(vs))


def f1(vs):
    terms = helpers.miscs.Miscs.get_terms_fixed_coefs(vs, 2, 1)
    print(helpers.miscs.Miscs.get_terms_fixed_coefs(
        vs, 2, 1, do_create_terms=False))
    return terms


ts1 = f1(vs)
print(sorted(ts1), len(ts1))


def f2(vs):
    terms = helpers.miscs.Miscs.get_terms(vs, 2)
    terms = [t for t in terms if t != 1]
    return helpers.miscs.Miscs.get_terms_fixed_coefs(terms, 2, 1)


ts2 = f2(vs)
print(ts2, len(ts2))


def f3(vs):
    assert isinstance(vs, list) and vs

    terms = helpers.miscs.Miscs.get_terms(vs, 2)
    terms = [t for t in terms if t != 1]
    print(terms)

    terms_l = []
    terms_nl = []
    for t in terms:
        if (t.operator() == operator.pow or t.operator()
                == sage.symbolic.operators.mul_vararg):
            terms_nl.append(t)
        else:
            terms_l.append(t)

    print(terms_l)
    print(terms_nl)

    terms_l = helpers.miscs.Miscs.get_terms_fixed_coefs(terms_l, 2, 1)
    terms_nl1 = helpers.miscs.Miscs.get_terms_fixed_coefs(
        terms_nl, 2, 1, do_create_terms=False)

    print(terms_l, len(terms_l))
    print(terms_nl1, len(terms_nl1))

    rs = set()
    for rs_ in terms_nl1:
        rs_ = sum(operator.mul(*tc) for tc in rs_)
        rs.add(rs_)

    print('boo', rs, len(rs))

    terms_nl2 = helpers.miscs.Miscs.get_terms_fixed_coefs(
        terms_nl, 2, 1)

    print('bah', terms_nl2, len(terms_nl2))
    print(rs == terms_nl2)

    myresults = set()
    for rs_ in terms_nl1:
        assert rs_
        print('hi', rs_)
        rs__ = [set(t.variables()) for t, _ in rs_]
        print('ba', rs__)
        if len(rs_) >= 2 and set.intersection(*rs__):
            print('remove', rs__)
        else:
            myresults.add(sum(operator.mul(*tc) for tc in rs_))

    print(myresults, len(myresults))
    return []


print('GH')
ts3 = f3(vs)
print(ts3, len(ts3))


def f4(vs):
    assert isinstance(vs, list) and vs
    print('ho', len(helpers.miscs.Miscs.get_terms_fixed_coefs(vs, 2, 1)))
    terms = helpers.miscs.Miscs.get_terms(vs, 2)
    terms = [t for t in terms if t != 1]
    print('hi', len(helpers.miscs.Miscs.get_terms_fixed_coefs(terms, 2, 1)))
    terms = helpers.miscs.Miscs.get_terms_fixed_coefs(
        terms, 2, 1, do_create_terms=False)

    myresults = set()
    for rs_ in terms:
        assert rs_
        rs__ = [set(t.variables()) for t, _ in rs_]
        if len(rs_) <= 1 or not set.intersection(*rs__):
            myresults.add(sum(operator.mul(*tc) for tc in rs_))

    return myresults


print('HG')
ts4 = f4([x, y])
print(ts4, len(ts4))

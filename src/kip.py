import z3

import prover.kip

prover.kip.example()


# def cohendiv():
#     #TODO: LI0_d
#     from invs_nla_dig import q, x, r, y, a, b, cohendiv_LI0, cohendiv_LI1

#     # inner loop
#     I = z3.And(x == r+q*y, r >= y,  # invs of outer loop & guard of outer loop
#                a == 1, b == y)

#     T = z3.And(pre_f(r >= 2*b),
#                a == 2*pre_f(a),
#                b == 2*pre_f(b),
#                r == pre_f(r),
#                y == pre_f(y),
#                x == pre_f(x),
#                q == pre_f(q))

#     LI1 = cohendiv_LI1
#     LI1_d = verify("cohendiv LI1", [], I, T, LI1)

#     T = And(pre_f(a*y == b),  # invs of inner loop
#             pre_f(q*y+r == x),
#             pre_f(Not(r >= 2*b)),  #guard of inner loop
#             x == pre_f(x),
#             y == pre_f(y),
#             q == pre_f(q + a),
#             r == pre_f(r - b),
#             a == pre_f(a),
#             b == pre_f(b))

#     LI0 = cohendiv_LI0
#     LI0_d = verify("cohendiv LI0",[],I,T, LI0)

#     print_summary([LI0_d,LI1_d])


# cohendiv()

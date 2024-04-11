from sage.all import *

import functools
from collections import Counter
from itertools import combinations
import pdb

DBG = pdb.set_trace


def is_constant(ls):
    # if len(ls) < 2:
    #     return True
    # x = ls[0]
    # return len(list(filter(lambda a: a != x, ls))) == 0
    return len(ls) < 2 or len(set(ls)) == 1


def remove_duplicates(ls1, ls2):
    assert len(ls1) == len(ls2)

    print(ls1)
    print(ls2)
    list1 = []
    list2 = []
    size = len(ls1)
    for i in range(size):
        if not ls1[i] in list1:
            list1.append(ls1[i])
            list2.append(ls2[i])
    print(list1)
    print(list2)
    DBG()
    return list1, list2


def raise_consts(consts, degree):
    ls = []
    for i in range(degree):
        ls.append(list(map(lambda x: x**(i+1), consts)))
    return ls


def remove_trailing_zeros(ls):
    count = len(ls)
    for i in range(1, len(ls)):
        if(ls[(-1)*i] != 0):
            count = i
            break
    return ls[0:len(ls)-count+1]


def get_deg(ls, consts):
    size = len(ls)
    count = -1
    while count > (-1)*size:
        if ls[count] == 0:
            count -= 1
        else:
            break
    curr_deg = size+count
    if len(consts) == 0:
        return curr_deg
    ls_without_trail_zeros = ls[0:curr_deg+1]
    for i in range(len(consts)):
        for j in range(len(ls_without_trail_zeros)):
            const_degree = i+1
            coeff_degree = j
            if ls_without_trail_zeros[j] != 0:
                temp = list(
                    map(lambda x: ls_without_trail_zeros[j] % x, consts[i]))
                if 0 in temp:
                    if const_degree+coeff_degree > curr_deg:
                        curr_deg = const_degree+coeff_degree
    return curr_deg


def divided_diff(trace1, trace2):
    ls1, ls2 = remove_duplicates(trace1, trace2)
    ls2, ls1 = remove_duplicates(ls2, ls1)
    if len(ls1) < 2:
        return None
    temp = []
    coeffs = [ls2[0]]
    size = len(ls2)
    diff = 1
    while size > 1:
        for i in range(len(ls2)-1):
            if ls2[i+1] == ls2[i]:
                temp.append(0)
            else:
                temp.append((ls2[i+1]-ls2[i])/(ls1[i+diff]-ls1[i]))
        coeffs.append(temp[0])
        size = len(temp)
        ls2 = temp.copy()
        temp = []
        diff += 1
    return coeffs


def create_composite(ls, degree, input):
    vars = ls[0]
    const_vars = input
    traces = ls[1:]
    variables = [i for i in vars if i not in const_vars]
    composite_vars = []
    composite_traces = []
    comb = []
    for i in range(1, degree):
        comb = comb + list(combinations(variables, i+1)) + \
            list(combinations(const_vars, i+1))
    # if degree>=2:
    #     for c in vars:
    #         for i in range(degree):
    #             comb.append(tuple(c*(i+1)))
    for c in vars:
        comb.append(tuple(c))
    # print(comb)
    for tup in comb:
        var = functools.reduce(lambda a, b: a+b, tup)
        # print(var)
        composite_vars.append((var, len(tup)))
        # the traces must have same length. So, we create a list with all ones same length as a trace length
        temp_list = [1]*len(traces[0])
        for j in tup:
            trace = traces[vars.index(j)]
            temp_list = list(map(lambda x, y: x*y, temp_list, trace))
        composite_traces.append(temp_list)
    return list([composite_vars] + composite_traces)


def valid_fraction(ls):
    for i in ls:
        if i != 0 and (abs(i.numerator()) > 9999999 or abs(i.denominator()) > 9999999):
            return False
    return True


def is_valid_pair(var1, var2, consts):
    str_var1 = var1[0]
    str_var2 = var2[0]
    for i in consts:
        str_var1 = str_var1.replace(i[0], "")
        str_var2 = str_var2.replace(i[0], "")
    str = set(str_var1) & set(str_var2)
    for i in str:
        str_var1 = str_var1.replace(i, "")
        str_var2 = str_var2.replace(i, "")
    if str_var1 != var1[0] or str_var2 != var2[0]:
        # if len(str_var1) == 0 or len(str_var2) == 0:
        return False
    return True


def multi_trace_max_deg(args):
    R = PolynomialRing(QQ, 'x')
    num_traces = len(args)
    num_vars = len(args[0][0])
    degs = []
    for i in range(num_vars-1):
        for j in range(i+1, num_vars):
            all_coeffs_consts = []
            for k in range(num_traces):
                single_trace = args[k]
                vars = single_trace[0]
                vars_changing = []
                traces = single_trace[1:]
                traces_changing = []
                const_vars = []
                const_vals = []
                for m in range(num_vars):
                    if is_constant(traces[m]):
                        const_vars.append(vars[m])
                        const_vals.append(traces[m][0])
                    else:
                        vars_changing.append(vars[m])
                        traces_changing.append(traces[m])
                if (not vars[i] in const_vars and not vars[j] in const_vars and is_valid_pair(vars[i], vars[j], const_vars)):
                    (a, b) = remove_duplicates(traces[i], traces[j])
                    pairs = list(map(lambda x, y: (x, y), a, b))
                    func = R.lagrange_polynomial(pairs)
                    coeffs = func.coefficients()
                    degree = func.degree()
                    # print(vars[i], vars[j], pairs, degree)
                    while(len(coeffs) < degree+1):
                        coeffs = [0] + coeffs
                    if len(coeffs) < len(pairs):
                        all_coeffs_consts.append(
                            (remove_trailing_zeros(coeffs), const_vals, const_vars))
                        var_composite_deg = max(
                            vars[j][1], (vars[i][1])*degree)
                        degs.append(var_composite_deg)
                        # print(func)
                        # print("L1:",var_composite_deg,degs,vars[i], vars[j],const_vars,(vars[i][1])*degree,vars[j][1])
                    else:
                        (b, a) = remove_duplicates(traces[j], traces[i])
                        pairs = list(map(lambda x, y: (y, x), a, b))
                        func = R.lagrange_polynomial(pairs)
                        coeffs = func.coefficients()
                        degree = func.degree()
                        while (len(coeffs) < degree + 1):
                            coeffs = [0] + coeffs
                        if len(coeffs) < len(pairs):
                            all_coeffs_consts.append(
                                (remove_trailing_zeros(coeffs), const_vals, const_vars))
                            var_composite_deg = max(
                                (vars[j][1])*degree, vars[i][1])
                            degs.append(var_composite_deg)
                            # print(func)
                            # print("L2:",var_composite_deg,degs,vars[i], vars[j],const_vars)
            if len(all_coeffs_consts) > 0:
                coeff_traces = []
                const_traces = []
                const_vars_in_all = all_coeffs_consts[0][2]
                size_traces = len(all_coeffs_consts[0][0])
                size_consts = len(all_coeffs_consts[0][1])
                # print("size traces", size_traces)
                # print("all co co", all_coeffs_consts)
                for n in range(size_traces):
                    # print("n",n)
                    coeff_traces.append(
                        list(map(lambda x: x[0][n], all_coeffs_consts)))
                for n in range(size_consts):
                    const_traces.append(
                        list(map(lambda x: x[1][n], all_coeffs_consts)))
                # print('coeff traces',coeff_traces)
                # print('const traces', const_traces)
                for n in range(len(coeff_traces)):
                    for p in range(len(const_traces)):
                        (a, b) = remove_duplicates(
                            const_traces[p], coeff_traces[n])
                        pairs = list(map(lambda x, y: (x, y), a, b))
                        func = R.lagrange_polynomial(pairs)
                        degree_cons = func.degree()
                        coeffs_re = func.coefficients()
                        const_composite_deg = const_vars_in_all[p][1] * \
                            degree_cons
                    # print("pairs", pairs, degree_cons, const_vars_in_all[p])
                        if func.constant_coefficient() == 0:
                            coeffs_re = [0]+coeffs_re
                        if degree_cons < len(pairs) and degree_cons > 0:
                            #             print("pairs", pairs, degree_cons, const_vars_in_all[p])
                            #             print("cons com", const_vars_in_all[p])
                            #             print("const composite deg", const_composite_deg)
                            #             print("hhghgg",n+degree_cons+const_composite_deg-1)
                            degs.append(n+const_composite_deg)
                            # print("L3:",n+const_composite_deg,degs)
                # print("d",degs)
    if len(degs) > 0:
        return max(degs)
    else:
        return None


def max_deg(traces_as_dict, input, degree_of_composite):
    traces_list = []
    inputs = input
    vars = list(traces_as_dict.keys())
    traces = list(map(lambda x: traces_as_dict[x], vars))
    input_indexes = list(map(lambda x: vars.index(x), inputs))
    input_traces = list(map(lambda x: traces[x], input_indexes))
    max_degs = []
    size = len(input_traces[0])
    counter = 0
    begin_index = 0
    curr_input_vals = list(map(lambda x: x[counter], input_traces))
    while True:
        is_same_index = functools.reduce(lambda x, y: x and y, list(
            map(lambda x, y: x == y[counter], curr_input_vals, input_traces)))
        if is_same_index:
            counter += 1
        if not is_same_index or counter == size:
            arg = []
            arg.append(vars)
            trace_lists = list(map(lambda x: x[begin_index:counter], traces))
            for i in trace_lists:
                arg.append(i)
            traces_list.append(create_composite(
                arg, degree_of_composite, input))
            # max_degs.append(single_trace_max_deg(*arg))
            if counter == size:
                break
            begin_index = counter
            curr_input_vals = list(map(lambda x: x[counter], input_traces))
    # print(traces_list)
    # return Counter(max_degs).most_common(1)[0][0]
    print(traces_list)
    return multi_trace_max_deg(traces_list)


def get_max_deg(traces_as_dict, input):
    x = max_deg(traces_as_dict, input, 1)
    if x != None:
        return x
    x = max_deg(traces_as_dict, input, 2)
    if x != None:
        return x
    x = max_deg(traces_as_dict, input, 3)
    if x != None:
        return x
    return None


def test():
    d = {'x': [1, 2, 3, 4, 5],
         'y': [2, 4, 5, 68, 10],
         'z': [10, 10, 10, 10, 10]}

    print(get_max_deg(d, ['x', 'y']))


def test_bresenham():

    X1 = [15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15]
    Y1 = [33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33]
    x1 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
    y1 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
    v1 = [51, 87, 123, 159, 195, 231, 267, 303, 339,
          375, 411, 447, 483, 519, 555, 591, 627]

    X2 = [11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11]
    Y2 = [27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27]
    x2 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
    y2 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
    v2 = [43, 75, 107, 139, 171, 203, 235, 267, 299, 331, 363, 395, 427]

    d = {'X': X1 + X2,
         'Y': Y1 + Y2,
         'x': x1 + x2,
         'y': y1 + y2,
         'v': v1 + v2}

    print(get_max_deg(d, ['X', 'Y']))


test_bresenham()

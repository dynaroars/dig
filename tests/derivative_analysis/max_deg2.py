import functools
from collections import Counter

def is_constant(ls):
    if len(ls)<2:
        return True
    x = ls[0]
    return len(list(filter(lambda a: a != x, ls))) == 0


def remove_duplicates(ls1, ls2):
    list1 = []
    list2 = []
    size = len(ls1)
    for i in range(size):
        if not ls1[i] in list1:
            list1.append(ls1[i])
            list2.append(ls2[i])
    return list1, list2


def raise_consts(consts, degree):
    ls = []
    for i in range(degree):
        ls.append(list(map(lambda x: x**(i+1), consts)))
    return ls

def remove_trailing_zeros(ls):
    count = len(ls)
    for i in range(1,len(ls)):
        if(ls[(-1)*i] != 0):
            count = i
            break
    return ls[0:len(ls)-count+1]


def get_deg(ls, consts):
    size = len(ls)
    count = -1
    while count>(-1)*size:
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
                temp = list(map(lambda x: ls_without_trail_zeros[j]%x, consts[i]))
                if 0 in temp:
                    if const_degree+coeff_degree>curr_deg:
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
    while size>1:
        for i in range(len(ls2)-1):
            if ls2[i+1] == ls2[i]:
                temp.append(0)
            else:
                temp.append( (ls2[i+1]-ls2[i])/(ls1[i+diff]-ls1[i]))
        coeffs.append(temp[0])
        size = len(temp)
        ls2 = temp.copy()
        temp = []
        diff += 1
    return coeffs


def single_trace_max_deg(*args):
    print(args)
    vars = args[0]
    vars_changing = []
    traces = args[1:]
    traces_changing = []
    consts = []
    degs = []
    num_vars = len(vars)
    for i in range(num_vars):
        if is_constant(traces[i]):
            consts.append(traces[i][0])
        else:
            vars_changing.append(vars[i])
            traces_changing.append(traces[i])
    consts_raised = []
    if len(consts) > 0:
        consts_raised = raise_consts(list(filter(lambda x: x != 1, consts)), 5)
    num_vars_changing = len(vars_changing)
    if num_vars_changing == 0:
        return 0
    for i in range(num_vars_changing-1):
        for j in range(i+1, num_vars_changing):
            coeffs = divided_diff(traces_changing[i], traces_changing[j])
            if coeffs != None and coeffs[-1] == 0:
                degs.append(get_deg(coeffs,consts_raised))
            else:
                coeffs = divided_diff(traces_changing[j], traces_changing[i])
                if coeffs != None and coeffs[-1] == 0:
                    degs.append(get_deg(coeffs, consts_raised))
    if len(degs) == 0:
        return None
    else:
        return max(degs)


def multi_trace_max_deg(args):
    num_traces = len(args)
    num_vars = len(args[0][0])
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
                if (not vars[i] in const_vars and not vars[j] in const_vars):
                    coeffs = divided_diff(traces[i], traces[j])
                    if coeffs != None and coeffs[-1] == 0:
                        all_coeffs_consts.append((remove_trailing_zeros(coeffs), const_vals))
                    else:
                        coeffs = divided_diff(traces[j], traces[i])
                        if coeffs != None and coeffs[-1] == 0:
                            all_coeffs_consts.append((remove_trailing_zeros(coeffs), const_vals))
            if len(all_coeffs_consts) >0:
                degs = []
                coeff_traces = []
                const_traces = []
                # print(all_coeffs_consts)
                size_traces = len(all_coeffs_consts[0][0])
                size_consts = len(all_coeffs_consts[0][1])
                for n in range(size_traces):
                    coeff_traces.append(list( map(lambda x: x[0][n], all_coeffs_consts)))
                for n in range(size_consts):
                    const_traces.append(list( map(lambda x: x[1][n], all_coeffs_consts)))
                for n in range(len(coeff_traces)):
                    for p in range(len(const_traces)):
                        coeffs_re = divided_diff(const_traces[p], coeff_traces[n])
                        if coeffs_re != None and coeffs_re[-1] == 0:
                            degs.append(n+len(remove_trailing_zeros(coeffs_re))-1)
                print(all_coeffs_consts)
                print(coeff_traces)
                print(const_traces)
                print(degs)




def max_deg(traces_as_dict, input):
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
        is_same_index = functools.reduce(lambda x,y: x and y, list(map(lambda x,y: x==y[counter], curr_input_vals, input_traces)))
        if is_same_index:
            counter+=1
        if not is_same_index or counter == size:
            arg = []
            arg.append(vars)
            trace_lists = list(map(lambda x: x[begin_index:counter], traces))
            for i in trace_lists:
                arg.append(i)
            traces_list.append(arg)
            max_degs.append(single_trace_max_deg(*arg))
            if counter == size:
                break
            begin_index = counter
            curr_input_vals = list(map(lambda x: x[counter], input_traces))
    #print(traces_list)
    return Counter(max_degs).most_common(1)[0][0]


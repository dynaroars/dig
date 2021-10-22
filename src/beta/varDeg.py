import itertools


def isFunction(traces):
    for i in traces:
        if traces.count(i) > 1:
            return False
    return True


def varDeg(*args):
    if len(args) < 2:
        print("wrong input. Not enough arguments")
        return
    varNames = args[0]
    lenArgs = len(args)
    varTraces = args[1:]
    printTraces = False

    if(args[lenArgs-1] == 'p'):
        varTraces = args[1:lenArgs-1]
        printTraces = True
    if len(varNames) != len(varTraces):
        print("wrong input. Traces and variable names don't match")
        return
    traceLength = len(varTraces[0])
    coeffs = dict()
    for i in range(len(varNames)-1):
        for j in range(i+1, len(varNames)):
            # print("{}, {}".format(varNames[i], varNames[j]))
            valueList = dividedDiff(
                varTraces[i], varTraces[j], varNames[i], varNames[j], printTraces)
            print('res', varNames[i], varNames[j], valueList)
            if valueList != None and valueList[len(valueList)-1] == 0:
                coeffs[(varNames[i], varNames[j])] = valueList
            else:
                try:
                    valueList = dividedDiff(
                        varTraces[j], varTraces[i], varNames[j], varNames[i], printTraces)
                    if valueList != None and valueList[len(valueList)-1] == 0:
                        coeffs[varNames[j], varNames[i]] = valueList
                    # print("boo")
                except ZeroDivisionError:
                    print("Zero division error", varTraces[j])

    # print('mycoeffs', coeffs)
    for tuple in coeffs:
        coeffList = coeffs[tuple]
        depVar = tuple[1]
        indepVar = tuple[0]
        indepVarList = varTraces[varNames.index(indepVar)]
        eqn = depVar + ' = '
        lastTerm = ''
        for i in range(len(coeffList)):
            if i == 0 or coeffList[i] != 0:
                if i >= 1:
                    lastTerm = lastTerm + \
                        '('+indepVar + ' - ' + str(indepVarList[i-1])+')'
                if i == 0:
                    eqn += str(coeffList[i])
                else:
                    eqn += '+('+str(coeffList[i])+')*'+lastTerm
        # print(eqn)


def makeFunc(list1, list2):
    newlist1 = []
    newlist2 = []
    length = len(list1)
    i = 0
    while i < length:
        while i+1 < length and list1[i+1] == list1[i]:
            print('skip', i, list1[i])
            i += 1
        newlist1.append(list1[i])
        newlist2.append(list2[i])
        i += 1
    return (newlist1, newlist2)


def dividedDiff(trace1, trace2, varName1, varName2, printTraces):
    print('diff {} {}'.format(varName1, varName2))
    if trace2 == []:
        return None
    if not isFunction(trace1):
        print('gh')
        (list1, list2) = makeFunc(trace1, trace2)
        print('blist1', list1, trace1)
        print('blist2', list2, trace2)
        if len(list1) == 0 or len(list1) == len(trace1):
            print('hi')
            return None
    else:
        list1 = trace1.copy()
        list2 = trace2.copy()
    derivativeTraces = [{varName1: trace1.copy()}, {varName2: trace2.copy()}]
    tempList = []
    coeffs = [list2[0]]
    diff = 1
    size = len(list2)
    maxdeg = None
    # print(list1, list2)
    while size > 1:
        # print('new iter')
        #print('list1', list1, 'list2', list2)
        for i in range(len(list2)-1):
            # print('list1', diff, 'here', list1[i+diff],
            # list1[i], list1[i+diff] - list1[i])
            # print('list2', 1, 'here', list2[i+1],
            # list2[i], list2[i+1]-list2[i])
            vv = (list2[i+1]-list2[i])/(list1[i+diff]-list1[i])
            # print(vv)
            tempList.append(vv)
        # print('tmpList', tempList)
        if maxdeg is None and all(x == 0 for x in tempList):
            maxdeg = diff-1
            print('maxdeg {} {} = {}'.format(varName1, varName2, maxdeg))

        coeffs.append(tempList[0])
        # print('coefs', coeffs)
        size = len(tempList)
        list2 = tempList.copy()
        derivativeTraces.append(tempList.copy())
        tempList = []
        diff += 1
    if printTraces:
        print(derivativeTraces)
    # print('mycoefs', coeffs)
    return coeffs


def test(r):
    # xs = list(range(1, r))
    # ys = [(x**2) for x in xs]
    # zs = [3*x + y for x, y in zip(xs, ys)]
    # print('xs', xs)
    # print('ys', ys)
    # print('zs', zs)
    # varDeg(['x', 'y', 'z'],  xs, ys, zs)
    #ys = list(range(-3, 3))
    #xs = [y**2 for y in ys]
    #maxdeg = vu1({'ys': ys, 'xs': xs})
    #maxdeg = vu(xs, ys)
    #print('vu maxdeg', maxdeg)

    # xs = [-2, -1, 0, 1, 2, 3, 4, 5, 7, -4]
    # ys = [3, 1, 0, -7, -12, 3, 4, 1, 2, 4]
    # zs = [-6, -1, 0, -7, -24, 9, 16, 5, 14, -16]
    # _ = varDeg(['x', 'y', 'z'], xs, ys, zs)

    xs = [-2, 1, 3, 2, 8, 10]
    ys = [3, 2, -12, 11, 8, 4]
    zs = [1, 3, -9, 13, 16, 14]
    _ = varDeg(['x', 'y', 'z'], xs, ys, zs)


def vu1(ds):
    maxdeg = 0
    pairs = itertools.combinations(ds.keys(), 2)
    for x, y in pairs:
        maxdeg_ = vu(ds[x], ds[y])
        if maxdeg_ > maxdeg:
            #print(x, y, maxdeg_)
            maxdeg = maxdeg_
        else:
            maxdeg_ = vu(ds[y], ds[x])
            if maxdeg_ > maxdeg:
                #print(y, x, maxdeg_)
                maxdeg = maxdeg_
    return maxdeg


def vu(xs, ys):
    assert len(xs), xs
    assert len(xs) == len(ys), (xs, ys)

    ys_ = list(ys)
    i = 0
    while ys_:
        ys_change = [s-f for f, s in zip(ys_, ys_[1:])]
        if ys_ and all(y == 0 for y in ys_):
            return i  # return max deg
        i = i + 1
        xs_change = [s-f for f, s in zip(xs, xs[i:])]
        ys_ = [y/x for x, y in zip(xs_change, ys_change)]
    return -1

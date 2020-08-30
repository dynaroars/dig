def isFunction(traces):
    for i in traces:
        if traces.count(i) > 1:
            return False
    return True


def varDeg(*args):
    if len(args)<2:
        return "wrong input. Not enough arguments"
    varNames = args[0]
    lenArgs = len(args)
    varTraces = args[1:]
    printTraces =False
    if(args[lenArgs-1]=='p'):
        varTraces = args[1:lenArgs-1]
        printTraces = True
    if len(varNames) != len(varTraces):
        return "wrong input. Traces and variable names don't match"
    traceLength = len(varTraces[0])
    coeffs = dict()
    for i in range(len(varNames)-1):
        for j in range(i+1, len(varNames)):
            valueList = dividedDiff(varTraces[i], varTraces[j], varNames[i], varNames[j], printTraces)
            if valueList != None and valueList[len(valueList)-1] == 0:
                coeffs[(varNames[i], varNames[j])] = valueList
            else:
                try:
                    valueList = dividedDiff(varTraces[j], varTraces[i], varNames[j], varNames[i], printTraces)
                    if valueList != None and valueList[len(valueList)-1] == 0:
                        coeffs[varNames[j], varNames[i]] = valueList
                except ZeroDivisionError:
                    print("Zero division error", varTraces[j])

    #print(coeffs)
    for tuple in coeffs:
        coeffList = coeffs[tuple]
        depVar = tuple[1]
        indepVar = tuple[0]
        indepVarList = varTraces[varNames.index(indepVar)]
        eqn = depVar + ' = '
        lastTerm = ''
        for i in range(len(coeffList)):
            if i == 0 or coeffList[i] != 0:
                if i>=1:
                    lastTerm = lastTerm + '('+indepVar + ' - ' + str(indepVarList[i-1])+')'
                if i == 0:
                    eqn += str(coeffList[i])
                else:
                    eqn += '+('+str(coeffList[i])+')*'+lastTerm
        print(eqn)

def makeFunc(list1, list2):
    newlist1 = []
    newlist2 = []
    length = len(list1)
    i = 0
    while i<length:
        while i+1 < length and list1[i+1] == list1[i]:
            i+=1
        newlist1.append(list1[i])
        newlist2.append(list2[i])
        i+=1
    return (newlist1, newlist2)




def dividedDiff(trace1, trace2, varName1, varName2, printTraces):
    if trace2 == []:
        return None
    if not isFunction(trace1):
        (list1, list2) = makeFunc(trace1, trace2)
        if len(list1) == 0 or len(list1) == len(trace1):
            return None
    else:
        list1 = trace1.copy()
        list2 = trace2.copy()
    derivativeTraces = [{varName1: trace1.copy()}, {varName2:trace2.copy()}]
    tempList = []
    coeffs = [list2[0]]
    diff = 1
    size = len(list2)
    while size>1:
        for i in range(len(list2)-1):
            tempList.append( (list2[i+1]-list2[i])/(list1[i+diff]-list1[i]))
        coeffs.append(tempList[0])
        size = len(tempList)
        list2 = tempList.copy()
        derivativeTraces.append(tempList.copy())
        tempList = []
        diff += 1
    if printTraces:
        print(derivativeTraces)
    return coeffs

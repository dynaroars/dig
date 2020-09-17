from copy import deepcopy

import numpy as np
from z3 import *
import array

nestings = []

class NestArray:
    def genNesting(self, lstTrace, l, r):
        if l == r:
            nestings.insert(len(nestings), deepcopy(lstTrace))
        else:
            for i in range(l, r + 1):
                lstTrace[l], lstTrace[i] = lstTrace[i], lstTrace[l]
                self.genNesting(lstTrace, l + 1, r)
                lstTrace[l], lstTrace[i] = lstTrace[i], lstTrace[l]

    def reachAnalysisTopLevel(self, n, proposedVariance, trace, frequencyTrace):
        pivot = proposedVariance[0]
        outerMost = proposedVariance[1]
        result = []
        for value in frequencyTrace[pivot]:
            if value not in frequencyTrace[outerMost]:
                return []
            all_index = []
            for index in frequencyTrace[outerMost][value]:
                all_index += self.reachAnalysisPerLevel(proposedVariance, trace, frequencyTrace, 2, index)
            if len(all_index) == 0:
                return []
            result.append([frequencyTrace[pivot][value], all_index])
        return result

    def reachAnalysisPerLevel(self, proposedVariance, trace, frequencyTrace, level, value):
        if value not in frequencyTrace[proposedVariance[level]]:
            return []
        if level == len(proposedVariance) - 1:
            return frequencyTrace[proposedVariance[level]][value]
        arr = proposedVariance[level]
        available_index = []
        for j in frequencyTrace[arr][value]:
            available_index += self.reachAnalysisPerLevel(proposedVariance, trace, frequencyTrace, level + 1, j)
        return available_index

    def preprocess(self, trace):
        allDicts = []
        for arr in trace:
            dictArray = {}
            for i in range(len(arr)):
                if arr[i] in dictArray:
                    dictArray[arr[i]].append(i)
                else:
                    dictArray[arr[i]] = [i]
            allDicts.append(dictArray)
        return allDicts

    def z3_solver(self, inps):
        s = Solver()
        p = Int('p')
        q = Int('q')
        for set in inps:
            for i in set[0]:
                condition = []
                for j in set[1]:
                    condition += [j == i*p + q]
                s.add(And(Or(condition)))
        print("s: ", s)
        if s.check() == sat:
            print(s.model())
        else:
            print("Cannot solve")
        #solve(s)

    def start(self, trace):
        variable = range(len(trace))
        nestedArray.genNesting(list(variable), 0, len(variable) - 1)
        allDict = nestedArray.preprocess(trace)
        for nesting in nestings:
            inps = nestedArray.reachAnalysisTopLevel(len(nesting), nesting, trace, allDict)
            if len(inps) == 0:
                print("Reach analysis fails")
            else:
                nestedArray.z3_solver(inps)



nestedArray = NestArray()

#trace = [[7, 1, -3], [1, -3, 5, 1, 0, 7, 1], [8, 5, 6, 6, 2, 1, 4], [0, 1, 3, 5]]
trace = [[7, 1, -3], [1, -3, 5, 1, 0, 7, 1], [8, 5, 6, 6, 2, 1, 4]]
nestedArray.start(trace)

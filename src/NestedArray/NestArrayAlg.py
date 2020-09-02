
import numpy as np

class NestArray:
    nesting = np.array([])

    def genNesting(self, lstTrace, l, r):
        if l == r:
            tempNest = np.array(lstTrace)
            ele = ""
            for c in lstTrace:
                ele += c
            self.nesting = np.append(self.nesting, ele)
        else:
            for i in range(l, r + 1):
                lstTrace[l], lstTrace[i] = lstTrace[i], lstTrace[l]
                self.genNesting(lstTrace, l + 1, r)
                lstTrace[l], lstTrace[i] = lstTrace[i], lstTrace[l]

    def printNesting(self):
        print(self.nesting)
        print(len(self.nesting))


nestedArray = NestArray()
variable = "ABCDE"
nestedArray.genNesting(list(variable), 0, 4)
nestedArray.printNesting()
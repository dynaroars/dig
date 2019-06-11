import vu_common as CM
import random
def guessupper(myvar, minv, maxv):
    print 'enter', minv,maxv
    if minv == maxv:
        return maxv
    elif maxv-minv == 1:
        if not isinstance(check(minv, myvar),dict):
            return minv
        else:
            return maxv
        
    v = ceil((maxv - minv)/2.0) + minv
    stat = check(v, myvar)
    if isinstance(stat, dict): #cex
        minv = stat[myvar]
        print 'cex', minv
    else:
        maxv = v
        print 'checked'

    return guessupper(myvar, minv, maxv)



def check(v, myvar):
    realv = 17
    print '... checking', v
    if v >= realv:
        return True
    else:
        vv = {myvar: random.randint(v+1, realv)} # v+1 to (including) realv
        return vv
        

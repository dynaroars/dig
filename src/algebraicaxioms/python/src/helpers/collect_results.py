import numpy
from collections import OrderedDict
import vcommon as CM
median = lambda l: numpy.median(numpy.array(l))
mean = lambda l: numpy.mean(numpy.array(l))
def doit(logfile="/home/tnguyen//Dropbox/git/symtraces/logMay8b_2017.log"):
    lines = [l for l in CM.iread(logfile) if "locs" in l and "time" in l]
    
    
    rs = OrderedDict()
    for l in lines:
        name, nlocs, ninvs, ninps, ntime, nrand = l.split(',')
        name = name.split()[1].strip()
        nlocs = float(nlocs.split()[0].strip())
        ninvs = float(ninvs.split()[1].strip())
        ninps = float(ninps.split()[1].strip())
        ntime = float(ntime.split()[1].strip())
        
        print name, nlocs, ninvs, ninps, ntime
        if name not in rs:
            rs[name] = {'nlocs':[], 'ninvs': [], 'ninps': [], 'ntime': []}

        rs[name]['nlocs'].append(nlocs)
        rs[name]['ninvs'].append(ninvs)
        rs[name]['ninps'].append(ninps)
        rs[name]['ntime'].append(ntime)        


    nruns = max(len(rs[name]['nlocs']) for name in rs)
    
    stats = {}
    for name in rs:
        stats[name] = {}
        for key in rs[name]:
            contents = rs[name][key]
            if len(contents) < nruns:
                maxv = max(contents)
                maxv = maxv*100
                contents.extend([maxv]* (nruns-len(contents)))
                
            medianc = median(contents)
            meanc = mean(contents)
            lenc = len(contents)
            stats[name][key] = (medianc, meanc, lenc)

            print ('{} {} median {} mean {} len {}'
                   .format(name, key, medianc, meanc, lenc))

    for name in sorted(stats):
        invsd = stats[name]["ninvs"]
        timesd = stats[name]["ntime"]
        print name, invsd[0], timesd[0]

    return stats


if __name__ == "__main__":
    import argparse
    aparser = argparse.ArgumentParser("Collect DIG's results")
    ag = aparser.add_argument
    
    ag("inp", help="inp")
    args = aparser.parse_args()
    doit(args.inp)

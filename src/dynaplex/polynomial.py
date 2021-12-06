#!/usr/bin/env python3
'''Estimates complexity of iterative functions using techniques from DIG'''

from pathlib import Path
from os import path
import argparse
import random
import numpy
import math
import time
import settings
from sklearn.metrics import r2_score
import matplotlib.pyplot as plt

def read_traces(filename):
    ''' reads traces from a file. format "size;counter"'''
    sizes = []
    counters = []
    with open(filename) as file:
        lines = file.readlines()
    for line in lines:
        size, counter = line.split(';')
        sizes.append(int(size))
        counters.append(int(float(counter.strip())))

    return sizes, counters

def logs_regression(sizes, counters, nlog_flag=False):
    nlogs = [c*math.log(c, 2) if c is not 0 else 0 for c in sizes] #arbitrary make log(0,2) = 0
    logs = [math.log(c, 2) if c is not 0  else 0 for c in sizes] #arbitrary make log(0,2) = 0

    x_logs, y_logs = logs[:int((len(logs)+1)*.80)], counters[:int((len(counters)+1)*.80)]
    test_xlog, test_counters = logs[int((len(logs)+1)*.80):], counters[int((len(sizes)+1)*.80):]

    x_nlogs, y_nlogs = nlogs[:int((len(nlogs)+1)*.80)], counters[:int((len(counters)+1)*.80)]
    test_xnlog, test_counters = nlogs[int((len(nlogs)+1)*.80):], counters[int((len(sizes)+1)*.80):]

    nlog_model = numpy.poly1d(numpy.polyfit(x_nlogs, y_nlogs, 1))
    log_model = numpy.poly1d(numpy.polyfit(y_logs, y_logs, 1))

    nlog_r2 = r2_score(test_counters, nlog_model(test_xnlog))
    log_r2 = r2_score(test_counters, log_model(test_xlog))

    #print("log: {}, r2_score {}".format(log_model, log_r2))

    if (log_r2 < nlog_r2) and nlog_flag:
        #print("nlog: {}, r2_score {}".format(nlog_model, nlog_r2))
        if nlog_model[nlog_model.order] < (1.0/max(x_nlogs)) or math.isclose(nlog_r2, 0.0, rel_tol=0.01):
            return "nlog", -1, nlog_model
        else:
            return "nlog", nlog_r2, nlog_model

    elif log_r2 > nlog_r2 or not nlog_flag:
        if log_model[log_model.order] < (1.0/max(x_logs)) or math.isclose(log_r2, 0.0, rel_tol=0.01):
            return "log", -1, log_model
        else:
            return "log", log_r2, log_model
    return "log", -1, log_model

def func(x, a, b):
    return a *numpy.log(x) + b

def log_plot(model, sizes, log):
    l = [model[1]*s*math.log(s, 2)+ model[0] for s in sizes] if log=="nlog" else [model[1]*math.log(s, 2)+model[0] for s in sizes]
    return l

def poly_regression(sizes, counters, maxdeg, plotting=False, r=False, nlog_flag=False):
    assert(len(sizes)==len(counters)), "Invalid traces"
    assert(maxdeg>=1), "maxdeg<1"
    start_time = time.time()
    k = 0  #n^k(logn)^p
    p = 0
    if(len(set(counters)) == 1):
        complexity = "1"
        if not r:
            print("Analysis complete in {} seconds\nComplexity is O({})".format(time.time()-start_time, complexity))
        return complexity, k, p

    x, y = sizes[:int((len(sizes)+1)*.80)], counters[:int((len(sizes)+1)*.80)]
    test_sizes, test_counters = sizes[int((len(sizes)+1)*.80):], counters[int((len(sizes)+1)*.80):]
    maxsize = max(sizes)
    models = []
    r2_scores = []
    if plotting:
        plt.scatter(sizes, counters)
        myline = numpy.linspace(1, maxsize, maxsize)

    print("models before applying heuristics")
    for i in range(0, maxdeg+1):
        mymodel = numpy.poly1d(numpy.polyfit(sizes, counters, i))
        models.append(mymodel)
        print(mymodel)

    # if plotting:
    #     plt.plot(myline, mymodel(myline), c=(random.random(), random.random(), random.random()), label="{}-D polynomial".format(i))

    #discard models where the coe of the highest order is less than 1/maxinput
    tmp = models
    models = []
    for model in tmp:
        order = model.order
        high_order_coe = model[order]
        if not(high_order_coe < (1.0/maxsize)): #heuristics can be improved
            models.append(model)

    assert(len(models)>0), "Heuristics eliminated all candidate models"

    #Calculate r2_scores
    for model in models:
        r_square = r2_score(test_counters, model(test_sizes))
        r2_scores.append(r_square)

    print("Models after applying Heuristics ")
    for m in models:
        print(m)

    highest_r2 = max(r2_scores)
    index = r2_scores.index(highest_r2)

    logarithmic, score, log_model = logs_regression(sizes, counters, nlog_flag)

    if highest_r2 >= score and highest_r2 >= 0.0:
        complexity = "n^{}".format(models[index].order)
        k = models[index].order
        p = 0
        #assert(models[index][order] < math.pow(maxsize, models[index].order))
    else:
        complexity = "{} n".format(logarithmic)
        p = 1
        k = 1 if logarithmic == "nlog" else 0


    seconds = time.time()-start_time
    if not r:
        print("Analysis complete in {} seconds\nComplexity is O({})".format(seconds, complexity))
    else:
        print("Analysis complete in {} seconds".format(seconds))
    if plotting:
        #plt.plot(myline, l, c=(random.random(), random.random(), random.random()), label="{}".format(logarithmic))
        plt.xlabel('Input size')
        plt.ylabel('Instruction Counter', rotation=90)
        plt.legend(loc='upper left')
        plt.grid()
        #plt.title("Strassen")
        #plt.show()
        plt.savefig('fig.png')

    return complexity, k, p


if __name__ == '__main__':
    parser = argparse.ArgumentParser(prog="dig.py")
    parser.add_argument('-trace', help="path/to/traceFile")
    parser.add_argument('-maxdeg', help="maximum deg of polynomial")
    parser.add_argument('-plot', action='store_true', help="To display plots of polynomial regression")
    parser.add_argument('-r', action='store_true', help="recursive program")
    parser.add_argument('-nlog', action='store_true', help="Turn on n log regression")
    args = parser.parse_args()
    trace_file = Path(args.trace)
    assert(path.exists(trace_file)), "{} doesn't exist".format(trace_file)
    maxdeg = int(args.maxdeg)
    sizes, counters = read_traces(trace_file)
    complexity, k, p = poly_regression(sizes, counters, maxdeg, args.plot, args.r, settings.nlog)
    if(args.r):
        print("Polynomial relation: ", complexity)
        print("k={} p={}".format(k, p))

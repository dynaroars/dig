import os

path_to_src = os.path.dirname(os.path.abspath(__file__))
maxdeg = 5
plot = False
nlog = True #nlog and n are very close. We can turn off nlog if necessary
min_freq = 0.95 #this is the frequency used as heuristics to select between T(n-a) and T(n/a)

import os
import os.path
import time
from datetime import datetime

import helpers.vcommon as CM

import settings
settings.logger_level = CM.getLogLevel(3)

TIMEOUT = 600  # seconds
CMD = "timeout {} ".format(TIMEOUT) +\
    "sage -python -O dig.py {filename} -log 4 -octmaxv 20 -seed {seed}"


def run(benchdir, ntimes):
    benchdir = os.path.realpath(os.path.expanduser(benchdir))
    assert os.path.isdir(benchdir), benchdir

    print("**** Benchmark dir '{}' {} times ({})".format(
        benchdir, ntimes, datetime.now()))

    fs = sorted(f for f in os.listdir(benchdir) if f.endswith(".java"))
    fs = [os.path.join(benchdir, f) for f in fs]

    for f in fs:
        if not os.path.isfile(f):
            print "File {} does not exist".format(f)
            continue

        for i in range(ntimes):
            i_run_cmd = CMD.format(filename=f, seed=i)
            print "### {}: {}".format(
                time.strftime("%c"), i_run_cmd)

            os.system(i_run_cmd)


ntimes = 2

# NLA
dir_nla = "../tests/nla/"
dir_mp = "../tests/mp/"
run(dir_nla, ntimes)


# dirComplexity = "programs/complexity/gulwani_cav09"
# run(dirComplexity, ntimes)

# dirComplexity = "programs/complexity/gulwani_pldi09"
# run(dirComplexity, ntimes)

# dirComplexity = "programs/complexity/gulwani_popl09"
# run(dirComplexity, ntimes)


#dirHola = "programs/hola/"
#run(dirHola, ntimes)

#dirBm_oopsla = "programs/PIE/bm_oopsla/"
#run(dirBm_oopsla, ntimes)

#dirBm_ice = "programs/PIE/bm_ice/"
#run(dirBm_ice, ntimes)


# f=../results/nla_080219 ; rm -rf $f; python benchmark.py 2>&1 | tee $f

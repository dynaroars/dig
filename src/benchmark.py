import vcommon as CM
import os
import os.path
import time
from datetime import datetime
from vcommon import getLogLevel
import dig
import settings
settings.logger_level = getLogLevel(3)


def run(benchdir, ntimes):
    print("**** Benchmark dir '{}' {} times ({})".format(
        benchdir, ntimes, datetime.now()))

    fs = sorted(f for f in os.listdir(benchdir) if f.endswith(".java"))
    fs = [os.path.join(benchdir, f) for f in fs]

    for f in fs:
        if not os.path.isfile(f):
            print "File {} does not exist".format(f)
            continue

        #run_cmd = "sage -python -O dig.py {} -log 3 -octmaxv 20 -seed {} -nopreposts"
        for i in range(ntimes):
            print "##### Running {} with seed {}, {}".format(
                f, i, time.strftime("%c"))
            dig.run(f, seed=i, maxdeg=None,
                    do_eqts=True, do_ieqs=True, do_minmaxplus=True,
                    do_preposts=False,
                    do_rmtmp=True)


ntimes = 1

# NLA
dir_nla = "../tests/nla/"
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

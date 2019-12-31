#! /usr/bin/env python3

"""
Example: f=../results/nla_082619 ; rm -rf $f; python benchmark.py 2>&1 | tee $f
"""
from pathlib import Path
import pdb
import os
import time
from datetime import datetime

import helpers.vcommon as CM

import settings
settings.logger_level = CM.getLogLevel(3)

DBG = pdb.set_trace

TIMEOUT = 600  # seconds
CMD = "timeout {} ".format(TIMEOUT) +\
    "$SAGE/git/sage-8.9/sage -python -O " +\
    "dig.py {filename} -log 2 -octmaxv 20 -seed {seed} -maxdeg 1 -noieqs -nominmax"


def run(benchdir, ntimes):
    assert benchdir.is_dir(), benchdir

    print("# Benchmark dir '{}' {} times ({})".format(
        benchdir, ntimes, datetime.now()))
    fs = sorted(f for f in benchdir.iterdir() if f.suffix == ".c")

    for f in fs:
        for i in range(ntimes):
            i_run_cmd = CMD.format(filename=f, seed=i)
            print("## {}/{}. {}: {}".format(
                i+1, ntimes, time.strftime("%c"), i_run_cmd))
            os.system(i_run_cmd)


ntimes = 1

# NLA
dir_ = Path("../tests/c/nla/")
# dir_mp = "../tests/mp/"
# dir_complexity = "../tests/complexity/"
run(dir_.resolve(), ntimes)


# dirComplexity = "programs/complexity/gulwani_cav09"
# run(dirComplexity, ntimes)

# dirComplexity = "programs/complexity/gulwani_pldi09"
# run(dirComplexity, ntimes)

# dirComplexity = "programs/complexity/gulwani_popl09"
# run(dirComplexity, ntimes)


# dirHola = "programs/hola/"
# run(dirHola, ntimes)

# dirBm_oopsla = "programs/PIE/bm_oopsla/"
# run(dirBm_oopsla, ntimes)

# dirBm_ice = "programs/PIE/bm_ice/"
# run(dirBm_ice, ntimes)

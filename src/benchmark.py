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

TIMEOUT = 900  # seconds
CMD = "timeout {} ".format(TIMEOUT) +\
    "$SAGE/sage -python -O " +\
    "dig.py {filename} -log 4 -seed {seed}"


def run(benchdir, ntimes):
    assert benchdir.is_dir(), benchdir

    print("# Benchmark dir '{}' {} times ({})".format(
        benchdir, ntimes, datetime.now()), flush=True)
    fs = sorted(f for f in benchdir.iterdir() if f.suffix == ".java")

    for i, f in enumerate(fs):
        for j in range(ntimes):
            i_run_cmd = CMD.format(filename=f, seed=j)
            print("## {}/{}, run {}/{}. {}: {}".format(
                i+1, len(fs), j+1, ntimes,
                time.strftime("%c"), i_run_cmd), flush=True)
            os.system(i_run_cmd)


ntimes = 2

# NLA
dir_ = Path("../tests/nla/")
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

import pdb
import sys
import datetime
import time
import helpers.vcommon
from pathlib import Path

DBG = pdb.set_trace


"""
Example runs:
- sage -python -O dig.py ../tests/benchmark/nla/Bresenham.java
- sage -python -O dig.py ../tests/benchmark/nla/Bresenham.java -benchmark_times 5  :  run this file 5 times
- sage -python -O dig.py ../tests/benchmark/nla/ -benchmark_times 5 -benchmark_dir /path/to/existing_dir/ :  run all files in this dir 5 times
- sage -python -O dig.py ../tests/benchmark/nla/ -benchmark_times 5 -benchmark_dir existing_dir/ :  run all files in this dir 5 times and store results in `existing_dir`. If existing_dir has results from previous runs, will only attempt to do incomplete runs.  
"""

if __name__ == "__main__":
    import argparse
    aparser = argparse.ArgumentParser("DIG")
    ag = aparser.add_argument
    ag("inp", help=("input file (.c, .java. , .class, trace_text_file) "
                    "for invariant generation or result directory for analysis"))

    # 0 Error #1 Warn #2 Info #3 Debug #4 Detail
    ag("--log_level", "-log_level",
       type=int,
       choices=range(5),
       default=2,
       help="set logger info")

    ag("--seed", "-seed",
       type=float,
       help="use this seed")

    ag("--maxdeg", "-maxdeg",
       type=int,
       default=None,
       help="find nonlinear invs up to degree")

    ag("--maxterm", "-maxterm",
       type=int,
       default=None,
       help="autodegree")

    ag("--inpMaxV", "-inpMaxV",
       type=int,
       help="max inp value")

    ag("--se_mindepth", "-se_mindepth",
       type=int,
       help="depthlimit of symbolic execution")

    ag("--octmaxv", "-octmaxv",
       type=int,
       help="max val for oct ieqs")

    ag("--noss", "-noss",
       action="store_true",
       help="don't use symbolic states, i.e., just dynamic analysis")

    ag("--noeqts", "-noeqts",
       action="store_true",
       help="don't compute eq invariants")

    ag("--noieqs", "-noieqs",
       action="store_true",
       help="don't compute ieq/oct invariants")

    ag("--nominmaxplus", "-nominmaxplus",
       action="store_true",
       help="don't compute min/max-plus invariants")

    ag("--nopreposts", "-nopreposts",
       action="store_true",
       help="don't compute prepost specs")

    ag("--nomp", "-nomp",
       action="store_true",
       help="don't use multiprocessing")

    ag("--test_tracefile", "-test_tracefile",
       type=str,
       default=None,
       help="tracefile to test")

    ag("-uterms", "--uterms",
       type=str,
       default=None,
       help="user-supplied terms (separated by space), e.g., \"-uterms y^2 xy\"")

    ag("--benchmark_times", "-benchmark_times",
       type=int,
       default=None,
       help="run Dig this many times")

    ag("--tmpdir", "-tmpdirdir",
       type=str,
       default=None,
       help="store invariant results in this dir")

    ag("--benchmark_dir", "-benchmark_dir",
       type=str,
       default=None,
       help="store benchmark results in this dir")

    args = aparser.parse_args()
    inp = Path(args.inp)
    if args.benchmark_times:
        from analysis import Benchmark
        Benchmark(inp, args).doit()

    elif inp.is_dir():
        from analysis import Analysis
        Analysis(inp, args).doit()

    else:  # benchmark_times is None, input is a file: normal, single run
        assert benchmark_times is None and inp.is_file(), inp
        seed = round(time.time(), 2) if args.seed is None else float(args.seed)
        import settings
        mlog, se_mindepth = settings.setup(settings, args)
        mlog.info("{}: {}".format(datetime.datetime.now(), ' '.join(sys.argv)))

        if __debug__:
            mlog.warning("DEBUG MODE ON. Can be slow !")

        import alg
        if inp.suffix == ".java" or inp.suffix == ".class":
            if se_mindepth:
                settings.Java.SE_MIN_DEPTH = args.se_mindepth
            dig = alg.DigSymStatesJava(inp)
        elif inp.suffix == ".c":
            if se_mindepth:
                settings.C.SE_MIN_DEPTH = args.se_mindepth
            dig = alg.DigSymStatesC(inp)
        else:
            # traces file(s)
            test_tracefile = Path(
                args.test_tracefile) if args.test_tracefile else None
            dig = alg.DigTraces(inp, test_tracefile)

        dig.start(seed=seed, maxdeg=args.maxdeg)

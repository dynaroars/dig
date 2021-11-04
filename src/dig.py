import pdb
import sys
import datetime
import time
from pathlib import Path

DBG = pdb.set_trace


"""
Example runs:
- python3 -O dig.py ../benchmark/nla/Bresenham.java
- python3 -O dig.py ../benchmark/nla/Bresenham.java -benchmark_times 5  :  run this file 5 times
- python3 -O dig.py ../benchmark/nla/ -benchmark_times 5 -benchmark_dir /path/to/existing_dir/ :  run all files in this dir 5 times
- python3 -O dig.py ../benchmark/nla/ -benchmark_times 5 -benchmark_dir existing_dir/ :  run all files in this dir 5 times and store results in `existing_dir`. If existing_dir has results from previous runs, will only attempt to do incomplete runs.  


Run on traces
- sage -python -O dig.py ../tests/traces/CohenDiv1.csv -log 3
"""
if __name__ == "__main__":
    import argparse

    aparser = argparse.ArgumentParser("DIG")
    ag = aparser.add_argument
    ag(
        "inp",
        help=(
            "input file (.c, .java. , .class, trace_text_file) "
            "for invariant generation or result directory for analysis"
        ),
    )

    # 0 Error #1 Warn #2 Info #3 Debug
    ag(
        "--log_level",
        "-log_level",
        type=int,
        choices=range(5),
        default=3,
        help="set logger info",
    )

    ag("--seed", "-seed", type=float, help="use this seed")

    ag("--maxdeg", "-maxdeg",
       type=int,
       default=None,
       help="find nonlinear invs up to degree")

    ag("--maxterm", "-maxterm", type=int, default=None, help="autodegree")

    ag("--nrandinps", "-nrandinps", type=int, default=None,
       help="number of random inputs (on used with --noss)")

    ag("--inpMaxV", "-inpMaxV", type=int, help="max inp value")

    ag("--se_mindepth", "-se_mindepth",
       type=int,
       help="depthlimit of symbolic execution")

    ag("--se_maxdepth", "-se_maxdepth",
       type=int,
       help="depthlimit of symbolic execution",
       )

    ag("--iupper", "-iupper", type=int, help="max upperbound val for ieqs")

    ag(
        "--ideg",
        "-ideg",
        type=int,
        help="degree for ieqs (e.g., 1 = linear, 2 = quadratic, etc)",
    )

    ag(
        "--iterms",
        "-iterms",
        type=int,
        help="number of terms for ieqs, 2 is octagonal invs",
    )

    ag(
        "--icoefs",
        "-icoefs",
        type=int,
        help="coefs for ieqs, e.g., 1 means [-1,0,1], i.e., oct",
    )

    ag(
        "--noss",
        "-noss",
        action="store_true",
        help="don't use symbolic states, i.e., just dynamic analysis",
    )

    ag("--noeqts", "-noeqts", action="store_true",
       help="don't compute eq invariants")

    ag(
        "--noieqs",
        "-noieqs",
        action="store_true",
        help="don't compute ieq/oct invariants",
    )
    ag(
        "--nocongruences",
        "-nocongruences",
        action="store_true",
        help="don't compute congruence invariants",
    )

    ag(
        "--noarrays",
        "-noarrays",
        action="store_true",
        help="don't compute array relations",
    )

    ag(
        "--nominmaxplus",
        "-nominmaxplus",
        action="store_true",
        help="don't compute min/max-plus invariants",
    )

    ag(
        "--nopreposts",
        "-nopreposts",
        action="store_true",
        help="don't compute prepost specs",
    )

    ag(
        "--noincrdepth",
        "-noincrdepth",
        action="store_true",
        help="don't use incremental depth",
    )

    ag(
        "--nosimplify",
        "-nosimplify",
        action="store_true",
        help="don't simplify invariants, e.g., don't remove weaker invariants (for debugging)",
    )

    ag(
        "--nofilter",
        "-nofilter",
        action="store_true",
        help="don't filter inequality terms (for deubgging)",
    )

    ag("--nomp", "-nomp", action="store_true", help="don't use multiprocessing")

    ag(
        "--dosolverstats",
        "-dosolverstats",
        action="store_true",
        help="collect solver stats (e.g., how many sat/unsat, etc)",
    )
    ag(
        "--writeresults",
        "-writeresults",
        type=str,
        default=None,
        help="print inv results to file",
    )
    ag(
        "--writevtraces",
        "-writevtraces",
        type=str,
        default=None,
        help="write vtraces to a csv file"
    )
    ag(
        "--test_tracefile",
        "-test_tracefile",
        type=str,
        default=None,
        help="tracefile to test",
    )

    ag(
        "-uterms",
        "--uterms",
        type=str,
        default=None,
        help='user-supplied terms (separated by ;), e.g., -uterms "y^2 ; xy+4"',
    )

    ag(
        "--benchmark_times",
        "-benchmark_times",
        type=int,
        default=None,
        help="run Dig this many times",
    )

    ag(
        "--tmpdir",
        "-tmpdir",
        type=str,
        default=None,
        help="store invariant results in this dir",
    )

    ag(
        "--benchmark_dir",
        "-benchmark_dir",
        type=str,
        default=None,
        help="store benchmark results in this dir",
    )

    args = aparser.parse_args()
    inp = Path(args.inp)
    if args.benchmark_times:
        from analysis import Benchmark

        Benchmark(inp, args).start()

    elif inp.is_dir():
        from analysis import Analysis

        Analysis(inp, args).start()

    else:  # benchmark_times is None, input is a file: normal, single run
        assert args.benchmark_times is None, args.benchmark_times

        if not inp.is_file():
            raise FileNotFoundError(f"'{inp}' not found")

        seed = round(time.time(), 2) if args.seed is None else float(args.seed)
        import settings

        mlog = settings.setup(settings, args)
        mlog.info(f"{datetime.datetime.now()}: {' '.join(sys.argv)}")

        if __debug__:
            mlog.warning("DEBUG MODE ON. Can be slow !")
        import alg

        if inp.suffix == ".java" or inp.suffix == ".class":
            dig = alg.DigSymStatesJava(inp)
        elif inp.suffix == ".c":
            dig = alg.DigSymStatesC(inp)
        else:
            # traces file(s)
            test_tracefile = Path(args.test_tracefile) \
                if args.test_tracefile else None
            dig = alg.DigTraces.mk(inp, test_tracefile)

        dinvs = dig.start(seed=seed, maxdeg=args.maxdeg)

        print(dinvs)
        # write results to file

        if args.writeresults:
            resultfile = Path(args.writeresults)
            invs = dinvs.__str__(writeresults=True)
            resultfile.write_text(invs)
            print(f"{dinvs.siz} invs over {len(dinvs)} locs written to {resultfile}")

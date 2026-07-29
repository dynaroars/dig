import pdb
import os
import sys
import datetime
import time
import argparse
from pathlib import Path
DBG = pdb.set_trace


"""
Example runs:
- python3 -O dig.py ../benchmark/nla/Bresenham.c
- python3 -O dig.py ../benchmark/nla/Bresenham.c -benchmark_times 5  :  run this file 5 times
- python3 -O dig.py ../benchmark/nla/ -benchmark_times 5 -benchmark_dir /path/to/existing_dir/ :  run all files in this dir 5 times
- python3 -O dig.py ../benchmark/nla/ -benchmark_times 5 -benchmark_dir existing_dir/ :  run all files in this dir 5 times and store results in `existing_dir`. If existing_dir has results from previous runs, will only attempt to do incomplete runs.


Run on traces
- sage -python -O dig.py ../tests/traces/CohenDiv1.csv -log 3
"""
    
if __name__ == "__main__":
    # Reproducibility: set iteration order influences the order RNG is consumed,
    # so without a fixed hash seed results vary run-to-run even with -seed. Pin it
    # and re-exec once (PYTHONHASHSEED must be set before the interpreter starts).
    # orig_argv preserves interpreter flags (e.g. -O). Opt out by setting the var
    # yourself, e.g. PYTHONHASHSEED=random.
    if os.environ.get("PYTHONHASHSEED") is None:
        os.environ["PYTHONHASHSEED"] = "0"
        os.execv(sys.executable,
                 getattr(sys, "orig_argv", [sys.executable] + sys.argv))

    aparser = argparse.ArgumentParser(
        "DIG",
        epilog="invariant types for -types: eqt, ieq, minmax, congruence, "
               "array, recurrence (e.g. -types eqt,ieq). Omit to infer all.",
    )

    # argument groups, shown in this order by --help
    g_sel = aparser.add_argument_group(
        "invariant selection", "which invariant types to infer (default: all)")
    g_mode = aparser.add_argument_group("modes")
    g_tune = aparser.add_argument_group("advanced tuning")
    g_eng = aparser.add_argument_group("advanced engines")
    g_io = aparser.add_argument_group("output & serialization")
    g_bench = aparser.add_argument_group("benchmarking")
    g_dbg = aparser.add_argument_group("debugging & diagnostics")

    # one positive selector replaces the seven -no<type> flags (which still
    # work as hidden aliases below, so existing scripts/UI keep functioning)
    g_sel.add_argument(
        "--types", "-types", "--only", "-only", type=str, default=None,
        metavar="T1,T2,...",
        help="comma-separated invariant types to infer; the rest are turned "
             "off. Types: eqt, ieq, minmax, congruence, array, recurrence. "
             "Default: all types.")

    ag = aparser.add_argument
    ag(
        "inp",
        help=(
            "input file (.c, trace_text_file) "
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

    ag = g_mode.add_argument
    ag(
        "--llm",
        "-llm",
        action="store_true",
        help="use an LLM (claude) to propose invariants, verified soundly by "
             "DIG's symbolic states + z3 (requires ANTHROPIC_API_KEY)",
    )

    ag(
        "--llm_rounds",
        "-llm_rounds",
        type=int,
        default=3,
        help="max LLM propose/verify (CEGIR) rounds (default 3)",
    )

    ag(
        "--llm_no_traces",
        "-llm_no_traces",
        action="store_true",
        help="LLM mode: prompt with source only, no concrete traces "
             "(does not run the compiled program)",
    )

    ag = g_tune.add_argument
    ag("--maxdeg", "-maxdeg",
       type=int,
       default=None,
       help="find nonlinear invs up to degree")

    # -maxterm: internal auto-degree cap, kept functional but hidden from --help
    ag("--maxterm", "-maxterm", type=int, default=None, help=argparse.SUPPRESS)

    ag("--nrandinps", "-nrandinps", type=int, default=None,
       help="number of random inputs (on used with --noss)")

    ag("--inpMaxV", "-inpMaxV", type=int, help="max inp value")

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

    ag = g_mode.add_argument
    ag(
        "--noss",
        "-noss",
        action="store_true",
        help="pure dynamic analysis: no symbolic states, no proofs",
    )

    # invariant-type selection is via -types (see the "invariant selection"
    # group above); the old per-type -no<type> flags have been removed.
    ag = g_sel.add_argument
    ag(
        "--norecurrencemp",
        "-norecurrencemp",
        action="store_true",
        help="don't extend the recurrence engine to branching (multi-path) "
             "loop bodies (egcd/fermat/prodbin); single-path recurrences only",
    )

    ag = g_eng.add_argument
    ag(
        "--dokapur",
        "-dokapur",
        action="store_true",
        help="also run the RC-Kapur bounded-degree ideal engine (static "
             "equalities via the reachable-state null space; in memory of "
             "Deepak Kapur)",
    )

    ag(
        "--dosymba",
        "-dosymba",
        action="store_true",
        help="use SYMBA simultaneous optimization for inequality/min-max "
             "bounds (one shared solver for all terms) instead of one "
             "z3-Optimize solve per term",
    )

    ag = g_mode.add_argument
    ag(
        "--nollmhoudini",
        "-nollmhoudini",
        action="store_true",
        help="llm mode: don't run the extra k-induction (houdini) pass over "
             "the union of LLM candidates",
    )

    # NOTE: -noincrdepth/-nosimplify/-nofilter were removed; incremental depth
    # is always on now, and DO_SIMPLIFY/DO_FILTER are constants in settings.py.
    ag = g_dbg.add_argument
    ag("--nomp", "-nomp", action="store_true", help="don't use multiprocessing")

    ag(
        "--dosolverstats",
        "-dosolverstats",
        action="store_true",
        help="collect solver stats (e.g., how many sat/unsat, etc)",
    )

    ag = g_io.add_argument
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
        "--writesstates",
        "-writesstates",
        type=str,
        default=None,
        help="write symbolic states to file; also stop after writing"
    )

    ag(
        "--readsstates",
        "-readsstates",
        type=str,
        default=None,
        help="read symbolic states from a file and do inference using them"
    )

    ag(
        "--test_tracefile",
        "-test_tracefile",
        type=str,
        default=None,
        help="tracefile to test",
    )

    ag = g_tune.add_argument
    ag(
        "--uterms",
        "-uterms",
        type=str,
        default=None,
        help='user-supplied terms (separated by ;), e.g., -uterms "y^2 ; xy+4"',
    )

    ag = g_bench.add_argument
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

    # Validate every path-taking flag up front (before any work, and not via
    # asserts that -O strips) so bad paths fail fast with a clear message.
    def _check_paths(args):
        # input paths that must already be a readable file
        for flag, val in (("-readsstates", args.readsstates),
                          ("-test_tracefile", args.test_tracefile)):
            if val and not Path(val).is_file():
                raise FileNotFoundError(f"{flag} '{val}' is not an existing file")
        # output file paths: parent dir must exist, and it can't be a directory
        for flag, val in (("-writeresults", args.writeresults),
                          ("-writevtraces", args.writevtraces),
                          ("-writesstates", args.writesstates)):
            if val:
                p = Path(val)
                if p.is_dir():
                    raise IsADirectoryError(
                        f"{flag} '{p}' is a directory; give a file path")
                if not p.parent.is_dir():
                    raise FileNotFoundError(
                        f"{flag} dir '{p.parent}' does not exist")
        # paths that must already be a directory
        for flag, val in (("-tmpdir", args.tmpdir),
                          ("-benchmark_dir", args.benchmark_dir)):
            if val and not Path(val).is_dir():
                raise NotADirectoryError(
                    f"{flag} '{val}' is not an existing directory")

    _check_paths(args)

    # validate -types up front so a bad name is a clean CLI error (all modes)
    if args.types:
        import settings as _settings
        try:
            _settings._parse_types(args.types)
        except ValueError as ex:
            aparser.error(str(ex))

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

        if inp.suffix == ".c" and args.llm:
            import llm_infer

            dinvs, time_d = llm_infer.run(inp, seed=seed,
                                          max_rounds=args.llm_rounds,
                                          no_traces=args.llm_no_traces)
            llm_infer.report(inp.stem, dinvs, time_d, seed)
        else:
            if inp.suffix == ".c":
                dig = alg.DigSymStatesC(inp)
            else:
                # traces file(s)
                test_tracefile = Path(args.test_tracefile) \
                    if args.test_tracefile else None
                dig = alg.DigTraces.mk(inp, test_tracefile)

            dinvs = dig.start(seed=seed, maxdeg=args.maxdeg)
            if dinvs:
                print(dinvs)

        # write results to file (shared by both paths)
        if dinvs and args.writeresults:
            resultfile = Path(args.writeresults)
            invs = dinvs.__str__(writeresults=True)
            resultfile.write_text(invs)
            print(f"{dinvs.siz} invs over {len(dinvs)} locs written to {resultfile}")

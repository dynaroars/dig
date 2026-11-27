import os
import sys
import datetime
import time
import argparse
from pathlib import Path


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
               "recurrence (e.g. -types eqt,ieq). Omit to infer all.",
    )

    # argument groups, shown in this order by --help
    g_sel = aparser.add_argument_group(
        "invariant selection", "which invariant types to infer (default: all)")
    g_mode = aparser.add_argument_group("modes")
    g_tune = aparser.add_argument_group("advanced tuning")
    g_io = aparser.add_argument_group("output & serialization")
    g_dbg = aparser.add_argument_group("debugging & diagnostics")
    g_axiom = aparser.add_argument_group("API axiom analysis")

    # one positive selector replaces the seven -no<type> flags (which still
    # work as hidden aliases below, so existing scripts/UI keep functioning)
    g_sel.add_argument(
        "--types", "-types", "--only", "-only", type=str, default=None,
        metavar="T1,T2,...",
        help="comma-separated invariant types to infer; the rest are turned "
             "off. Types: eqt, ieq, minmax, congruence, recurrence. "
             "Default: all types.")

    ag = aparser.add_argument
    ag(
        "inp",
        nargs="?",
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

    ax = g_axiom.add_argument
    ax("--axioms", type=str, metavar="MANIFEST", help="run API axiom analysis from TOML")
    ax("--max-call-cost", type=int)
    ax("--variables-per-type", type=int)
    ax("--max-terms-per-type", type=int)
    ax("--discovery-tests", type=int)
    ax("--validation-tests", type=int)
    ax("--minimum-valid-samples", type=int)
    ax("--python-executable", default=sys.executable)
    ax("--java", default="java", help="Java executable for a Java axiom target")
    ax("--javac", default="javac", help="Java compiler for the checked-in worker")
    ax("--worker-timeout", type=float)
    ax("--verifier", choices=("none", "finite", "smt-model"), default="none")
    ax("--replay-counterexample", type=str, metavar="RESULT_JSON")
    ax("--finding", type=str, help="finding ID to replay (default: first counterexample)")
    ax("--json-output", type=str, metavar="FILE")

    ag = g_mode.add_argument
    ag(
        "--llm",
        "-llm",
        action="store_true",
        help="use an LLM (Gemini) to propose invariants, verified soundly by "
             "DIG's symbolic states + z3 (uses GEMINI_API_KEY or ./gemini_api)",
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

    g_cert = aparser.add_argument_group(
        "verification (default: Z3; optional Lean 4 certification)")
    ag = g_cert.add_argument
    ag("--certify-lean", "-certify_lean", dest="certify_lean",
       action="store_true",
       help="certify the Z3-checked invariants with Lean 4 (unbounded, "
            "zero Z3 in TCB)")
    ag("--lean-only", dest="lean_only", action="store_true",
       help="verify candidates directly with Lean 4 instead of Z3 "
            "(drops unproved candidates unless --keep-unverified is set)")
    ag("--z3-check", "-z3check", dest="z3_check", action="store_true",
       help="check candidates with Z3 against symbolic states (default)")
    ag("--keep-unverified", dest="keep_unverified", action="store_true",
       help="with --lean-only: also report candidates Lean could not prove "
            "(marked unverified) instead of dropping them")
    ag("--lean-out", dest="lean_out", type=str, default=None, metavar="FILE",
       help="write the final .lean certificate to FILE")
    ag("--lean-bin", dest="lean_bin", type=str, default=None, metavar="PATH",
       help="Lean binary (default: lean on PATH, then elan's pinned toolchain)")
    ag("--lean-timeout", dest="lean_timeout", type=float, default=None,
       metavar="SECS", help="timeout per Lean run (default 120)")
    ag("--lean-max-rounds", dest="lean_max_rounds", type=int, default=None,
       help="cap on drop-pass rounds (default 8)")

    ag = g_tune.add_argument
    ag("--maxdeg", "-maxdeg",
       type=int,
       default=None,
       help="find nonlinear invs up to degree")

    ag("--se_maxdepth", "-se_maxdepth",
       type=int,
       help="depthlimit of symbolic execution",
       )

    ag = g_mode.add_argument
    ag(
        "--noss",
        "-noss",
        action="store_true",
        help="pure dynamic analysis: no symbolic states, no proofs",
    )

    ag(
        "--nollmhoudini",
        "-nollmhoudini",
        action="store_true",
        help="llm mode: don't run the extra k-induction (houdini) pass over "
             "the union of LLM candidates",
    )

    ag = g_dbg.add_argument
    ag("--nomp", "-nomp", action="store_true", help="don't use multiprocessing")

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
        "--tmpdir",
        "-tmpdir",
        type=str,
        default=None,
        help="store invariant results in this dir",
    )

    args = aparser.parse_args()

    for name in ("maxdeg", "se_maxdepth", "llm_rounds"):
        value = getattr(args, name, None)
        if value is not None and value < 1:
            aparser.error(f"--{name} must be positive")

    if args.axioms and args.inp:
        aparser.error("positional input and --axioms are mutually exclusive")
    if not args.axioms and not args.inp:
        aparser.error("a positional input or --axioms MANIFEST is required")

    # Validate every path-taking flag up front (before any work, and not via
    # asserts that -O strips) so bad paths fail fast with a clear message.
    def _check_paths(args):
        # input paths that must already be a readable file
        for flag, val in (("--axioms", args.axioms),
                          ("--replay-counterexample", args.replay_counterexample)):
            if val and not Path(val).is_file():
                raise FileNotFoundError(f"{flag} '{val}' is not an existing file")
        # output file paths: parent dir must exist, and it can't be a directory
        for flag, val in (("-writeresults", args.writeresults),
                          ("-writevtraces", args.writevtraces),
                          ("--json-output", args.json_output)):
            if val:
                p = Path(val)
                if p.is_dir():
                    raise IsADirectoryError(
                        f"{flag} '{p}' is a directory; give a file path")
                if not p.parent.is_dir():
                    raise FileNotFoundError(
                        f"{flag} dir '{p.parent}' does not exist")
        # paths that must already be a directory
        if args.tmpdir and not Path(args.tmpdir).is_dir():
            raise NotADirectoryError(
                f"-tmpdir '{args.tmpdir}' is not an existing directory")

    _check_paths(args)

    if args.axioms:
        from axioms.cli import run_from_args

        raise SystemExit(run_from_args(args))

    # validate -types up front so a bad name is a clean CLI error (all modes)
    if args.types:
        import settings as _settings
        try:
            _settings._parse_types(args.types)
        except ValueError as ex:
            aparser.error(str(ex))

    inp = Path(args.inp)
    if inp.is_dir():
        from analysis import Analysis

        Analysis(inp, args).start()

    else:  # input is a file: normal, single run
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
                dig = alg.DigTraces.mk(inp)

            dinvs = dig.start(seed=seed, maxdeg=args.maxdeg)
            if dinvs:
                print(dinvs)

        # write results to file (shared by both paths)
        if dinvs and args.writeresults:
            resultfile = Path(args.writeresults)
            invs = dinvs.__str__(writeresults=True)
            resultfile.write_text(invs)
            print(f"{dinvs.siz} invs over {len(dinvs)} locs written to {resultfile}")

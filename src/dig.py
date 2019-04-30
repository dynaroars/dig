from vcommon import getLogger, getLogLevel

if __name__ == "__main__":
    import argparse
    aparser = argparse.ArgumentParser("DIG")
    ag = aparser.add_argument

    ag("inp", help="inp")

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

    ag("--jpfmindepth", "-jpfmindepth",
       type=int,
       help="JPF depthlimit")

    ag("--octMaxV", "-octMaxV",
       type=int,
       help="max val for oct ieqs")

    ag("--eqtrate", "-eqtrate",
       type=float,
       help="Equation rate multiplier")

    ag("--noeqts", "-noeqts",
       action="store_true")

    ag("--noieqs", "-noieqs",
       action="store_true")

    ag("--nomp", "-nomp",
       action="store_true",
       help="don't use multiprocessing")

    ag("--normtmp", "-normtmp",
       action="store_true")

    from time import time
    args = aparser.parse_args()

    import settings
    settings.doMP = not args.nomp

    if args.log_level != settings.logger_level and 0 <= args.log_level <= 4:
        settings.logger_level = args.log_level
    settings.logger_level = getLogLevel(settings.logger_level)

    mlog = getLogger(__name__, settings.logger_level)

    if args.inpMaxV != settings.inpMaxV and args.inpMaxV >= 1:
        settings.inpMaxV = args.inpMaxV

    if args.eqtrate != settings.eqtrate and args.eqtrate >= 1:
        settings.eqtrate = args.eqtrate

    if args.jpfmindepth != settings.jpfmindepth and args.jpfmindepth >= 1:
        settings.jpfmindepth = args.jpfmindepth

    if args.octMaxV != settings.octMaxV and args.octMaxV >= 1:
        settings.octMaxV = args.octMaxV

    if args.maxterm != settings.maxterm and args.maxterm >= 1:
        settings.maxterm = args.maxterm

    if __debug__:
        mlog.warn("DEBUG MODE ON. Can be slow !")

    seed = round(time(), 2) if args.seed is None else float(args.seed)

    import alg
    inp = args.inp
    if inp.endswith(".java") or inp.endswith(".class"):
        dig = alg.DigCegir(inp)
    else:
        dig = alg.DigTraces(inp)

    invs, traces, tmpdir = dig.start(
        seed=seed, maxdeg=args.maxdeg,
        doEqts=not args.noeqts, doIeqs=not args.noieqs)

    if not args.normtmp:
        import shutil
        mlog.debug("rm -rf {}".format(tmpdir))
        shutil.rmtree(tmpdir)
    else:
        print("tmpdir: {}".format(tmpdir))

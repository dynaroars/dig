import pdb
import helpers.vcommon as CM
# import config as CC
import settings


DBG = pdb.set_trace

mlog = CM.getLogger(__name__, settings.logger_level)


if __name__ == "__main__":
    import argparse
    aparser = argparse.ArgumentParser("Axiom Inferrence")
    aparser.add_argument("sig",
                         help="file containing function signatures",
                         action="store")

    # 0 Error #1 Warn #2 Info #3 Debug #4 Detail
    aparser.add_argument("--log_level", "-log_level",
                         help="set log info",
                         type=int,
                         choices=range(5),
                         default=4)

    aparser.add_argument("--seed", "-seed",
                         type=float,
                         help="use this seed")

    aparser.add_argument("--ntests", "-ntests",
                         type=int,
                         default=10,
                         help="use this # of tests (initial test)")

    aparser.add_argument("--max_nfuns", "-max_nfuns",
                         type=int,
                         default=3,
                         help="max number of functions in terms")

    aparser.add_argument("--merge_se", "-merge_se",
                         default=False,
                         action="store_true",
                         help="considffer all possible side effects (will generate more stuff)")

    import os.path
    args = aparser.parse_args()

    settings.logger_level = args.log_level
    settings.logger_level = CM.getLogLevel(
        settings.logger_level)
    mlog = CM.getLogger(__name__, settings.logger_level)

    import alg
    mlog.warning("DEBUG MODE ON. Can be slow !")

    from time import time
    seed = round(time(), 2) if args.seed is None else float(args.seed)

    import importlib.util
    spec = importlib.util.spec_from_file_location("", args.sig)
    ex = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(ex)

    for d in ex.defs:
        print(d)
        alg.Fun.eval_fun_def(d)

    fterms = [alg.Fun.eval_fun_def(d) for d in ex.defs]
    infer = alg.Infer(fterms)
    try:
        typs_d = ex.typs_d
    except AttributeError:
        typs_d = {}
    infer.search(seed, args.ntests, args.max_nfuns,
                 args.merge_se, typs_d, ex.lang)

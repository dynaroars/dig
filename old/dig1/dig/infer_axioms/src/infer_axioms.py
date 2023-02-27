import vu_common as CM
import config as CC

if __name__ == "__main__":
    import argparse
    aparser = argparse.ArgumentParser("Axiom Inferrence")
    aparser.add_argument("sig", 
                         help="file containing function signatures",
                         action="store")
    
    #0 Error #1 Warn #2 Info #3 Debug #4 Detail
    aparser.add_argument("--logger_level", "-logger_level",
                         help="set logger info",
                         type=int,
                         choices=range(5),
                         default = 4)
    
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
                         help="consider all possible side effects (will generate more stuff)")
    
    import os.path    
    args = aparser.parse_args()
    CC.logger_level = args.logger_level            
    logger = CM.VLog(os.path.basename(__file__))
    logger.level = CC.logger_level
    
    import alg    
    alg.logger.level = logger.level
    if __debug__: logger.warn("DEBUG MODE ON. Can be slow !")

    from time import time
    seed = round(time(), 2) if args.seed is None else float(args.seed)
    
    import sys
    if sys.version_info >= (3, 5):
        import importlib.util
        spec = importlib.util.spec_from_file_location("", args.sig)
        ex = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(ex)
    else:
        from importlib.machinery import SourceFileLoader
        ex = SourceFileLoader("", args.sig).load_module()
    
    fterms = [alg.Fun.eval_fun_def(d) for d in ex.defs]
    infer = alg.Infer(fterms)
    try:
        typs_d = ex.typs_d
    except AttributeError:
        typs_d = {}
    infer.search(seed, args.ntests, args.max_nfuns, args.merge_se, typs_d, ex.lang)

    

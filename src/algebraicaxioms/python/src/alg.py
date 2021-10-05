"""
pop(push(l,x)) = x
pop(insert(l,x,idx),idx) = x
pop_last(l) = pop(l,len(idx)-1)
append(l,x) = insert(l,x,len(idx)-1)
"""
import pdb
import random
import os.path
from collections import Counter

import settings
import helpers.vcommon as CM

from term import IncompatTyp, Term, Fun
from eqfun import EqFun
from alg_lang import Python, Java


DBG = pdb.set_trace

mlog = CM.getLogger(__name__, settings.logger_level)


class Infer(object):
    clses = {Python.__name__.lower(): Python,
             Java.__name__.lower(): Java}

    def __init__(self, terms):
        assert all(isinstance(t, Term) for t in terms)
        self.terms = terms

    @classmethod
    def prune(cls, axioms, pure_imply=True):
        """
        Return strongest axioms not implied by others
        """
        weaks = set()
        for f in axioms:
            if f in weaks:
                continue
            for g in axioms:
                if f is g or g in weaks:
                    continue
                if pure_imply:
                    is_implied = f.implies(g)
                else:
                    qfs_f = {}
                    qfs_g = {}
                    is_implied = f.iimplies(qfs_f, g, qfs_g)

                if is_implied:
                    mlog.debug("{} => {}".format(f, g))
                    weaks.add(g)

        strongs = [a for a in axioms if a not in weaks]
        return strongs

    @classmethod
    def test(cls, axioms, ntests: int, merge_se: bool, typs_d: dict, lang_cls):
        assert isinstance(axioms, list) and axioms
        assert isinstance(ntests, int) and ntests > 0, ntests
        assert isinstance(typs_d, dict), typs_d

        iaxioms = []
        test_funs = []
        for i, axiom in enumerate(axioms):
            axioms_, test_funs_ = axiom.gen_test_funs(
                i, merge_se, typs_d, ntests, lang_cls)
            iaxioms.extend(axioms_)
            test_funs.extend(test_funs_)

        mlog.info("{} instantiated candidates".format(len(iaxioms)))
        mlog.debug("\n" + Term.str_of_terms(iaxioms))

        mlog.info("test against random inputs")
        code = lang_cls.mk_fun_main(test_funs)
        stats = lang_cls.myrun(code)
        # CM.pause()
        assert len(iaxioms) == len(stats)
        axioms = [axiom for axiom, stat in zip(iaxioms, stats) if stat]

        mlog.info("{} candidate(s)".format(len(axioms)))
        if axioms:
            mlog.debug("\n" + Term.str_of_terms(axioms))

        return axioms

    def search(self, seed: (float, int), ntests: int, max_nfuns: int,
               merge_se: bool, typs_d: dict, lang: str):
        assert isinstance(seed, (float, int)), seed
        assert isinstance(ntests, int) and ntests > 0, ntests
        assert isinstance(typs_d, dict), typs_d
        assert isinstance(lang, str), lang

        random.seed(seed)
        mlog.info("seed: {}".format(seed))

        lang_cls = Infer.clses[lang.lower()]
        axioms = self.terms
        mlog.info("{} terms".format(len(axioms)))
        mlog.debug("\n" + Term.str_of_terms(axioms))

        mlog.info("test for exceptions")
        test_funs = []
        for i, axiom in enumerate(axioms):
            test_funs_ = axiom.gen_test_funs_soft(
                i, merge_se, typs_d, ntests, lang_cls)
            test_funs.append(test_funs_)

        code = lang_cls.mk_fun_main(test_funs)
        stats = lang_cls.myrun(code)

        ignores = set(
            [axiom for axiom, stat in zip(axioms, stats) if not stat])
        mlog.info("{}/{} ignores".format(len(ignores), len(axioms)))
        if ignores:
            mlog.debug("\n" + Term.str_of_terms(ignores))
        axioms = EqFun.gen_eqts(axioms, ignores, max_nfuns)
        assert axioms

        mlog.info("{} eqt templates".format(len(axioms)))
        mlog.debug("\n" + Term.str_of_terms(axioms))

        part_siz = 50
        axioms = list(set(axioms))  # shuffle axioms
        axioms_parts = [axioms[i: i + part_siz]
                        for i in range(0, len(axioms), part_siz)]

        taxioms = []
        for i, ps in enumerate(axioms_parts):
            mlog.info("{}/{}. testing {} eqt templates"
                      .format(i + 1, len(axioms_parts), len(ps)))
            axioms_ = self.test(ps, ntests, merge_se, typs_d, lang_cls)
            taxioms.extend(axioms_)

        axioms = sorted(taxioms, key=lambda a: (len(a.funs), len(a.nodes)))
        if not axioms:
            return

        mlog.info("{} candidates(s) total".format(len(axioms)))
        # some final simplifications
        # done after testings, which return likely candidates
        axioms = self.prune(axioms, pure_imply=True)
        mlog.info("after 1st pruning {} candidate(s)".format(len(axioms)))
        if not axioms:
            return
        mlog.debug("\n" + Term.str_of_terms(axioms))
        
        axioms = self.prune(axioms, pure_imply=False)
        mlog.info("after 2nd pruning, {} candidate(s)".format(len(axioms)))
        if not axioms:
            return
        mlog.info("\n" + Term.str_of_terms(axioms))


if __name__ == "__main__":
    import doctest
    doctest.testmod()
            

import operator
import pdb
import sympy
import z3
from beartype import beartype


import settings
import helpers.vcommon as CM
from helpers.miscs import Miscs
from helpers.z3utils import Z3

import infer.inv
import infer.infer

DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.LOGGER_LEVEL)


class Oct(infer.inv.Inv):
    """
    Octagonal invariants c1x + c2y <= c3
    """
    @beartype
    def __init__(self, myoct:sympy.Le, stat=None) -> None:
        """
        For both <=  (normal OctInvs)  or < (Precond in PrePost)
        """
        assert isinstance(myoct, sympy.Le), myoct

        super().__init__(myoct, stat)

    @beartype
    @property
    def is_simple(self) -> bool:
        return self.inv.rhs.is_constant() and self.inv.rhs.is_zero

    @beartype
    @property
    def mystr(self) -> str:
        return f"{self.inv.lhs} <= {self.inv.rhs}"


class Infer(infer.infer._Opt):

    IUPPER = settings.IUPPER

    def __init__(self, symstates, prog):
        super().__init__(symstates, prog)

    @beartype
    @staticmethod
    def to_expr(term) -> z3.ExprRef:
        return Z3.parse(str(term.term))

    @staticmethod
    def inv_cls(term_ub:int) -> Oct:
        return Oct(term_ub)

    @classmethod
    def my_get_terms(cls, symbols):
        assert symbols, symbols
        assert settings.IDEG >= 1, settings.IDEG

        if settings.IDEG == 1:
            terms = Miscs.get_terms_fixed_coefs(
                symbols, settings.ITERMS, settings.ICOEFS
            )
        else:
            terms = Miscs.get_terms(list(symbols), settings.IDEG)
            terms = [t for t in terms if t != 1]
            terms = Miscs.get_terms_fixed_coefs(
                terms, settings.ITERMS, settings.ICOEFS, do_create_terms=False
            )

            terms_ = set()
            for ts in terms:
                assert ts
                ts_ = [set(t.free_symbols) for t, _ in ts]
                if len(ts) <= 1 or not set.intersection(*ts_):
                    terms_.add(sum(operator.mul(*tc) for tc in ts))
            terms = terms_

        if settings.UTERMS:
            uterms = cls.my_get_terms_user(symbols, settings.UTERMS)
            old_siz = len(terms)
            terms.update(uterms)
            mlog.debug(f"add {len(terms) - old_siz} new terms from user")

        terms = [infer.inv.RelTerm(t) for t in terms]
        return terms

    @staticmethod
    def my_get_terms_user(symbols, uterms):
        assert isinstance(uterms, set) and uterms, uterms
        assert all(isinstance(t, str) for t in uterms), uterms

        uterms = set(sympy.sympify(term) for term in uterms)

        if not set(v for t in uterms for v in t.free_symbols).issubset(set(symbols)):
            raise NameError(f"{uterms} contain symbols not in {symbols}")
        terms = set()
        for t in uterms:
            terms.add(t)
            terms.add(-t)
            ts = [t_ for v in symbols for t_ in (v+t, v-t, -v+t, -v-t)]
            for t_ in ts:
                if isinstance(t_, sympy.Number):
                    mlog.warning(f"skipping {t_}")
                else:
                    terms.add(t_)

        return terms

    @staticmethod
    def get_excludes(terms, inps):
        excludes = set()
        for term in terms:
            t_symbs = set(map(str, term.symbols))
            if len(t_symbs) <= 1:  # ok for finding bound of single input val
                continue

            if inps.issuperset(t_symbs):
                excludes.add(term)
        return excludes

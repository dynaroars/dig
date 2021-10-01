import typing
import os.path

import vu_common as CM
import config as CC

from term import Term, Arg, Fun

logger = CM.VLog(os.path.basename(__file__))
logger.level = CC.logger_level
CM.VLog.PRINT_TIME = False

class EqFun(Fun):
    axiomeq = "eq"
    
    def __init__(self, fun):
        super(EqFun, self).__init__(fun)
        assert self.val == self.axiomeq and len(self.children) == 2

    @property
    def lhs(self): return self.children[0]

    @property
    def rhs(self): return self.children[1]

    def __str__(self): return "{} = {}".format(self.lhs, self.rhs)
        
    @classmethod
    def eq(cls, children:tuple):
        assert isinstance(children,tuple) and len(children) == 2, children
        return cls.mk(val=cls.axiomeq,
                      call="==", 
                      inp_typs=(typing.Any, typing.Any),  #TODO, is this right ? 
                      outp_typ=bool,
                      side_effect_idxs=None,
                      is_commute=True,
                      children=children)

    @classmethod
    def mk_term_filters(cls, ignores, max_nfuns):
        too_long = lambda term: len(term.funs) > max_nfuns
        in_ignores = lambda term: term in ignores
        filters = [too_long, in_ignores]
        return filters

    @classmethod
    def gen_const_eqts(cls, terms):
        #axioms of the form  x = fun(...,x)

        #don't consider x = fun(x,y,z)
        too_simple = lambda _, rhs: \
                     (isinstance(rhs, Fun) and
                      all(isinstance(c, Arg) for c in rhs.children))
        filters = [too_simple]
        
        ceqts = []
        for rhs in terms:
            #don't consider axiom of the form ? = void_fun
            if rhs.outp_typ: 
                lhs = Arg.mk(rhs.outp_typ)
                children = (lhs, rhs)
                if any(f(lhs,rhs) for f in filters):
                    continue

                eqt = cls.eq(children)                
                ceqts.append(eqt)

        logger.info("{} const eqts".format(len(ceqts)))
        if ceqts:
            logger.debug("\n" + Term.str_of_terms(ceqts))
        #CM.pause()
        return ceqts

    @classmethod
    def gen_term_eqts(cls, terms, eterms, my_gen_trees_all):
        assert isinstance(terms, list) and terms
        assert isinstance(eterms, list) and eterms
        assert callable(my_gen_trees_all)
        #axioms of the form fun1(..) = fun2(..)        
        
        incompat = lambda lhs, rhs: lhs.outp_typ != rhs.outp_typ
        same_sig = lambda lhs, rhs: lhs.same_sig(rhs)
        impure = lambda lhs, rhs: not rhs.is_pure and  not rhs.is_pure
        filters = [incompat, same_sig, impure]
        
        teqts = []
        scache = set()
        for i, lhs in enumerate(eterms):
            rhss = my_gen_trees_all(terms[:i] + terms[i+1:])
            for rhs in rhss:
                children = (lhs, rhs)
                assert isinstance(lhs, Fun)
                assert isinstance(rhs, Fun)
                
                children_r = (rhs, lhs)
                if children in scache or children_r in scache:
                    continue
                scache.add(children)
                
                if any(f(lhs,rhs) for f in filters):
                    continue

                assert lhs != rhs
                eqt = cls.eq(children)
                teqts.append(eqt)
                    
        logger.info("{} term eqts".format(len(teqts)))
        if teqts:
            logger.debug("\n" + Term.str_of_terms(teqts))        
        #CM.pause()
        return teqts
        
    @classmethod
    def gen_eqts(cls, terms, ignores:set, max_nfuns:int):
        """
        Enumerate eqts of the form  x = y[...]  where x, y are terms
        """
        assert all(isinstance(t, Term) for t in terms), terms
        assert isinstance(ignores, set), ignores
        assert isinstance(max_nfuns, int) and max_nfuns > 0, max_nfuns
        
        tfilters = cls.mk_term_filters(ignores, max_nfuns)
        cache = dict()
        my_gen_trees_all = lambda ts: cls.gen_trees_all(ts, tfilters, cache)
        
        eterms = my_gen_trees_all(terms)
        logger.info("{} enumerated terms".format(len(eterms)))
        logger.debug("\n" + Term.str_of_terms(eterms))

        ceqts = cls.gen_const_eqts(eterms)
        teqts = cls.gen_term_eqts(terms, eterms, my_gen_trees_all)
        return ceqts + teqts

    def is_redundant(self, others):
        """
        #int_0 = pop(push(bool_0, int_0))
        >>> t = EqFun(('eq', '==', (Arg((0, int)), Fun(('pop', 'pop', (Fun(('push', 'push', (Arg((0, bool)), Arg((0, int))), (bool, int), None, frozenset({0}), False)),), (bool,), int, frozenset({0}), False))), (typing.Any, typing.Any), bool, None, True))

        #2. search(bool_0, int_0) = search(bool_0, pop(push(bool_1, int_0)))
        >>> r1 = EqFun(('eq', '==', (Fun(('search', 'search', (Arg((0, bool)), Arg((0, int))), (bool, int), int, None, False)), Fun(('search', 'search', (Arg((0, bool)), Fun(('pop', 'pop', (Fun(('push', 'push', (Arg((0, bool)), Arg((0, int))), (bool, int), None, frozenset({0}), False)),), (bool,), int, frozenset({0}), False))), (bool, int), int, None, False))), (typing.Any, typing.Any), bool, None, True))


        #3. empty(pop(push(bool_0, int_0))) = empty(bool_0)
        >>> r2 = EqFun(('eq', '==', (Fun(('empty', 'empty', (Fun(('pop', 'pop', (Fun(('push', 'push', (Arg((0, bool)), Arg((0, int))), (bool, int), None, frozenset({0}), False)),), (bool,), int, frozenset({0}), False)),), (bool,), bool, None, False)), Fun(('empty', 'empty', (Arg((0, bool)),), (bool,), bool, None, False))), (typing.Any, typing.Any), bool, None, True))

        
        # >>> assert t.is_redundant(set([t]))
        # >>> assert r1.is_redundant(set([t]))
        >>> r2.is_redundant(set([t]))
        
        """

        def f(l,r):
            return self.eq((l, r))

        # print(self)
        # print(list(others)[0])
        
        
        if self.lhs == self.rhs:
            return True

        if self in others:
            return True

        if f(self.lhs, self.rhs) in others:
            return True


        # def same_sig():
        #     return (self.lhs.val == self.rhs.val and
        #             self.lhs.call == self.rhs.call and
        #             len(self.lhs.children) == len(self.rhs.children) and 
        #             self.lhs.inp_typs == self.rhs.inp_typs and
        #             self.lhs.outp_typ == self.rhs.outp_typ and
        #             self.lhs.side_effect_idxs == self.rhs.side_effect_idxs and
        #             self.lhs.is_commute == self.rhs.is_commute)

        
        def same_children():
            return all(f(l,r).is_redundant(others)
                       for l,r in zip(self.lhs.children, self.rhs.children))


        # b1 = same_sig()
        # print("same_sig {}".format(b1))
        
        return self.lhs.same_sig(self.rhs) and same_children()


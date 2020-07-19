import abc
import typing
import itertools
from collections import Counter
import os.path
import copy

import alg_miscs
import vu_common as CM
import config as CC
import mytyp

logger = CM.VLog(os.path.basename(__file__))
logger.level = CC.logger_level
CM.VLog.PRINT_TIME = False

"""
Important,  use == for Typing instead of "is"
>>> t1 = typing.List[typing.Any]
>>> t2 = typing.List[typing.Any]
>>> t1 == t2
True
>>> t1 is t2
False
"""

class IncompatTyp(Exception): pass

class Term(tuple):
    """
    >>> t = Fun(('push', 'push', (Arg((None, str)), Arg((None, int))), (str, int), None, frozenset({0}), False))
    >>> assert len(t.nodes) == 3
    >>> assert t.arg_typs_d == Counter({int: 1, str: 1})
    

    >>> t = Fun(('pop', 'pop', (Arg((None, str)),), (str,), int, frozenset({0}), False))
    >>> assert len(t.nodes) == 2
    >>> assert t.arg_typs_d == Counter({str: 1})

    >>> t = Fun(('peek', 'peek', (Arg((None, str)),), (str,), int, None, False))
    >>> assert len(t.nodes) == 2
    >>> assert t.arg_typs_d == Counter({str: 1})

    >>> t = Fun(('empty', 'empty', (Arg((None, str)),), (str,), bool, None, False))
    >>> assert len(t.nodes) == 2
    >>> assert t.arg_typs_d == Counter({str: 1})

    >>> t = Fun(('pop', 'pop', (Fun(('push', 'push', (Arg((None, int)), Arg((None, int))), (int, int), None, frozenset({0}), False)),), (int,), int, frozenset({0}), False))
    >>> assert len(t.nodes) == 4
    >>> assert t.arg_typs_d == Counter({int: 2})


    >>> t = Fun(('peek', 'peek', (Fun(('push', 'push', (Arg((None, int)), Arg((None, int))), (int, int), None, frozenset({0}), False)),), (int,), int, None, False))
    >>> assert len(t.nodes) == 4
    >>> assert t.arg_typs_d == Counter({int: 2})

    >>> t = Fun(('empty', 'empty', (Fun(('push', 'push', (Arg((None, int)), Arg((None, int))), (int, int), None, frozenset({0}), False)),), (int,), bool, None, False))
    >>> assert len(t.nodes) == 4
    >>> assert t.arg_typs_d == Counter({int: 2})

    >>> t = Fun(('peek', 'peek', (Fun(('pop', 'pop', (Fun(('push', 'push', (Arg((None, int)), Arg((None, int))), (int, int), None, frozenset({0}), False)),), (int,), int, frozenset({0}), False)),), (int,), int, None, False))
    >>> assert len(t.nodes) == 5
    >>> assert t.arg_typs_d == Counter({int: 2})

    >>> t = Fun(('empty', 'empty', (Fun(('pop', 'pop', (Fun(('push', 'push', (Arg((None, int)), Arg((None, int))), (int, int), None, frozenset({0}), False)),), (int,), int, frozenset({0}), False)),), (int,), bool, None, False))
    >>> assert len(t.nodes) == 5
    >>> assert t.arg_typs_d == Counter({int: 2})

    # >>> from eqfun import EqFun
    # >>> t = EqFun(('eq', '==', (Arg((None, int)), Fun(('pop', 'pop', (Fun(('push', 'push', (Arg((None, str)), Arg((None, int))), (str, int), None, frozenset({0}), False)),), (str,), int, frozenset({0}), False))), (typing.Any, typing.Any), bool, None, True))
    # >>> assert t.arg_typs_d == Counter({int: 2, str: 1})
    # >>> t = EqFun(('eq', '==', (Arg((None, int)), Fun(('peek', 'peek', (Fun(('push', 'push', (Arg((None, str)), Arg((None, int))), (str, int), None, frozenset({0}), False)),), (str,), int, None, False))), (typing.Any, typing.Any), bool, None, True))
    # >>> assert t.arg_typs_d ==  Counter({int: 2, str: 1})
    # >>> t = EqFun(('eq', '==', (Arg((None, bool)), Fun(('empty', 'empty', (Fun(('push', 'push', (Arg((None, str)), Arg((None, int))), (str, int), None, frozenset({0}), False)),), (str,), bool, None, False))), (typing.Any, typing.Any), bool, None, True))
    # >>> assert t.arg_typs_d == Counter({int: 1, bool: 1, str: 1})
    # >>> t = EqFun(('eq', '==', (Arg((None, int)), Fun(('peek', 'peek', (Fun(('pop', 'pop', (Fun(('push', 'push', (Arg((None, str)), Arg((None, int))), (str, int), None, frozenset({0}), False)),), (str,), int, frozenset({0}), False)),), (str,), int, None, False))), (typing.Any, typing.Any), bool, None, True))
    # >>> assert t.arg_typs_d == Counter({int: 2, str: 1})
    # >>> t = EqFun(('eq', '==', (Arg((None, bool)), Fun(('empty', 'empty', (Fun(('pop', 'pop', (Fun(('push', 'push', (Arg((None, str)), Arg((None, int))), (str, int), None, frozenset({0}), False)),), (str,), int, frozenset({0}), False)),), (str,), bool, None, False))), (typing.Any, typing.Any), bool, None, True))
    # >>> assert t.arg_typs_d == Counter({int: 1, bool: 1, str: 1})
    """
    
    __metaclass__ = abc.ABCMeta
                     
    def __init__(self, contents):
        assert contents, contents
        tuple.__init__(contents)

        self._val = self[0]
        self._outp_typ = self[1]

    @property
    def val(self): return self._val
    @property
    def outp_typ(self): return self._outp_typ

    #recurse term (tree)
    @property
    def nodes(self) -> list:
        """
        Return all nodes  (args + funs)
        """
        try:
            return self._nodes
        except AttributeError:
            def compute(t, l):
                l.append(t)
                if not isinstance(t, Arg):
                    for c in t.children:
                        compute(c, l)
                
            self._nodes = []
            compute(self, self._nodes)
            return self._nodes

    @property
    def args(self) -> list:
        """
        Return all args in term
        """
        try:
            return self._args
        except AttributeError:
            self._args = [t for t in self.nodes if isinstance(t, Arg)]
            return self._args

    @property
    def funs(self) -> list:
        """
        Return all functions (non-args)
        """
        try:
            return self._funs
        except AttributeError:
            self._funs = [t for t in self.nodes if not isinstance(t, Arg)]
            return self._funs
    
    @property
    def arg_typs_d(self):
        try:
            return self._arg_typs_d
        except AttributeError:
            C = Counter()
            for arg in self.args: C[arg.outp_typ] += 1
            self._arg_typs_d = C
            return self._arg_typs_d

    @property
    def arg_names_d(self):
        try:
            return self._arg_names_d
        except AttributeError:
            def compute(t, s):
                if isinstance(t, Arg):
                    assert isinstance(t.val, int)
                    k = "{}_{}".format(mytyp.MyTyp.name(t.outp_typ), t.val)
                    key = (k, t.outp_typ)
                    s.add(key)
                else:
                    for c in t.children: compute(c, s)
            arg_names_d = set()
            compute(self, arg_names_d)
            self._arg_names_d = sorted(arg_names_d)
            return self._arg_names_d

    def same_sig(self, other):
        """
        Similar in everything except children
        """
        return (self.val == other.val and
                self.call == other.call and
                len(self.children) == len(other.children) and 
                self.inp_typs == other.inp_typs and
                self.outp_typ == other.outp_typ and
                self.side_effect_idxs == other.side_effect_idxs and
                self.is_commute == other.is_commute)

    def gen_code(self, merge_se, typs_d, lang_cls) -> typing.List[tuple]:
        used_vars = Counter()
        return self._gen_code(merge_se, used_vars, typs_d, lang_cls)    
    
    def gen_test_funs(self, mid:str, merge_se:bool, typs_d:dict, 
                      ntests:int, lang_cls) -> (str, str):
        assert not self.is_instantiated
        axioms = [self.instantiate(args_d)
                  for args_d in self.gen_args()]

        codes = []
        for i, axiom in enumerate(axioms):
            code = axiom.gen_code(merge_se, typs_d, lang_cls)
            code = axiom._gen_test_funs(
                "{}_{}".format(mid, i), code, ntests, lang_cls)
            codes.append(code)
            
        return axioms, codes

    def _gen_test_funs(self, mid:str, codes, ntests:int, lang_cls):
        assert self.is_instantiated
        from eqfun import EqFun
        
        fname, fbody = lang_cls.mk_fun_f(
            mid, codes, "testing {}".format(self),
            self.val == EqFun.axiomeq, ntests, self.arg_names_d)
        
        return fname, fbody #("foo()", "code1\ncode2")
    

    def gen_test_funs_soft(self, mid, merge_se:bool, typs_d:dict, ntests:int, lang_cls):
        _, funs = self.gen_test_funs(mid, merge_se, typs_d, ntests, lang_cls)
        fname, fbody = lang_cls.mk_fun("soft_{}".format(mid),
                                       funs, lang_cls.connector_or, None)
        return fname, fbody
    
    @classmethod
    def str_of_terms(cls, terms):
        return '\n'.join("{}. {}".format(i, t) for i, t in enumerate(terms))

    def instantiate(self, typs_d):
        """
        Instantiate leaf to real arguments, e.g., 
        f(int,int) to  f(int_0, int_1) or f(int_0, int_0)
        """
        assert not self.is_instantiated
        return self._instantiate(typs_d, dict((typ, 0) for typ in typs_d))
    
class Arg(Term):
    """
    >>> a1 = Arg((0, int))
    >>> assert str(a1) == "int_0"
    >>> assert str(Arg((None, int))) == "int"
    >>> assert str(repr(a1)) == "Arg((0, int))"
    >>> assert str(Arg((1, typing.List[typing.Any]))) == "Any_List_1"
    """
    def __init__(self, term):
        (val, typ) = term
        assert val is None or (isinstance(val, int) and val >= 0), val
        assert mytyp.MyTyp.is_valid_typ(typ), typ
        
        super(Arg, self).__init__((val, typ))

    #doesn't really matter if is_commute is set to True or False
    #since it doesn't apply
    #so just set ot False to avoid extra work
    @property
    def is_commute(self): return False
    @property
    def nchildren(self): return 0
    
    def __str__(self):
        s = mytyp.MyTyp.name(self.outp_typ)
        if self.val is not None:
            s = '{}_{}'.format(s, self.val)
        return s
    
    def __repr__(self):
        return "{}(({}, {}))".format(
            self.__class__.__name__,
            self.val, mytyp.MyTyp.reprname(self.outp_typ))

    @classmethod
    def mk(cls, typ): return cls((None, typ))

    @property
    def is_instantiated(self):
        try:
            return self._is_instantiated
        except AttributeError:
            self._is_instantiated = isinstance(self.val, int) and self.val >= 0
            return self._is_instantiated

    def _instantiate(self, typs_d, ctr_d):
        idx = ctr_d[self.outp_typ]
        ctr_d[self.outp_typ] += 1
        val = typs_d[self.outp_typ][idx]
        return self.__class__((val, self.outp_typ))

    def _gen_code(self, merge_se, used_vars, typs_d, lang_cls) -> typing.List[tuple]:
        assert isinstance(self, Arg)
        assert self.is_instantiated
        varname = '_'.join(str(self).split())
        varname = lang_cls.mk_var(varname, used_vars)
        code = lang_cls.gen_code_arg(
            varname, self.outp_typ, str(self), typs_d)
        se = {}
        out = (varname, self.outp_typ)
        rs = [([code], se, out)]
        return rs        

    def implies(self, o):
        #todo, only if self. is bounded to forall
        return (self == o or
                (isinstance(o, Arg) and self.outp_typ != o.outp_typ) or
                isinstance(o, Fun))

    def iimplies(self, qfs1, o, qfs2):
        assert self.is_instantiated
        assert o.is_instantiated
        assert isinstance(qfs1, dict), qfs1
        assert isinstance(qfs2, dict), qfs2

        if not(type(self) is type(o) and self.outp_typ == o.outp_typ):
            return False
        
        is_implied = iimplies((self.outp_typ,self.val), qfs1, (o.outp_typ,o.val), qfs2)
        return is_implied

class Fun(Term):
    """
    #any_0 = list.pop(list.append(any list_0,any_0))
    
    >>> arglist = Arg((None, typing.List[typing.Any]))
    >>> argint = Arg((None, int))
    >>> argany = Arg((None, typing.Any))
    >>> children = (arglist, argint, argany)
    >>> inp_typs = ((typing.List[typing.Any], int, typing.Any))
    >>> linsert = Fun(('linsert', 'list.insert', children, inp_typs, None, frozenset({0}), False))
    
    >>> print(linsert)
    linsert(Any_List, int, Any)

    >>> print(repr(linsert))
    Fun(('linsert', 'list.insert', (Arg((None, typing.List[typing.Any])), Arg((None, int)), Arg((None, typing.Any))), (typing.List[typing.Any], int, typing.Any), None, frozenset({0}), False))

    """
    def __init__(self, term):
        (val,   #lpop
         call,  #list.pop
         children,
         inp_typs, outp_typ,
         side_effect_idxs,
         is_commute) = term
         
        assert isinstance(val, str) and val, val
        assert isinstance(call, str) and call, call
        assert isinstance(children, tuple), children
        assert all(isinstance(c, Term) for c in children), children
        assert isinstance(inp_typs, tuple), inp_typs
        assert len(children) == len(inp_typs)
        assert all(mytyp.MyTyp.is_valid_typ(t) for t in inp_typs), inp_typs
        assert mytyp.MyTyp.is_valid_typ(outp_typ), outp_typ
        assert (side_effect_idxs is None
                or (isinstance(side_effect_idxs, frozenset) and side_effect_idxs))
        assert isinstance(is_commute, bool), is_commute
            
        super(Fun, self).__init__(
            (val, outp_typ, call,
             children, inp_typs, 
             side_effect_idxs, is_commute))

        self._call = call
        self._children = children
        self._inp_typs = inp_typs
        self._outp_typ = outp_typ
        self._side_effect_idxs = side_effect_idxs
        self._is_commute = is_commute
        if len(children) <= 1:
            assert not is_commute, self
            
    @property
    def is_commute(self): return self._is_commute
    @property
    def children(self): return self._children
    @property
    def nchildren(self): return len(self.children)
    @property
    def inp_typs(self): return self._inp_typs
    @property
    def outp_typ(self): return self._outp_typ
    @property
    def side_effect_idxs(self): return self._side_effect_idxs
    @property
    def is_pure(self): return not self.side_effect_idxs
    @property
    def call(self): return self._call
        
    def __str__(self):
        s = "{}{}".format(self.val, "*" if self.is_commute else "")
        if not self.children:
            return s
        else:
            return "{}({})".format(s, ', '.join(map(str, self.children)))

    def __repr__(self):
        if len(self.children) == 1:
            children_str = '{},'.format(repr(self.children[0]))
            inp_typs_str = '{},'.format(mytyp.MyTyp.reprname(self.inp_typs[0]))
        else:
            children_str = ', '.join(repr(c) for c in self.children)
            inp_typs_str = ', '.join(mytyp.MyTyp.reprname(t) for t in self.inp_typs)
                                    
        return "{}(('{}', '{}', ({}), ({}), {}, {}, {}))".format(
            self.__class__.__name__,
            self.val, self.call,
            children_str,
            inp_typs_str,
            mytyp.MyTyp.reprname(self.outp_typ),
            self.side_effect_idxs, self.is_commute)

    def _gen_code(self, merge_se:bool, used_vars, typs_d, lang_cls) -> typing.List[tuple]:
        assert self.is_instantiated
        ps = [c._gen_code(merge_se, used_vars, typs_d, lang_cls)
              for c in self.children]
        rs = [tup for p in itertools.product(*ps)
              for tup in self._gc2(p, merge_se, used_vars, typs_d, lang_cls)]
        return rs

    def _gc2(self, ls, merge_se, used_vars, typs_d, lang_cls):
        codes, sideeffects, outs = zip(*ls)

        #merge code
        codes = [code for codes_ in codes for code in codes_]

        acc_side_effects = {}
        if merge_se:
            #merge side effects
            for se in sideeffects:
                for typ in se:
                    if typ not in acc_side_effects:
                        acc_side_effects[typ] = set()
                    acc_side_effects[typ].update(se[typ])

        #create args for foo
        vss = []
        for typ, se, out in zip(self.inp_typs, sideeffects, outs):
            if typ in se:
                vss.append(se[typ])
            else:
                outv, outtyp = out
                assert typ == typing.Any or typ == outtyp
                vss.append([outv])

        rs = [self._gc3(vs, codes, acc_side_effects, used_vars, typs_d, lang_cls)
              for vs in itertools.product(*vss)]

        return rs

    def _gc3(self, vs, codes, acc_side_effects, used_vars, typs_d, lang_cls):
        new_code, out = lang_cls.gen_code_fun_f3(
            self.val, self.call, self.outp_typ,
            vs, used_vars, typs_d)

        #compute side effects
        if acc_side_effects:
            side_effects = copy.deepcopy(acc_side_effects)
        else:
            side_effects = {}
            
        if self.side_effect_idxs:
            for i in self.side_effect_idxs:
                typ, v = self.inp_typs[i], vs[i]
                if typ not in side_effects:
                    side_effects[typ] = set()
                side_effects[typ].add(v)


        return codes + [new_code], side_effects, out
    
    @property
    def is_instantiated(self):
        try:
            return self._is_instantiated
        except AttributeError:
            self._is_instantiated = all(c.is_instantiated for c in self.children)
            return self._is_instantiated

    def _instantiate(self, typs_d, ctr_d):
        children = tuple(c._instantiate(typs_d, ctr_d) for c in self.children)
        return self.__class__((self.val,
                               self.call,
                               children,
                               self.inp_typs,
                               self.outp_typ,
                               self.side_effect_idxs,
                               self.is_commute))
        
    def construct(self, children:tuple):
        assert isinstance(children, tuple) and \
            all(isinstance(c, Term) for c in children), children
        assert self.nchildren == len(children)

        #update type of ground typs
        children_ = []
        for c,t in zip(children, self.inp_typs):
            if isinstance(c, Arg) and c.outp_typ is None:
                children_.append(Arg((c.val, t)))
            else:
                children_.append(c)
        children = tuple(children_)

        #check compatibility
        def compat(c, typ):
            if c.outp_typ == typ:
                return True
            else:
                return (c.side_effect_idxs and
                        any(typ == self.inp_typs[idx]
                            for idx in c.side_effect_idxs))
            
        if all(compat(c, t) for c, t in zip(children, self.inp_typs)):
            return Fun((self.val,
                        self.call,
                        children,
                        self.inp_typs,
                        self.outp_typ,
                        self.side_effect_idxs, 
                        self.is_commute))
        else:
            raise IncompatTyp

    def gen_args(self):
        typs_d = self.arg_typs_d
        d = dict((typ, alg_miscs.gen_args(typs_d[typ])) for typ in typs_d)
        keys, values = d.keys(), d.values()
        combs = itertools.product(*values)
        ds = [dict(zip(keys, comb)) for comb in combs]
        return ds

    def implies(self, o):
        """
        #any_0 = list.pop(list.append(any list_0,any_0))
        #>>> ax1 = Fun(('eq', (Arg((0, 'any')), Fun(('list.pop', (Fun(('list.append', (Arg((0, 'any list')), Arg((0, 'any'))), (('any list', 'any')), 'None', frozenset([0]), False)),), (('any list',)), 'any', frozenset([0]), False))), (('any', 'any')), 'bool', None, True))

        #any_0 = list.pop(list.append(list.insert(any list_0,int_0,any_0),any_0))
        #>>> ax2 = Fun(('eq', (Arg((0, 'any')), Fun(('list.pop', (Fun(('list.append', (Fun(('list.insert', (Arg((0, 'any list')), Arg((0, 'int')), Arg((0, 'any'))), (('any list', 'int', 'any')), 'None', frozenset([0]), False)), Arg((0, 'any'))), (('any list', 'any')), 'None', frozenset([0]), False)),), (('any list',)), 'any', frozenset([0]), False))), (('any', 'any')), 'bool', None, True))

        #>>> assert ax1.implies(ax2)
        #>>> assert ax1.implies(ax1)        
        #>>> assert not ax2.implies(ax1)
        """
        return (self == o
                or (self.val == o.val and
                    self.outp_typ == o.outp_typ
                    and all(c.implies(oc) for c,oc in zip(self.children, o.children))))
    
    def iimplies(self, qfs1, o, qfs2):
        ret = (self == o
               or (self.val == o.val and
                   type(self) is type(o) and 
                   self.outp_typ == o.outp_typ
                   and all(c.iimplies(qfs1, oc, qfs2)
                           for c,oc in
                           zip(self.children, o.children))))
        return ret

    @classmethod
    def gen_trees_all(cls, trees, filter_fs:list, cache:dict):
                      
        """
        Enumerate all possible tree structures from trees by calling 
        gen_trees on each subset of trees of size 1 to |trees|
        """
        assert isinstance(filter_fs, list) and filter_fs
        assert isinstance(cache, dict)

        rs = []
        for i in range(1, len(trees) + 1):
            for strees in itertools.combinations(trees, i):
                trees_ = cls.gen_trees(strees, filter_fs, cache)
                rs.extend(trees_)

        return rs
    
    @classmethod
    def gen_trees(cls, trees:tuple, filter_fs:list, cache:dict):
        """
        Enumerate all possible tree structures from trees.
        I.e., each structure consist of exactly |trees| trees

        # >>> kt1 = Term.mk_simple('a', 2)
        # >>> kt2 = Term.mk_simple('b', 2)
        # >>> map(str, Term.gen_trees([kt1, kt2])) #doctest: +NORMALIZE_WHITESPACE
        # ['a(None,b(None,None))',
        # 'a(b(None,None),None)',
        # 'b(None,a(None,None))',
        # 'b(a(None,None),None)']

        # >>> kt3 = Term.mk_simple('b',3)
        # >>> map(str, Term.gen_trees([kt1, kt3])) #doctest: +NORMALIZE_WHITESPACE
        # ['a(None,b(None,None,None))',
        # 'a(b(None,None,None),None)',
        # 'b(None,None,a(None,None))',
        # 'b(None,a(None,None),None)',
        # 'b(a(None,None),None,None)']
        
        # >>> trees = [map(lambda x: Term.mk_simple(x,nchildren=2,is_commute=False), range(i)) for i in range(7)]
        # >>> [len(Term.gen_trees(ts)) for ts in trees]
        # [1, 1, 4, 30, 336, 5040, 95040]
        """
        assert isinstance(trees, tuple), trees
        assert all(isinstance(tree, Fun) for tree in trees), trees
        assert isinstance(filter_fs, list) and filter_fs        
        assert isinstance(cache, dict)

        if trees in cache:
            #print("cached")
            return cache[trees]
        
        if not trees:
            rs = [Arg.mk(None)]
        else:
            rs = []
            for i in range(len(trees)):
                root = trees[i]
                rest = trees[:i] + trees[i+1:]
                parts = alg_miscs.gen_parts(
                    rest, root.nchildren, root.is_commute)
                for part in parts:
                    ctrees = [cls.gen_trees(p, filter_fs, cache) for p in part]
                    for c in itertools.product(*ctrees):
                        try:
                            tree = root.construct(tuple(c))
                            if any(f(tree) for f in filter_fs):
                                continue
                            
                            rs.append(tree)
                        except IncompatTyp:
                            pass

        if trees not in cache:
            cache[trees] = rs
            
        return rs

    @classmethod
    def mk(cls, val:str, call:str, inp_typs, outp_typ, side_effect_idxs,
           is_commute=False, children=None):
        """
        >>> Fun.mk("lpop", "list.pop", (typing.List[typing.Any],), typing.Any, frozenset({0}), False, None)
        Fun(('lpop', 'list.pop', (Arg((None, typing.List[typing.Any])),), (typing.List[typing.Any],), typing.Any, frozenset({0}), False))
        """
        if children:
            assert isinstance(children, tuple)
            assert len(children) == len(inp_typs)
        else:
            children = tuple(Arg.mk(t) for t in inp_typs)

        if len(inp_typs) <= 1 and is_commute:
            is_commute = False
                
        fun = cls((val, call, children, inp_typs, outp_typ,
                   side_effect_idxs, is_commute))
        return fun

    @classmethod
    def eval_fun_def(cls, fun_def):
        assert mytyp.is_valid_def(fun_def), fun_def

        fun_obj, fun_call, side_effect_idxs = fun_def
        assert all(isinstance(i, int) and i >= 0
                   for i in side_effect_idxs), side_effect_idxs

        val = fun_obj.__name__
        typs = typing.get_type_hints(fun_obj)
        outp_typ = typs['return']
        inp_typs = tuple(typs[arg] for arg in fun_obj.__code__.co_varnames)
        if side_effect_idxs:
            side_effect_idxs = frozenset(side_effect_idxs)
        else:
            side_effect_idxs = None
        fun_term = cls.mk(val, fun_call, inp_typs, outp_typ, side_effect_idxs)
        return fun_term
    
    
def iimplies(v1, qfs1,  v2, qfs2):
    """
    >>> from eqfun import EqFun

    #>>> f1 = EqFun(('eq', '==', (Arg((0, typing.Any)), Fun(('lpop', 'list.pop', (Fun(('linsert', 'list.insert', (Fun(('lextend', 'list.extend', (Arg((0, typing.List[typing.Any])), Fun(('lappend', 'list.append', (Arg((1, typing.List[typing.Any])), Arg((0, typing.Any))), (typing.List[typing.Any], typing.Any), None, frozenset({0}), False))), (typing.List[typing.Any], typing.List[typing.Any]), None, frozenset({0}), False)), Arg((0, int)), Arg((1, typing.Any))), (typing.List[typing.Any], int, typing.Any), None, frozenset({0}), False)),), (typing.List[typing.Any],), typing.Any, frozenset({0}), False))), (typing.Any, typing.Any), bool, None, True))


    #any_0 = lpop(linsert(lextend(any_list_0,lappend(any_list_1,any_0)),int_0,any_1))

    >>> any_0 = Arg((0, typing.Any))

    #lappend(any_list_1,any_0)
    >>> lappend = Fun(('lappend', 'list.append', (Arg((1, typing.List[typing.Any])), Arg((0, typing.Any))), (typing.List[typing.Any], typing.Any), None, frozenset({0}), False))

    #lextend(any_list_0,lappend(any_list_1,any_0))


    #case 3
    >>> qfs1 = {}
    >>> v1 = 'x'
    >>> qfs2 = {}
    >>> v2 = 'x'
    >>> assert iimplies(v1, qfs1, v2, qfs2)

    #case 1
    >>> qfs1 = {'x':0}
    >>> v1 = 'y'
    >>> qfs2 = {'x':0}
    >>> v2 = 'x'
    >>> assert iimplies(v1, qfs1, v2, qfs2)
    >>> assert qfs1 == {'x':0 , 'y':0}

    #case 0
    >>> qfs1 = {'y':0}
    >>> v1 = 'y'
    >>> qfs2 = {'x':0}
    >>> v2 = 'x'
    >>> assert iimplies(v1, qfs1, v2, qfs2)

    >>> qfs1 = {'y':0}
    >>> v1 = 'y'
    >>> qfs2 = {'x':0}
    >>> v2 = 'x'
    >>> assert iimplies(v2, qfs2, v1, qfs1)

    """
    if v2 in qfs2:
        if v1 in qfs1: #case 0
            return qfs2[v2] == qfs1[v1]
        else:  #case 1
            qfs1[v1] = qfs2[v2]  #set so that others will see it
            return True
    else:
        if v1 in qfs1:  #case 2
            #no need to set qfs because this is false, will stop the process
            return False
        else:  #case 3
            qfs1[v1] = qfs2[v2] = len(qfs1) + len(qfs2) #so that others will see it
            return True

if __name__ == "__main__":
    import doctest
    doctest.testmod()

"""
TODO: why pop(push(int_0, MyAny_0)) = int_0  not a candidate?

"""    

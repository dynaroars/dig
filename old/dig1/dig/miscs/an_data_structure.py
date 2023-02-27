from vu_common import isnum, is_iterable, vset, str_of_list
from collections import namedtuple

import itertools
import vu_common as CM

is_scalar = lambda v: not is_iterable(v)
is_output = lambda outp: is_scalar(outp)
is_input = lambda inp: (isinstance(inp,tuple) and 
                        all(CM.isnum(i) for i in inp))

is_fun_or_arr_elem = lambda k,v: (is_output(k) and 
                                  isinstance(v,(list,tuple)) 
                                  and all(is_input(v_) for v_ in v))
is_fun_or_arr = lambda v: (isinstance(v,dict) and 
                           all(is_fun_or_arr_elem(k,v) 
                               for k,v in v.iteritems()))

class IOput(object):
    """
    Represent input and output values to a function/tree.
    For an array, these are array indices

    """
    def __init__(self,inp,outp):
        if __debug__:
            assert is_input(inp),inp
            assert is_output(outp), outp

        self.inp = inp
        self.outp = outp

    def __str__(self):
        return "{} -> {}".format(self.inp,self.outp)

    
    @staticmethod
    def create(iops):
        """short cupt to create a list of in/outputs"""
        if __debug__:
            assert (CM.is_iterable(iops) and 
                    all(isinstance(io,tuple) and
                        len(io)==2 for io in iops)), iops
                        
        return (IOput(i,o) for i,o in iops)


    
class KTree(object):
    """
    sage: t = KTree('a',(),is_commute=True)
    sage: print t, t.is_leaf, t.leaves, t.is_instantiated
    a True ('a',) True

    sage: t = KTree(None,())
    sage: print t, t.is_leaf, t.leaves, t.is_instantiated
    None True (None,) False
    
    sage: t = KTree('a',(KTree(2,()),))
    sage: print t, t.is_leaf, t.leaves, t.is_instantiated
    a(2) False (2,) True

    sage: t = KTree('a',(KTree(2,()),KTree(3,())),is_commute=True)
    sage: print t.__str__(), t.is_leaf, t.leaves, t.is_instantiated
    a*(2,3) False (2, 3) True

    sage: t = KTree.create(('a',(None,None)))
    sage: print t, t.is_leaf, t.leaves, t.is_instantiated
    a(None,None) False (None, None) False

    """
    def __init__(self, root, children, is_commute=False):
        if __debug__:
            assert is_scalar(root), root
            assert isinstance(children,tuple) \
                and all(isinstance(c,KTree) for c in children), children

        self.root = root
        self.children = children
        self.nchildren = len(self.children)
        self.is_leaf = self.nchildren == 0
        self.is_commute = False if self.nchildren <= 1 else is_commute

        self.leaves = KTree.get_leaves(self)
        self.is_instantiated = all(l is not None for l in self.leaves)

    def __str__(self):
        root_s = str(self.root) + ("*" if self.is_commute else "")

        if self.is_leaf:
            return root_s
        else:
            return "{}({})".format(root_s,str_of_list(self.children,","))
                

    def __eq__(self, o):
        """
        sage: KTree('a',(KTree(2,()),KTree(3,())),is_commute=True) == \
        KTree('a',(KTree(2,()),KTree(3,())),is_commute=True)
        True

        sage: KTree('a',(KTree(2,()),KTree(3,())),is_commute=False) == \
        KTree('a',(KTree(2,()),KTree(3,())),is_commute=True)
        False


        sage: KTree('a',(KTree(2,()),KTree(3,())),is_commute=False) == \
        KTree('b',(KTree(2,()),KTree(3,())),is_commute=True)
        False


        sage: KTree('a',(KTree(2,()),KTree('3',()))) == \
        KTree('a',(KTree(2,()),KTree(3,())))
        False

        sage: KTree('a',(KTree(2,()),)) ==  KTree('a',(KTree(2,()),KTree(3,())))
        False

        sage: KTree.create_simple('c',2) == KTree.create_simple('b',2)
        False

        sage: hash(KTree('a',(KTree(2,()),KTree(3,())),is_commute=False)) \
        == hash(KTree('a',(KTree(2,()),KTree(3,())),is_commute=False))
        True

        sage: hash(KTree('a',(KTree(2,()),KTree(3,())),is_commute=False)) \
        == hash(KTree('a',(KTree(2,()),KTree(3,())),is_commute=True))
        False

        """
        return ((self.root,self.children,self.is_commute) ==
                (o.root,o.children,o.is_commute))
               

    def __ne__(self,o):
        return not self.__eq__(o)

    def __hash__(self):
        return hash((self.root,self.children,self.is_commute))


    @staticmethod
    def get_leaves(tree):
        if tree.is_leaf:
            return (tree.root,)
        else:
            leaves = []
            for c in tree.children:
                leaves.extend(KTree.get_leaves(c)) 
            return tuple(leaves)

    @staticmethod
    def create_leaf(val=None):
        """
        sage: print KTree.create_leaf(3)
        3
        sage: print KTree.create_leaf()
        None
        """
        if __debug__:
            assert is_scalar(val),val
            
        return KTree(val,(),is_commute=False)


    @staticmethod
    def create_simple(name,nchildren,is_commute=False):
        """
        sage: print KTree.create_simple('a',3,is_commute=True)
        a*(None,None,None)
        """
        children = tuple(KTree.create_leaf(None) for _ in range(nchildren))
                         
        return KTree(name,children,is_commute)


    @staticmethod
    def create(tree):
        """
        Shortcut to create trees

        sage: print KTree.create(('a',()))
        a
        sage: print KTree.create(('a',(None,None,None)))
        a(None,None,None)
        sage: print KTree.create(('a',(('b',()),)))
        a(b)
        sage: print KTree.create(('a',((2,()),(3,()))))
        a(2,3)
        sage: print KTree.create(('a',((2,()),(3,(None,)))))
        a(2,3(None))
        """
        if is_scalar(tree):
            return KTree.create_leaf(tree)
        else:
            root = tree[0]
            children = tuple(KTree.create(t) for t in tree[1])
            return KTree(root,children)



class KTreeExp(object):
    """
    To manipulate tree expression, e.g., A[i] = C[B[..]][..]
    """

    def __init__(lt,rt):
        assert isinstance(lh,KTree), lh
        assert isinstance(rh,KTree), rh
        self.lt = lt
        self.rt = rt

        

import pdb
import itertools
import functools

from collections import namedtuple, defaultdict, OrderedDict
from collections.abc import Iterable

import sympy
import z3

import settings
import helpers.vcommon as CM
from helpers.miscs import Miscs, MP
from helpers.z3utils import Z3

import infer.inv
import infer.infer


DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.LOGGER_LEVEL)

special_str = "_special"


class NestedArray(infer.inv.Inv):

    def __init__(self, rel, stat=None):
        assert isinstance(rel, str) and rel, rel

        super().__init__(rel, stat)

    @property
    def mystr(self):
        return str(self.inv)

    @staticmethod
    def eval_lambda(inv, idx_info, tc):
        """
        Evaluate array expression p, e.g. p:  A[i,j,k]=B[2i+3j+k]

        if idx_info is specified then only test p on the idxs from idx_info


        Assumes:
        the first array in lambda is the pivot
        lambda A,B,i,j,k: ...  =>  i,j,k  belong to A

        inv = 'lambda B,C,D,i,j: B[i][j]=C[D[2i+3]]'
        returns true if inv is true on tc

        Examples:

        >>> var('a,b,c,i,j')
        (a, b, c, i, j)

        >>> InvArray.eval_lambda('lambda a,b,c,i,j: a[i][j]==2*b[i]+c[j]', None, {'a':[[4,-5],[20,11]],'b':[1,9],'c':[2,-7]})
        True

        >>> InvArray.eval_lambda('lambda c,a,b,xor,i: c[i] == xor(a[i],b[i])', None, {'a': [147, 156, 184, 76], 'b': [51, 26, 247, 189], 'c': [160, 334, 79, 281]})
        False

        >>> InvArray.eval_lambda('lambda c,a,b,xor,i1: c[i1] == xor(a[i1],b[i1])', None, {'a': [147, 156, 184, 76], 'b': [51, 26, 247, 189], 'c': [160, 134, 79, 241]})
        True


        >>> InvArray.eval_lambda('lambda rvu, t, rvu1, rvu0: (rvu[rvu0][rvu1]) + (-t[4*rvu0 + rvu1]) == 0', None, {'t': [28, 131, 11, 85, 133, 46, 179, 20, 227, 148, 225, 197, 38, 221, 221, 126], 'rvu': [[28, 131, 11, 85], [133, 46, 179, 20], [227, 148, 225, 197], [38, 221, 221, 126]]})
        True

        # The following illustrate the use of idxVals,
        # i.e. p is only true under certain array rages

        >>> InvArray.eval_lambda('lambda st, rvu, st0, st1: (-st[st0][st1]) + (rvu[4*st0 + st1]) == 0', None, tc = {'rvu': [28, 131, 11, 85, 193, 124, 103, 215, 66, 26, 68, 54, 176, 102, 15, 237], 'st': [[28, 131, 11, 85, 133, 46, 179, 20, 227, 148, 225, 197, 38, 221, 221, 126], [193, 124, 103, 215, 106, 229, 162, 168, 166, 78, 144, 234, 199, 254, 152, 250], [66, 26, 68, 54, 206, 16, 155, 248, 231, 198, 240, 43, 208, 205, 213, 26], [176, 102, 15, 237, 49, 141, 213, 97, 137, 155, 50, 243, 112, 51, 124, 107]]})
        False

        >>> InvArray.eval_lambda('lambda st, rvu, st0, st1: (-st[st0][st1]) + (rvu[4*st0 + st1]) == 0', idx_info = [{'st0': 0, 'st1': 0}, {'st0': 0, 'st1': 1}, {'st0': 2, 'st1': 2}, {'st0': 2, 'st1': 3}, {'st0': 3, 'st1': 0}, {'st0': 3, 'st1': 1}, {'st0': 3, 'st1': 2}, {'st0': 3, 'st1': 3}, {'st0': 0, 'st1': 2}, {'st0': 0, 'st1': 3}, {'st0': 1, 'st1': 0}, {'st0': 1, 'st1': 1}, {'st0': 1, 'st1': 2}, {'st0': 1, 'st1': 3}, {'st0': 2, 'st1': 0}, {'st0': 2, 'st1': 1}], tc = {'rvu': [28, 131, 11, 85, 193, 124, 103, 215, 66, 26, 68, 54, 176, 102, 15, 237], 'st': [[28, 131, 11, 85, 133, 46, 179, 20, 227, 148, 225, 197, 38, 221, 221, 126], [193, 124, 103, 215, 106, 229, 162, 168, 166, 78, 144, 234, 199, 254, 152, 250], [66, 26, 68, 54, 206, 16, 155, 248, 231, 198, 240, 43, 208, 205, 213, 26], [176, 102, 15, 237, 49, 141, 213, 97, 137, 155, 50, 243, 112, 51, 124, 107]]})
        True

        """

        """
        Note: sage_eval vs eval
        # sage_eval works on str of the format 'lambda x,y: 2*x+y'
        whereas eval works on str of the format 2*x+y directly (no lambda)
        Also, the result of sage_eval can apply on dicts whose keys are str
        e.g.  f(**{'x':2,'y':3})
        whereas the result of eval applies on dict whose keys are variables
        e.g.  f(**{x:2,y:3})
        """

        assert (idx_info is None or
                isinstance(idx_info, list) and
                all(isinstance(v, dict) for v in idx_info)), indx_info
        assert isinstance(tc, dict), tc
        assert all(isinstance(k, str) for k in tc), tc.keys()

        f = eval(inv)
        vs = f.__code__.co_varnames

        arrs = [v for v in vs if v in tc]  # A,B

        from infer.nested_array import ExtFun, MyMiscs
        extfuns = [v for v in vs if v in ExtFun.d]
        idxStr = [v for v in vs if v not in arrs + extfuns]  # i,j,k

        d_tc = {v: tc[v] for v in arrs}
        d_extfun = {v: ExtFun(v).fun for v in extfuns}
        d_ = Miscs.merge_dict([d_tc, d_extfun])

        if idx_info is None:  # obtain idxsVals from the pivot array
            pivotContents = tc[arrs[0]]
            idxVals = [idx for idx, _ in MyMiscs.travel(pivotContents)]
            idx_info = [dict(zip(idxStr, idxV)) for idxV in idxVals]

        ds = [Miscs.merge_dict([d_, idx_info_]) for idx_info_ in idx_info]

        try:
            return all(f(**d) for d in ds)
        except IndexError:
            return False
        except TypeError:
            return False
        except NameError as msg:
            mlog.warn(msg)
            return False

    def test_single_trace(self, trace):
        assert isinstance(trace, data.traces.Trace), trace
        return self.eval_lambda(self.inv, None, trace.mydict)


class Infer(infer.infer._Infer):

    @classmethod
    def gen_from_traces(cls, traces):
        """
        return nested arrays from traces
        """

        tc = list(traces)[0]  # just use 1 trace for inference
        tc = {k: MyMiscs.get_idxs(l) for k, l in zip(
            tc.ss, tc.vs)}  # convert to idx format

        trees = [Tree(a, [None] * len(list(d.items())[0][1]), ExtFun(a).commute)
                 for a, d in tc.items()]
        tasks = AEXP.gen_aexps(trees, XInfo(), tc)

        def f(tasks):
            rs = [a.peelme(tc) for a in tasks]
            return rs

        wrs = MP.run_mp("Apply reachability", tasks, f, settings.DO_MP)

        rels = [NestedArray(ar) for ar in itertools.chain(*wrs)]
        mlog.debug(f"Potential rels: {len(rels)}")
        return rels


class Tree(namedtuple("Tree", ("root", "children", "commute"))):
    """
    leaf: Tree(None,None,False), Tree(x+7,None,False)
    tree: Tree('a',[Tree],False/True)

    >>> assert set([Tree(), Tree()]) == {Tree(root=None, children=[], commute=False)}

    """

    def __new__(cls, root=None, children=[], commute=False):
        assert(root is None or isinstance(root, (str, sympy.Expr))), root
        assert isinstance(children, Iterable), children
        assert isinstance(commute, bool), commute

        if (root is None or Miscs.is_expr(root) or
                (isinstance(root, str) and special_str in root)):  # leaf
            assert not children, children
            assert not commute, commute
        else:
            assert isinstance(children, Iterable) and children, children
            assert all(isinstance(c, Tree) or
                       c is None or
                       (Miscs.is_expr(c) and not c.is_symbol())
                       for c in children), children
            assert isinstance(commute, bool), commute

            children_ = []
            for c in children:
                if isinstance(c, Tree):
                    children_.append(c)
                elif c is None:
                    children_.append(Tree())  # leaf
                else:
                    assert Miscs.is_expr(c), c
                    children_.append(Tree(c))
            children = children_
            commute = False if len(children) <= 1 else commute

        return super().__new__(cls, root, tuple(children), commute)

    @property
    def nchildren(self) -> bool:
        return len(self.children)

    @property
    def is_leaf(self) -> bool:
        return not self.children

    def __str__(self, leaf_content=None):
        """
        Examples:
        >>> t = Tree()
        >>> assert t == Tree(root=None, children=[], commute=False)
        >>> assert str(t) == 'None'
        >>> assert str(Tree('a',[Tree('b',[None]), None])) == 'a[b[None]][None]'
        >>> assert str(Tree('a',[None, None])) == 'a[None][None]'
        >>> assert str(Tree('a',[None,Tree('b',[None])])) == 'a[None][b[None]]'

        # sage: print(Tree({'root':'xor','children':[None, \
        {'root':'b','children':[None]}, {'root':x,'children':[None]}]})
        xor(None,b[None],x[None]))

        >>> assert str(Tree(x**2 + 7)) == 'x^2 + 7'
        >>> assert Tree(x).__str__(leaf_content='hi') == 'hi'
        >>> var('y')
        y
        >>> assert Tree(x).__str__(leaf_content={x:y+7}) == 'y + 7'
        """
        if self.is_leaf:
            if isinstance(leaf_content, dict):  # {x: y+5}
                if Miscs.is_expr(self.root):  # x + 7
                    ret = self.root.xreplace(leaf_content)  # y+12
                else:
                    ret = self.root
            else:
                if leaf_content:
                    assert isinstance(leaf_content, str), leaf_content
                    ret = leaf_content
                else:
                    assert(leaf_content is None), leaf_content
                    ret = self.root
            return str(ret)
        else:
            if self.root in ExtFun.d:
                rs = '({})'.format(','.join(c.__str__(leaf_content)
                                            for c in self.children))
            else:
                rs = ''.join(
                    f"[{c.__str__(leaf_content)}]" for c in self.children)

            return f"{self.root}{rs}"

    def gen_root_trees(self, nodes, vss, blacklist, data):
        """
        Generates trees from nodes whose root is self.root

        blacklist {a: L} disallows a[b[..]] and a[[c..]]
        where {b,c} in L and only allows
        [a[x[..]]] where x is not in L

        so for example if we want to force a to be a Leaf then {a:L}
        where L is all variables (except None).
        This allows the removal of an extra whitelist

        also if we have {a: L} where L is all variablles (except a) then basically
        we disallow the tree with root 'a' since this says 'a' cannot have
        any children (including) leaf.


        Examples

        # sage: t = Tree({'root':'a','children':[None,None]})
        # sage: nodes = [Tree({'root':'b','children':[None,None]})]
        # sage: map(str,t.gen_root_trees(
            nodes, vss=None, blacklist = {}, data={}))
        ['a[b[None][None]][b[None][None]]',
        'a[b[None][None]][None]',
        'a[None][b[None][None]]',
        'a[None][None]']

        # sage: t = Tree({'root':'B','children':[None]})

        # sage: nodes = [ \
        Tree({'root':'C','children':[None,None]}), \
        Tree({'root':'D','children':[None]})]

        # sage: vss=[(8,),(15,),(7,)]
        # sage: data = {'C':{8: [(2, 6)], 10: [(3, 7), (8, 2)], 3: [(1, 2)], 4: [(0, 4)], 2: [(2, 0), (1, 7)]},\
        'D':{8: [(7,)], 1: [(9,)], 2: [(8,)], 3: [(5,)]}, 'B':{8: [(10,), (4,)], 7: [(2,)], 15: [(8,), (3,)]}}

        # sage: map(str,t.gen_root_trees(nodes,vss=vss, blacklist={}, data=data))
        ['B[C[D[None]][None]]', 'B[C[None][None]]', 'B[None]']

        """
        assert (isinstance(nodes, list) and
                all(isinstance(t, Tree) and t.is_node for t in nodes)), nodes

        assert(vss is None or
               (isinstance(vss, list) and
                all(isinstance(v, tuple) for v in vss))), vss

        assert isinstance(blacklist, dict), blacklist

        # print('START!!')
        # print('self', self, len(self.children))
        # print('nodes', ';'.join(map(str, nodes)))
        # print('vss', vss)
        # print('data', data)

        if vss:
            children_vss = MyMiscs.reach(vss, data[self.root])
            if not children_vss:
                # print('no children_vss')
                return []
        else:
            children_vss = [None] * self.nchildren
        # print('children_vss', children_vss)

        if nodes:
            children = nodes + [Tree()]

            children = [c for c in children
                        if self.root not in blacklist or
                        c.root not in blacklist[self.root]]

            # recursive call
            def gt(t, nodes_, vss_):
                if t.is_leaf:
                    return [t]
                else:
                    return t.gen_root_trees(nodes_, vss_, blacklist, data)

            # print('0', len(children), children,
            # len(children_vss), children_vss)
            children = [[gt(c, [node for node in nodes if node != c], vs) for c in children]
                        for vs in children_vss]
            # print('1', len(children), children)
            children = [list(itertools.chain(*c)) for c in children]
            # print('2',  len(children), children)
            # DBG()
            # assert len(children) == len(
            #     self.children), (len(children), len(self.children))

            combs = list(itertools.product(*children))
            # print('combs', len(combs), combs)

            if self.commute:
                """
                (T1, T2, T3) is equiv to (T1, T3, T2)
                """
                combs = list(set(combs))

            rs = [Tree(self.root, list(c), self.commute) for c in combs]
        else:
            rs = [Tree(self.root, [Tree()] * self.nchildren, self.commute)]

        # print('rs',  ';'.join(map(str, rs)))
        return rs

    @property
    def is_node(self):
        """
        >>> assert Tree('a',[None,None]).is_node is True
        >>> assert not Tree('a',[Tree('b',[None]), None]).is_node
        """
        return all(c.is_leaf for c in self.children)

    def get_non_leaf_nodes(self, nodes=[]):
        """
        Returns the *names* of the non-leaves nodes

        # sage: print Tree({'root':'a','children':[None,None]}).get_non_leaf_nodes()
        ['a']

        # sage: Tree({'root':'a','children':[None, \
        {'root':'b','children':[None,None]}, \
        {'root':'c','children':[None]}, \
        {'root':'d','children':[None,None]}]}).get_non_leaf_nodes()
        ['a', 'b', 'c', 'd']
        """
        if self.is_leaf:
            return nodes
        else:
            nodes_ = [c.get_non_leaf_nodes(nodes) for c in self.children]
            nodes = [self.root] + list(itertools.chain(*nodes_))
            return nodes

    def gen_formula(self, v, data):
        """
        Generate a formula recursively to represent the data structure of tree based on
        input value v and data.


        # sage: var('_B_0_C_0__i0 _B_0_C_0__i1')
        (_B_0_C_0__i0, _B_0_C_0__i1)


        # sage: Tree({'root':'B','children':[\
        {'root':'C', 'children':[_B_0_C_0__i0 + 2*_B_0_C_0__i1]}]}).gen_formula(v=81,\
        data = {'C':{0: [(0,), (3,)], 1: [(4,)], 7: [(2,), (5,)], 8: [(6,)], 9: [(1,), (8,)], 17: [(7,)]},\
        'B':{81: [(17,)], 74: [(6,), (8,)], 71: [(5,), (7,)]}})
        _B_0_C_0__i0 + _B_0_C_0__i1*2 == 7


        # sage: Tree({'root':'B','children':[\
        {'root':'C', 'children':[_B_0_C_0__i0 + 2*_B_0_C_0__i1]}]}).gen_formula(v=81, \
        data = {'C':{0: [(0,), (3,)], 1: [(4,)], 7: [(2,), (5,)], 8: [(6,)], 9: [(1,), (8,)], 17: [(7,)]},\
        'B':{81: [(17,), (9,)], 74: [(6,), (8,)], 71: [(5,), (7,)]}})
        Or(_B_0_C_0__i0 + _B_0_C_0__i1*2 == 7,
        Or(_B_0_C_0__i0 + _B_0_C_0__i1*2 == 1,
        _B_0_C_0__i0 + _B_0_C_0__i1*2 == 8))


        # sage: Tree({'root':'add','children':[\
        {'root':'C', 'children':[{'root':'_add_0_C_','children':[100,200]}]},\
        {'root':'D', 'children':[{'root':'_add_1_D_','children':[100,200]}]}]}).gen_formula(v=17, \
        data = {'C':{0:[(0,)],17:[(1,)],8:[(2,)],3:[(3,),(4,)]},\
        'D':{1:[(0,)],9:[(1,),(3,)],0:[(2,)]},\
        'add':{17:[(8,9),(17,0)],8:[(8,0)],12:[(3,9),(0,12)],3:[(3,0)]}})


        """
        if Miscs.is_expr(self.root):
            return Z3.parse(str(self.root)) == v

        elif isinstance(self.root, str) and special_str in self.root:
            # special case {'first_idx':i,'coef':z}
            myroot = self.root.replace(special_str, "")
            mycoef = f"{myroot}0"
            if v == 0:
                t0 = f"{mycoef} == 0"  # coef
                t1 = f"{myroot}1 == 1"  # first_idx
                ret = z3.And([Z3.parse(t0), Z3.parse(t1)])
                return ret
            else:
                return Z3.parse(mycoef) == v
        else:
            try:
                idxs = data[self.root][v]
            except KeyError:  # not reachable, no rel
                return None

            ors = []
            for idx in idxs:
                ands = []
                for v_, t in zip(idx, self.children):
                    p_ = t.gen_formula(v_, data)
                    if p_ is None:
                        ands = []
                        break
                    ands.append(p_)

                if ands:
                    assert len(ands) > 0
                    ands = z3.simplify(Z3._and(
                        [f if z3.is_expr(f) else Z3.parse(str(f)) for f in ands]))
                    ors.append(ands)

            return z3.simplify(Z3._or(ors)) if ors else None

    ##### Static methods for Tree #####

    @staticmethod
    def uniq(trees, tree):
        assert isinstance(trees, list) and all(isinstance(t, Tree)
                                               for t in trees) and trees, trees
        assert isinstance(tree, Tree), tree
        return [t for t in trees if t.root != tree.root]

    @staticmethod
    def gen_trees(nodes, vss, blacklist, data):
        """
        Generates nestings from a set of nodes. E.g., given nodes [a,b,c],
        returns all nestings, e.g. [{a,[b,c],{a,[c,b]}},{b,[a,c]} ..

        Examples:


        # >>> nodes = [Tree('A', [None]),
         Tree('B', [None, None]),
         Tree('C', [None, None, None])]
        print(len(Tree.gen_trees(nodes, None, {}, {})))
        477

        """

        assert isinstance(nodes, list) and \
            all(isinstance(x, Tree) and x.is_node for x in nodes), nodes
        assert vss is None or \
            (isinstance(vss, list) and all(isinstance(v, tuple)
                                           for v in vss)), vss
        assert isinstance(blacklist, dict), blacklist

        trees = [node.gen_root_trees(Tree.uniq(nodes, node), vss, blacklist, data)
                 for node in nodes]
        trees = list(itertools.chain(*trees))
        assert all(isinstance(t, Tree) for t in trees), trees
        return trees


class AEXP(namedtuple("AEXP", ("lt", "rt"))):

    def __new__(cls, lt, rt):
        """
        Initialize AEXP (Array Expression) which has the form left_tree = right_tree,
        e.g.  A[None][None] = B[C[None][None]][D[None]]

        Examples:
        _ = AEXP({'root':'v','children':[None]}, \
        {'root':'a','children':[{'root':'x3','children':[None,None,None]}]})

        # sage: _ = AEXP(Tree({'root':'v','children':[None]}), \
        {'root':'a','children':[{'root':'x3','children':[None,None,None]}]})

        # sage: _ = AEXP({'root':'v','children':[{'root':'a','children':[None]}]}, \
        {'root':'a','children':[{'root':'x3','children':[None,None,None]}]})
        Traceback (most recent call last):
        ...
        AssertionError: left tree has to be a node tree

        """
        assert isinstance(lt, Tree), lt
        assert lt.is_node, lt
        assert isinstance(rt, Tree), rt

        return super().__new__(cls, lt, rt)

    def __str__(self, leaf_content=None, do_lambda=False):
        """
        Returns the str of AEXP

        leaf_content: {},None,str
        Instantiates leaves of rt with leaf_content, e.g. A[x], leaf_info={x:5} => A[5]

        do_lambda: T/F
        Returns a lambda format of array expressions for evaluation

        Examples:
        # sage: a = AEXP(Tree('v', [None]), Tree('a', [Tree('x3', [None, None, None])]))
        # sage: a.__str__()
        'v[i1] == a[x3[(i1)_][(i1)_][(i1)_]]'

        # sage: a.__str__(do_lambda=True)
        'lambda v,a,x3,i1: v[i1] == a[x3[(i1)_][(i1)_][(i1)_]]'

        # sage: a.__str__(leaf_content={x: 5}, do_lambda=True)
        'lambda v,x3,a,i1: v[i1] == a[x3[None][None][12]]'

        # sage: var('y')
        y
        # sage: t1 = Tree('x3', [None, Tree('c', [x-y, None]), x+7])
        # sage: a1 = AEXP(Tree('v', [None]), Tree('a', [t1]))
        # sage: a1.__str__(leaf_content={x: 5, y: 7}, do_lambda=True)
        'v[i1] == a[x3[None][c[-2][None]][12]]'

        """
        l_idxs = [i+1 for i in range(self.lt.nchildren)]
        l_iformat = ''.join(f'[i{i}]' for i in l_idxs)  # [i][j]
        l_aformat = ','.join(f'i{i}' for i in l_idxs)  # i,j

        if leaf_content is None:
            r_idxs = f"({l_aformat})_"
            rt = self.rt.__str__(leaf_content=r_idxs)
        else:
            assert isinstance(leaf_content, dict), leaf_content
            rt = self.rt.__str__(leaf_content=leaf_content)

        rs = f"{self.lt.root}{l_iformat} == {rt}"

        if do_lambda:
            l_idxs_ = ','.join([f'i{li}' for li in l_idxs])
            nodes = OrderedDict((n, None)
                                for n in self.rt.get_non_leaf_nodes())
            nodes = [self.lt.root] + list(nodes)
            lambda_ = f"lambda {','.join(nodes)},{l_aformat}"  # v,a,b,c,i1,i2
            rs = f"{lambda_}: {rs}"
        return rs

    def is_ok(self, xinfo):
        """
        Return True if this aexp is fine. Otherwise, returns False, which marks
        it for pruning.

        e.g., Those that do not contain the input variables
        """

        # all inputs must be in rt
        roots = self.rt.get_non_leaf_nodes()
        rs = all(iv in roots for iv in xinfo.inputs)
        return rs

    def gen_template(self, idxs_vals=None, special=False):
        """
        special = True then it means we only have 1 data to compare against
        thus if the pass in indices of the leaves are 0's  , the result will be  z + 0*i = 0
        which then just gives z = 0, doesn't contribute to anything if we have only 1 data.
        Thus special flag turns the result z + 0*i = 0 into z = 0 and i = 1.

        Examples:

        >>> lt = Tree('R', [None,None,None])
        >>> rt = Tree('add', [Tree('C',[None]), Tree('D', [None])])
        >>> a = AEXP(lt,rt).gen_template()
        >>> assert str(a.lt) == 'R[None][None][None]'
        >>> str(a.rt)
        'add(C[_add_0_C_0__i1*i1 + _add_0_C_0__i2*i2 + _add_0_C_0__i3*i3 + _add_0_C_0__i0],D[_add_1_D_0__i1*i1 + _add_1_D_0__i2*i2 + _add_1_D_0__i3*i3 + _add_1_D_0__i0])'

        >>> lt = Tree('R', [None,None])
        >>> rt = Tree('add', [Tree('C',[None]), Tree('D', [None])])
        >>> a = AEXP(lt,rt).gen_template()
        >>> assert str(a.lt) == 'R[None][None]'
        >>> str(a.rt)
        'add(C[_add_0_C_0__i1*i1 + _add_0_C_0__i2*i2 + _add_0_C_0__i0],D[_add_1_D_0__i1*i1 + _add_1_D_0__i2*i2 + _add_1_D_0__i0])'


        >>> lt = Tree('R', [None,None])
        >>> rt = Tree('add', [None, None])
        >>> a = AEXP(lt,rt).gen_template(idxs_vals=[0,0],special=False)
        >>> assert str(a.lt) == "R[None][None]"
        >>> str(a.rt)
        'add(_add_0__i0,_add_1__i0)'
        """
        assert(not special or
               all(x == 0 for x in idxs_vals)), (special, idxs_vals)

        assert idxs_vals is not None or not special, (idxs_vals, special)

        if idxs_vals is None:
            ts = [1] + [sympy.Symbol(f'i{i+1}')
                        for i in range(self.lt.nchildren)]
        else:
            ts = [1] + list(idxs_vals)

        def rpl(t, tid):
            if t.is_leaf:
                prefix = f"_{'_'.join(map(str, tid))}__i"
                if special:
                    c = f"{prefix}{special_str}"
                else:
                    uks = [sympy.Symbol(prefix + str(i))
                           for i in range(len(ts))]
                    c = sum(map(sympy.prod, zip(uks, ts)))
                return Tree(c)
            else:
                children = [rpl(c, tid + [t.root, i])
                            for i, c in enumerate(t.children)]
                return Tree(t.root, children, t.commute)

        rt = rpl(self.rt, tid=[])
        return AEXP(lt=self.lt, rt=rt)

    def peelme(self, data) -> list:
        """
        Go through each nesting (aexp), generate a SMT formula, and checks its satisfiability.

        Examples:
        # sage: data = {'C':{1: [(5,)], 2: [(4,)], 4: [(6,)], 5: [(1,)], 6: [(2,), (3,)], 8: [(0,)]},\
        'B': {0: [(4,)], 1: [(0,), (3,), (6,)], 7: [(5,)], -3: [(1,)], 5: [(2,)]},\
        'A':{1: [(1,)], -3: [(2,)], 7: [(0,)]}}

        # sage: AEXP({'root':'A','children':[None]}, \
        {'root': 'B','children':[{'root':'C','children':[None]}]}).peelme(data=data)
        ['lambda A,B,C,i1: A[i1] == B[C[2*i1 + 1]]']

        # sage: data = {'C':{0:[(0,),(3,)],9:[(1,),(8,)],7:[(2,),(5,)], 1:[(4,)],8:[(6,)],17:[(7,)]},\
        'B':{71:[(5,),(7,)],74:[(6,),(8,)],81:[(17,)]},\
        'A':{71:[(0,)],74:[(1,)],81:[(2,)]}}
        # sage: AEXP({'root':'A','children':[None]},\
        {'root':'B','children':[{'root':'C','children':[None]}]}).peelme(data=data)
        ['lambda A,B,C,i1: A[i1] == B[C[i1 + 5]]']

        # sage: data = {'A':{17:[(0,0)],8:[(0,1)],12:[(1,0)],3:[(1,1)]},\
        'C':{0:[(0,)],17:[(1,)],8:[(2,)],3:[(3,),(4,)]},\
        'D':{1:[(0,)],9:[(1,),(3,)],0:[(2,)]},\
        'add': {17:[(8,9),(17,0)],8:[(8,0)],12:[(3,9),(0,12)],3:[(3,0)]}}
        # sage: rs = AEXP({'root':'A','children':[None]}, \
        {'root':'add','children':[{'root':'C' , 'children':[None]}, \
        {'root':'D','children':[None]}]}).peelme(data=data)

        # sage: print '\n'.join(sorted(rs,key=str))
        lambda A,add,C,D,i1: A[i1] == add(C[2*i1 + 2],D[1])
        lambda A,add,C,D,i1: A[i1] == add(C[2*i1 + 2],D[3])
        lambda A,add,C,D,i1: A[i1] == add(C[i1 + 2],D[1])
        lambda A,add,C,D,i1: A[i1] == add(C[i1 + 2],D[3])

        """

        vi = [[(v, i) for i in idxs]
              for v, idxs in data[self.lt.root].items()]
        vi = list(itertools.chain(*vi))
        # print(data[self.lt.root])
        # print(vi)
        sts = [self.gen_template(i, len(vi) == 1).rt for _, i in vi]
        formula = Z3._and([rh.gen_formula(v, data)
                           for (v, _), rh in zip(vi, sts)])
        if formula is None:
            return []

        # print('formula', formula)
        models, stat = Z3.get_models(formula, k=10)
        if models is False:  # no model, formula is unsat, i.e. no relation
            return []

        ds = [get_constraints(m, result_as_dict=True) for m in models]
        # generate the full expression
        template = self.gen_template(None, False)
        assert(isinstance(template, AEXP)), template

        rs = [template.__str__(leaf_content=d, do_lambda=True) for d in ds]
        return rs

    ##### Static methods for AEXP #####

    @classmethod
    def gen_aexps(cls, nodes, xinfo, data):
        """
        arrs = [a,b,c]
        returns a=allpostrees(b,c)  , b = allpostrees(a,b)  , etc

        >>> nodes = [Tree('A',[None]), Tree('C',[None]), Tree('B',[None])]
        >>> data = {'A':{1: [(1,)], -3: [(2,)], 7: [(0,)]}, 'B':{0: [(4,)], 1: [(0,), (3,), (6,)], 7: [(5,)], -3: [(1,)], 5: [(2,)]}, 'C': {1: [(5,)], 2: [(4,)], 4: [(6,)], 5: [(1,)], 6: [(2,), (3,)], 8: [(0,)]}}
        >>> aexps = AEXP.gen_aexps(nodes, XInfo(myall=['A', 'B', 'C']), data=data)
        __main__:DEBUG:generate 2 aexps over A,C,B
        0. A[i1] == B[C[(i1)_]]
        1. A[i1] == B[(i1)_]

        >>> aexps = AEXP.gen_aexps(nodes, XInfo(myall=['A', 'B', 'C']), data={})
        __main__:DEBUG:generate 12 aexps over A,C,B
        0. A[i1] == C[B[(i1)_]]
        1. A[i1] == C[(i1)_]
        2. A[i1] == B[C[(i1)_]]
        3. A[i1] == B[(i1)_]
        4. C[i1] == A[B[(i1)_]]
        5. C[i1] == A[(i1)_]
        6. C[i1] == B[A[(i1)_]]
        7. C[i1] == B[(i1)_]
        8. B[i1] == A[C[(i1)_]]
        9. B[i1] == A[(i1)_]
        10. B[i1] == C[A[(i1)_]]
        11. B[i1] == C[(i1)_]


        >>> aexps = AEXP.gen_aexps(nodes, XInfo(myall=['A','B','C'], outputs=['C']), data={})
        __main__:DEBUG:generate 4 aexps over A,C,B
        0. C[i1] == A[B[(i1)_]]
        1. C[i1] == A[(i1)_]
        2. C[i1] == B[A[(i1)_]]
        3. C[i1] == B[(i1)_]

        """
        assert(isinstance(nodes, list) and
               all(isinstance(x, Tree) and x.is_node for x in nodes)), nodes
        assert isinstance(xinfo, XInfo), xinfo

        # Generate nestings
        def _gt(nodes, ln):
            if ln.root not in data:
                vss = None
            else:
                vss = data[ln.root].keys()
                assert all(not isinstance(v, list) for v in vss)
                vss = [tuple([v]) for v in vss]

            rs = Tree.gen_trees(nodes, vss, xinfo.blacklist, data)
            return rs

        def _loop(mynodes, get_others):
            aexps = []
            for i, node in enumerate(mynodes):
                lt = Tree(node.root, [None] * node.nchildren, node.commute)
                others = get_others(node, i)
                nestings = _gt(others, node)
                for nesting in nestings:
                    aexp = AEXP(lt, nesting)
                    aexps.append(aexp)

            # filter out unlikely array expressions
            aexps = [a for a in aexps if a.is_ok(xinfo)]
            return aexps

        # Construct an AEXP

        if xinfo.outputs:
            # x = a[b[...]], x in output vars and a,b not in output vars
            anodes, lnodes = [], []
            for x in nodes:
                (lnodes if x.root in xinfo.outputs else anodes).append(x)
            aexps = _loop(lnodes, lambda node, i: anodes)
        else:
            aexps = _loop(nodes,
                          lambda node, i: Tree.uniq(nodes[: i] + nodes[i+1:], node))

        s = '\n'.join(f'{i}. {a}' for i, a in enumerate(aexps))
        mlog.debug(f"generate {len(aexps)} aexps over "
                   f"{','.join(map(lambda x: str(x.root), nodes))}\n{s}")
        return aexps


class XInfo(namedtuple("XInfo", ("assumes", "consts",
                                 "expects", "extfuns",
                                 "extvars", "inputs",
                                 "outputs", "myall", "myglobals"))):

    def __new__(cls, assumes=[], consts=[],
                expects=[], extfuns=[], extvars=[],
                inputs=[], outputs=[],
                myall=[], myglobals=[]):

        return super().__new__(cls, assumes, consts,
                               expects, extfuns, extvars,
                               inputs, outputs, myall, myglobals)

    @property
    def blacklist(self):
        """
        Use manual inputs to reduce the number of generated nestings

        Examples:

        >>> xinfo = XInfo(myall=['R','A','B','D','E','xor','g'], inputs=['A','B'],outputs=['R'],extfuns=['xor'],myglobals=['g'])
        >>> xinfo.blacklist
        OrderedDict([('A', ['R', 'A', 'B', 'D', 'E', 'xor', 'g']),
                     ('B', ['R', 'A', 'B', 'D', 'E', 'xor', 'g']),
                     ('xor', [None]), ('g', [None]),
                     ('R', ['R', 'A', 'B', 'D', 'E', 'xor', 'g', None])])

        """
        # Inputs must be leaves
        # e.g., a[i] = x[y[i']] is not possible
        # e.g., a[i] = xor[x[i'][y[i']]
        inpleaveseaves = [{inp: self.myall} for inp in self.inputs]

        # Const must be leaves
        constleaves = [{c: self.myall} for c in self.consts]

        # Extfuns are never leaves
        # e.g.,  r[i] = a[b[xor[i'][i']]]  is not possible
        extfuns_not_leaves = [{ef: [None]} for ef in self.extfuns]

        # Globals are never leaves
        globals_not_leaves = [{gv: [None]} for gv in self.myglobals]

        # Outputs should never be part of the tree
        outputs_not_in_tree = [{oup: self.myall + [None]}
                               for oup in self.outputs]

        ds = (inpleaveseaves+constleaves + extfuns_not_leaves +
              globals_not_leaves + outputs_not_in_tree)
        rs = Miscs.merge_dict(ds)

        return rs


class ExtFun(str):

    d = {
        'add': (lambda x, y: QQ(ZZ(x) + ZZ(y)), True),
        'sub': (lambda x, y: QQ(ZZ(x) - ZZ(y)), False),  # not commute
        'xor': (lambda x, y: QQ(ZZ(x).__xor__(ZZ(y))), True),
        'xor_xor': (lambda x, y, z: QQ(ZZ(x).__xor__(ZZ(y)).__xor__(ZZ(z))), True),
        'mod4': (lambda x: QQ(ZZ(x) % 4), True),
        'mod255': (lambda x: QQ(ZZ(x) % 255), True),
        'mul4': (lambda x: QQ(ZZ(x) * 4),  True),
        'div4': (lambda x: QQ(ZZ(x) // 4), True)   # commute ??
    }

    def __new__(cls, fn):
        assert isinstance(fn, str), fn
        return super().__new__(cls, fn.strip())

    @property
    def fun(self):
        """
        >>> assert ExtFun('xor').fun(*[7,15]) == 8
        >>> assert ExtFun('xor').fun(8,9) == 1
        >>> assert ExtFun('xor').fun(18,-9) == -27
        >>> assert ExtFun('sub').fun(128,1) == 127

        >>> ExtFun('sub').fun(0,1)
        -1
        >>> ExtFun('xor').fun(10,128)
        138
        >>> ExtFun('xor').fun(128,10)
        138
        >>> ExtFun('mod4').fun(128)
        0
        >>> ExtFun('mod4').fun(127)
        3
        >>> ExtFun('mod4').fun(1377)
        1
        >>> ExtFun('mod4').fun(1378)
        2
        >>> ExtFun('mod4').fun(1379)
        3
        >>> ExtFun('mod4').fun(1380)
        0
        >>> ExtFun('div4').fun(127)
        31
        >>> ExtFun('div4').fun(128)
        32
        >>> ExtFun('div4').fun(126)
        31
        """
        return ExtFun.d[self][0]

    @property
    def nargs(self):
        """
        Returns the number of function arguments

        Examples:
        >>> ExtFun('sub').nargs
        2
        >>> ExtFun('something').nargs
        Traceback (most recent call last):
        ...
        KeyError: 'something'

        """
        return len(self.fun.__code__.co_varnames)

    @property
    def commute(self):
        """
        Returns true if the function is commutative

        >>> assert not ExtFun('sub').commute
        >>> assert ExtFun('add').commute
        >>> assert not ExtFun('something').commute
        """
        try:
            return ExtFun.d[self][1]
        except KeyError:
            """
            If we don't know anything about the function, then
            the default is non commutative.
            """
            return False

    def gen_data(self, avals, do_dict):
        """
        Note: did not use caching because caching makes it slower.
        Probably because these functions are too simple that
        doesn't worth the caching overhead
        Examples:

        >>> assert ExtFun('add').gen_data([1,7,9,-1], do_dict=False) == set([2, 8, 10, 0, 14, 16, 6, 18, -2, 1, 7, 9, -1])

        >>> assert ExtFun('add').gen_data([[1,7,9,-1]], do_dict=False) == set([2, 8, 10, 0, 14, 16, 6, 18, -2, 1, 7, 9, -1])

        >>> ExtFun('add').gen_data([[1,7,9,-1]],do_dict=True)
        OrderedDict([('add', OrderedDict([(2, [(1, 1)]), (0, [(-1, 1)]), (10, [(1, 9)]), (8, [(-1, 9), (1, 7)]), (-2, [(-1, -1)]), (6, [(-1, 7)]), (18, [(9, 9)]), (16, [(7, 9)]), (14, [(7, 7)])]))])

        >>> assert ExtFun('sub').gen_data([[1,2],[5,6]], do_dict=False) == set([0, -1, -4, -5, 1, -3, 4, 3, 5, 2, 6])


        >>> assert ExtFun('sub').gen_data([[1,2,5,6]], do_dict=False) == set([0, -1, -4, -5, 1, -3, 4, 3, 5, 2, 6])

        >>> assert ExtFun('sub').gen_data([1,2,5,6], do_dict=False) == set([0, -1, -4, -5, 1, -3, 4, 3, 5, 2, 6])

        >>> ExtFun('sub').gen_data([[1,2],[5,6]],do_dict=True)
        OrderedDict([('sub', {0: [(1, 1), (2, 2), (5, 5), (6, 6)], -1: [(1, 2), (5, 6)], -4: [(1, 5), (2, 6)], -5: [(1, 6)], 1: [(2, 1), (6, 5)], -3: [(2, 5)], 4: [(5, 1), (6, 2)], 3: [(5, 2)], 5: [(6, 1)]})])

        # sage: ExtFun('add').gen_data([[1,2,3,4],[5,6],[7,8,9]], do_dict=False)
        [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 1]

        # sage: ExtFun('add').gen_data([[1,2,3,4],[5,6],[7,8,9]], do_dict=True)
        OrderedDict([('add', OrderedDict([(2, [(1, 1)]), (3, [(1, 2)]), (4, [(1, 3), (2, 2)]), (5, [(1, 4), (2, 3)]), (6, [(1, 5), (2, 4), (3, 3)]), (7, [(1, 6), (2, 5), (3, 4)]), (8, [(1, 7), (2, 6), (3, 5), (4, 4)]), (9, [(1, 8), (2, 7), (3, 6), (4, 5)]), (10, [
                    (1, 9), (2, 8), (3, 7), (4, 6), (5, 5)]), (11, [(2, 9), (3, 8), (4, 7), (5, 6)]), (12, [(3, 9), (4, 8), (5, 7), (6, 6)]), (13, [(4, 9), (5, 8), (6, 7)]), (14, [(5, 9), (6, 8), (7, 7)]), (15, [(6, 9), (7, 8)]), (16, [(7, 9), (8, 8)]), (17, [(8, 9)]), (18, [(9, 9)])]))])
        """

        # assert isinstance(avals, Iterable) and not any(
        #     isinstance(v, Iterable) for v in avals), avals

        if any(isinstance(v, Iterable) for v in avals):
            avals = set(itertools.chain(*avals))

        alists = [avals] * self.nargs
        idxs = list(itertools.product(*alists))
        fun_vals = [self.fun(*idx) for idx in idxs]

        if do_dict:  # create dict
            cs = zip(fun_vals, idxs)
            cs = [(fv, tuple(idx)) for (fv, idx) in cs]

            d = Miscs.create_dict(cs)
            if self.commute:
                # [(1,2),(2,1),(2,2)] => [(1,2),(2,2)]
                # print(d)
                def _set(l):
                    return list(set(tuple(sorted(e)) for e in l))

                d = OrderedDict((k, _set(d[k])) for k in d)
            rs = OrderedDict()
            rs[self] = d

            # print('fun: {}, fvals {}, idxs {}'
            #       .format(self, len(d.keys()), len(idxs)))

        else:  # returns fun_vals as well as the orig avals
            rs = set(fun_vals + list(avals))

        return rs

    @staticmethod
    def gen_ef_data(extfuns, avals):
        """
        create representations for extfuns
        Note: the order of F matters (see example below when add,xor,xor_xor gens 63
        but xor,add,xor_xor gens 124.

        Examples

        # sage: mlog.set_level(VLog.DEBUG)
        # sage: rs = ExtFun.gen_ef_data(map(ExtFun,['add','xor','xor_xor']),[1,2,256,9]); len(rs[0].values()[0])
        dig_miscs:Debug:gen_ef_data([add,xor,xor_xor],|avals|=4)
        dig_miscs:Debug:fun: add, fvals 30, idxs 64
        dig_miscs:Debug:fun: xor, fvals 8, idxs 64
        dig_miscs:Debug:fun: xor_xor, fvals 16, idxs 1331
        30

        # sage: rs = ExtFun.gen_ef_data(map(ExtFun,['xor','add','xor_xor']),[1,2,256,9]); len(rs[0].values()[0])
        dig_miscs:Debug:gen_ef_data([xor,add,xor_xor],|avals|=4)
        dig_miscs:Debug:fun: xor, fvals 8, idxs 64
        dig_miscs:Debug:fun: add, fvals 30, idxs 64
        dig_miscs:Debug:fun: xor_xor, fvals 95, idxs 2197
        8
        """

        assert(isinstance(extfuns, list) and extfuns
               and all(isinstance(f, str) for f in extfuns)), extfuns
        assert(isinstance(avals, set) and
               all(isinstance(v, int) for v in avals)), avals

        mlog.debug(
            f"gen_ef_data({','.join(extfuns)},|avals|={len(avals)})")

        avals = list(avals)
        if len(extfuns) == 1:
            F_avals = [avals]
        else:
            # assert vall_uniq(map(lambda f: f, extfuns)), \
            #     'extfuns list cannot contain duplicate'

            F_avals = []
            for i in range(len(extfuns)):
                rest = extfuns[:i]+extfuns[i+1:]
                F_avals_ = ExtFun.get_outvals(tuple(rest), tuple(avals))
                F_avals.append(F_avals_)
            # F_rest = [CM.vsetdiff(extfuns, [f]) for f in extfuns]

            # F_avals = [ExtFun.get_outvals(tuple(fs), tuple(avals))
            #            for fs in F_rest]

        F_d = [fn.gen_data(f_aval, do_dict=True)
               for fn, f_aval in zip(extfuns, F_avals)]

        return F_d

    @classmethod
    def get_outvals(cls, extfuns, avals):
        """
        Recursive function that returns the all possible input values

        [f,g,h],[avals] =>  f(g(h(avals)))

        Examples:

        # sage: ExtFun.get_outvals(tuple(map(ExtFun,['sub'])),tuple([1,2,256]))
        [0, -1, -255, 1, -254, 255, 254, 2, 256]
        # sage: ExtFun.get_outvals(tuple(map(ExtFun,['xor_xor'])),tuple([1,2,256]))
        [1, 2, 256, 259]
        # sage: ExtFun.get_outvals(tuple(map(ExtFun,['xor_xor','add'])),tuple([1,2,256]))
        [2, 3, 257, 4, 258, 512, 1, 256]
        # sage: ExtFun.get_outvals(tuple(map(ExtFun,['add','xor_xor'])),tuple([1,2,256]))
        [1, 2, 256, 259]
        """

        assert extfuns, extfuns
        assert all(isinstance(f, ExtFun) for f in extfuns)

        if len(extfuns) > 1:
            avals = cls.get_outvals(extfuns[1:], avals)
        else:
            avals = extfuns[0].gen_data(avals, do_dict=False)

        return avals

    @classmethod
    def gen_extfuns(cls, tc, xinfo):
        """
        Returns a list of dicts representing extfuns
        The values of the extfuns are customized over the given tc

        Examples:

        # sage: mlog.set_level(VLog.DEBUG)

        # sage: ExtFun.gen_extfuns(tc={'X':[1,7,9,15]}, xinfo={'ExtFun':['add'],'Output':[]})
        dig_miscs:Debug:gen_extfuns: 1 ext funs [add]
        dig_miscs:Debug:gen_ef_data([add],|avals|=4)
        dig_miscs:Debug:fun: add, fvals 9, idxs 16
        [OrderedDict([('add', OrderedDict([(2, [(1, 1)]), (8, [(1, 7)]), (10, [(1, 9)]), (16, [
                     (1, 15), (7, 9)]), (14, [(7, 7)]), (22, [(7, 15)]), (18, [(9, 9)]), (24, [(9, 15)]), (30, [(15, 15)])]))])]


        # sage: _ = ExtFun.gen_extfuns({'x': [0, 1, 3], 'y': [2, 5, 1], 'z': [153, 173, 184, 65]}, \
        {'Output': ['z'], 'ExtFun': ['sub', 'add']})
        dig_miscs:Debug:gen_extfuns: 2 ext funs [sub, add]
        dig_miscs:Debug:gen_ef_data([sub,add],|avals|=5)
        dig_miscs:Debug:fun: sub, fvals 21, idxs 100
        dig_miscs:Debug:fun: add, fvals 21, idxs 121

        # sage: ExtFun.gen_extfuns({'x': [0, 1, 3], 'y': [2, 5, 1], 'z': [153, 173, 184, 65]}, \
        {'Output': ['z'], 'ExtFun': ['xor', 'mod255']})
        dig_miscs:Debug:gen_extfuns: 2 ext funs [xor, mod255]
        dig_miscs:Debug:gen_ef_data([xor,mod255],|avals|=5)
        dig_miscs:Debug:fun: xor, fvals 8, idxs 25
        dig_miscs:Debug:fun: mod255, fvals 8, idxs 8
        [OrderedDict([('xor', OrderedDict([(0, [(2, 2), (5, 5), (1, 1), (0, 0), (3, 3)]), (7, [(2, 5)]), (3, [(2, 1), (0, 3)]), (2, [(2, 0), (1, 3)]), (1, [(2, 3), (1, 0)]), (4, [(5, 1)]), (5, [(5, 0)]), (6, [(5, 3)])]))]),
        OrderedDict([('mod255', OrderedDict([(0, [(0,)]), (7, [(7,)]), (3, [(3,)]), (2, [(2,)]), (1, [(1,)]), (4, [(4,)]), (5, [(5,)]), (6, [(6,)])]))])]


        # sage: ExtFun.gen_extfuns({'x': [0, 1, 3], 'y': [2, 5, 1], 'z': [153, 173, 184, 65]}, \
        {'Output': ['z'], 'ExtFun': ['xor', 'mod255']})
        dig_miscs:Debug:gen_extfuns: 2 ext funs [xor, mod255]
        dig_miscs:Debug:gen_ef_data([xor,mod255],|avals|=5)
        dig_miscs:Debug:fun: xor, fvals 8, idxs 25
        dig_miscs:Debug:fun: mod255, fvals 8, idxs 8
        [OrderedDict([('xor', OrderedDict([(0, [(2, 2), (5, 5), (1, 1), (0, 0), (3, 3)]), (7, [(2, 5)]), (3, [(2, 1), (0, 3)]), (2, [(2, 0), (1, 3)]), (1, [(2, 3), (1, 0)]), (4, [(5, 1)]), (5, [(5, 0)]), (6, [(5, 3)])]))]),
         OrderedDict([('mod255', OrderedDict([(0, [(0,)]), (7, [(7,)]), (3, [(3,)]), (2, [(2,)]), (1, [(1,)]), (4, [(4,)]), (5, [(5,)]), (6, [(6,)])]))])]


        # sage: ExtFun.gen_extfuns({'R':[128,127,126,125], 'N':[128],'x': [0, 7]},{'Output': ['R'], 'ExtFun': ['sub']})
        dig_miscs:Debug:gen_extfuns: 1 ext funs [sub]
        dig_miscs:Debug:gen_ef_data([sub],|avals|=6)
        dig_miscs:Debug:fun: sub, fvals 25, idxs 36
        [OrderedDict([('sub', OrderedDict([(0, [(0, 0), (7, 7), (128, 128), (1, 1), (2, 2), (3, 3)]), (-7, [(0, 7)]), (-128, [(0, 128)]), (-1, [(0, 1), (1, 2), (2, 3)]), (-2, [(0, 2), (1, 3)]), (-3, [(0, 3)]), (7, [(7, 0)]), (-121, [(7, 128)]), (6, [(7, 1)]), (5, [(7, 2)]), (4, [(7, 3)]),
                     (128, [(128, 0)]), (121, [(128, 7)]), (127, [(128, 1)]), (126, [(128, 2)]), (125, [(128, 3)]), (1, [(1, 0), (2, 1), (3, 2)]), (-6, [(1, 7)]), (-127, [(1, 128)]), (2, [(2, 0), (3, 1)]), (-5, [(2, 7)]), (-126, [(2, 128)]), (3, [(3, 0)]), (-4, [(3, 7)]), (-125, [(3, 128)])]))])]


        """
        assert isinstance(tc, dict), tc
        assert isinstance(xinfo, XInfo), xinfo

        # print(xinfo)
        # print(tc.keys())
        # print(tc)
        extfuns = [ExtFun(x) for x in xinfo.extfuns]
        if not extfuns:
            return []

        mlog.debug(f"gen_extfuns: {len(extfuns)} {','.join(extfuns)}")

        # don't consider values of output arrays
        avals = [tc[a] for a in tc if a not in xinfo.outputs]
        # the range of the outputs are also included e.g. R[i] = sub(N,i)
        lo = list(map(len, [tc[a] for a in tc if a in xinfo.outputs]))

        if lo:
            avals = avals + [range(max(lo))]

        avals = set(itertools.chain(*avals))

        # generate new arrays representing external functions
        ds = cls.gen_ef_data(extfuns, avals)

        return ds

    @staticmethod
    def parse_extvar(ev):
        """
        Return a tuple (var, value)

        Examples:
        # sage: ExtFun.parse_extvar('mpi 3.14')
        OrderedDict([(mpi, 157/50)])

        # sage: ExtFun.parse_extvar(' r [1, 2,  3] ')
        OrderedDict([(r, [1, 2, 3])])

        # sage: ExtFun.parse_extvar('0wrongvarname 3')
        Traceback (most recent call last):
        ...
        AssertionError: 0wrongvarname
        """

        assert False, "Not implemented/checked"

        ev = ev.strip()

        assert ev.count(' ') >= 1, ev

        idx = ev.find(' ')

        vname = ev[:idx].strip()
        vname = ReadFile.strToVar(vname)

        vval = ev[idx:].strip()
        vval = ReadFile.formatter(vval)
        vval = ReadFile.strToRatOrList(vval, is_num_val=None)
        return OrderedDict([(vname, vval)])

    @classmethod
    def gen_extvars(cls, xinfo):
        """
        Returns a list of dicts representing extvars

        [{v1: 3.14},  {v2: [1,2,3]}]

        # >>> ExtFun.gen_extvars(XInfo(extvars=['mpi 3.1415', ' t 20.5 ',  'arr [1,[2,3,4]]']))
        dig_miscs:Debug:gen_extvar: 3 ext funs found in xinfo['ExtVar']
        dig_miscs:Detail:mpi 3.1415,  t 20.5 , arr [1,[2,3,4]]
        [OrderedDict([(mpi, 6283/2000)]), OrderedDict([(t, 41/2)]),
                     OrderedDict([(arr, [1, [2, 3, 4]])])]

        >>> ExtFun.gen_extvars(XInfo())
        []
        """

        assert isinstance(xinfo, XInfo), xinfo
        if not xinfo.extvars:
            return []

        extvars = [cls.parse_extvar(e) for e in xinfo.extvars]
        mlog.debug(f"generate {len(extvars)} ext vars: {extvars}")
        return extvars


def get_traces(tcs, ntcs, ntcs_extra):
    """
    ntcs : number of traces
    ntcs_extra : number of extra traces

    Examples:
    ### sage: l=range(10)
    ### sage: mlog.set_level(VLog.DEBUG)

    ### sage: set_random_seed(0)
    ### sage: l1,l2= get_traces(l,7,3); l1,l2,l
    dig_miscs:Debug:Total traces 10, request (ntcs 7, ntcs_extra 3)
    dig_miscs:Debug:mk_traces: |tcs1|=7, |tcs2|=3
    ([5, 9, 8, 6, 7, 3, 2], [0, 4, 1], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9])

    ### sage: mlog.set_level(VLog.WARN)

    ### sage: set_random_seed(0)
    ### sage: l1,l2= get_traces(l,3,7); l1,l2
    ([5, 9, 8], [6, 7, 3, 2, 0, 4, 1])

    ### sage: set_random_seed(0)
    ### sage: l1,l2= get_traces(l,10,2); l1,l2
    ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [])

    ### sage: set_random_seed(0)
    ### sage: l1,l2= get_traces(l,13,3); l1,l2
    ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [])

    ### sage: set_random_seed(0)
    ### sage: l1,l2= get_traces(l,8,5); l1,l2
    ([5, 9, 8, 6, 7, 3, 2, 0], [4, 1])

    ### sage: set_random_seed(0)
    ### sage: l1,l2= get_traces(l,0,3); l1,l2
    ([], [5, 9, 8])

    ### sage: l1,l2= get_traces(l,3,0); l1,l2
    ([3, 0, 2], [])

    """

    assert isinstance(tcs, list) and tcs, tcs
    assert ntcs >= 0, ntcs
    assert ntcs_extra >= 0, ntcs_extra

    print('Total traces {}, '
          'request (ntcs {}, ntcs_extra {})'
          .format(len(tcs), ntcs, ntcs_extra))

    if len(tcs) <= ntcs:
        tcs1 = tcs[:]
        tcs2 = []
    else:
        # preserve the original tcs content
        idxs = range(len(tcs))
        shuffle(idxs)
        tcs1 = [tcs[i] for i in idxs[:ntcs]]
        tcs2 = [tcs[i] for i in idxs[ntcs:ntcs+ntcs_extra]]

    print('mk_traces: |tcs1|={}, |tcs2|={} '
          .format(len(tcs1), len(tcs2)))

    return tcs1, tcs2


class MyMiscs(object):

    @staticmethod
    def keys_to_str(ls):
        """
        Convert key in dictionary to str, {a:5} => {'a' => 5}

        Input: list of dicts (could be some non-dict elem)
        Output: list of dicts with keys as string

        Examples:

        >>> MyMiscs.keys_to_str([{var('a'):5},{var('b'):7},5])
        [{'a': 5}, {'b': 7}, 5]          

        """
        return [{str(k): l[k] for k in l} if isinstance(l, dict) else l
                for l in ls]

    @staticmethod
    def travel(A):
        """
        Examples:

        >>> MyMiscs.travel([1,[0,[5]],8,[8]])
        [([0], 1), ([1, 0], 0), ([1, 1, 0], 5), ([2], 8), ([3, 0], 8)]
        """
        assert isinstance(A, Iterable), A

        def _travel(A, idx, rs):
            for i, c in enumerate(A):
                myi = idx+[i]
                if isinstance(c, list):
                    rs = _travel(c, myi, rs)
                else:
                    rs = rs + [(myi, c)]
            return rs

        return _travel(A, [], [])

    @classmethod
    def get_idxs(cls, A):
        """
        Return the (nested) order of A in dict format where dkey is value v
        of A and the dvalue is the list of indices I of A containing v

        Examples:

        >>> MyMiscs.get_idxs([1,[0,[5]],8,[8]])
        {0: [(1, 0)], 1: [(0,)], 5: [(1, 1, 0)], 8: [(2,), (3, 0)]}

        >>> assert MyMiscs.get_idxs([]) == OrderedDict()
        """

        rs = [(v, tuple(idx)) for idx, v in cls.travel(A)]
        return Miscs.create_dict(rs)

    @staticmethod
    def reach(vss, rdata):
        """
        Checks if values in vss can be found from rdata and performs
        branching if necessary in the case of multiple occurences.

        The output is a list of size == dim of rdata.

        Examples:

        >>> MyMiscs.reach([(8,), (15,), (7,)], rdata = {8:[(10,), (4,)], 15:[(8,), (3,)], 7:[(2,)]})
        [[(10, 4), (8, 3), (2,)]]

        10 is found at either (3,) or (8,), written as (3,8)
        The output is a list of size 1 since the dim of rdata is 1
        >>> MyMiscs.reach([(10,)], rdata = {10:[(3,), (8,)]})
        [[(3, 8)]]

        10 is found at either (3,7) or (8,2), written as [(3,8)],[(7,2)]
        >>> MyMiscs.reach([(10,)], rdata = {10:[(3,7),(8,2)]})
        [[(3, 8)], [(7, 2)]]

        10 or 4 is found at either (3,7),(8,2) or (0,4), written as [(3,8,0)],[(7,2,4)]
        >>> MyMiscs.reach([(10,4)], rdata = {4:[(0,4)], 10:[(3,7),(8,2)]})
        [[(3, 8, 0)], [(7, 2, 4)]]

        10 or 4 is found at either (3,7),(8,2) or (0,4), written as [(3,8,0)],[(7,2,4)]
        8 or 3 is found at either (2,6) or (1,2), written as [(2,1)],[(6,2)]
        2 is found at either (2,0) or (1,7),  written as [(2,1)],[(0,7)]
        all together, written as [[(3,8,0),(2,1),(2,1)], [(7,2,4),(6,2),(0,7)]]
        The output is 2 lists. Each list has 3 (# of inputs) tuples.

        >>> MyMiscs.reach([(10,4),(8,3),(2,)], rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})
        [[(3, 8, 0), (2, 1), (2, 1)], [(7, 2, 4), (6, 2), (0, 7)]]

        >>> sage: MyMiscs.reach([(10,4),(8,3),(8,3)], rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})
        [[(3, 8, 0), (2, 1), (2, 1)], [(7, 2, 4), (6, 2), (6, 2)]]

        >>> MyMiscs.reach([(10,5),(8,3),(2,)], rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})
        [[(3, 8), (2, 1), (2, 1)], [(7, 2), (6, 2), (0, 7)]]

        >>> sage: MyMiscs.reach([(10,4),(8,13),(2,)], rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})
        [[(3, 8, 0), (2,), (2, 1)], [(7, 2, 4), (6,), (0, 7)]]

        >>> MyMiscs.reach([(100,14),(8,13),(2,)], rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})
        []

        >>> MyMiscs.reach([(100,4),(8,13),(2,)], rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})
        [[(0,), (2,), (2, 1)], [(4,), (6,), (0, 7)]]

        >>> MyMiscs.reach([(100,4),(8,13),(100,)], rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})
        []

        """
        assert(isinstance(vss, list) and
               all(isinstance(vs, tuple) for vs in vss)), vss

        rs = [[rdata[v] for v in vs if v in rdata] for vs in vss]
        if any(not r for r in rs):
            return []
        else:
            rs = [itertools.chain(*r) for r in rs]
            rs = [zip(*r) for r in rs]
            rs = zip(*rs)
            rs = [list(r) for r in rs]
            assert len(rs) == len(rdata[list(rdata.keys())[0]][0])
            return rs


def get_constraints(m, result_as_dict=False):
    """
    Input a model m, returns its set of constraints in either 
    1) sage dict {x:7,y:10}  
    1) z3 expr [x==7,y==0]


    # sage: S = z3.Solver()
    # sage: S.add(z3.Int('x') + z3.Int('y') == z3.IntVal('7'))
    # sage: S.check()
    sat
    # sage: M = S.model()
    # sage: SMT_Z3.get_constraints(M,result_as_dict=True)
    {y: 0, x: 7}
    # sage: SMT_Z3.get_constraints(M)
    [y == 0, x == 7]
    # sage: S.reset()

    """

    assert m is not None

    if result_as_dict:  # sage format
        rs = [(sympy.Symbol(str(v())), eval(str(m[v])))
              for v in m]
        rs = dict(rs)

        # assert all(isinstance(x, Miscs.sage_expr) for x in rs.keys())
        # assert all(isinstance(x, Miscs.sage_real)
        #            or isinstance(x, Miscs.sage_int)
        #            for x in rs.values())

    else:  # z3 format
        rs = [v() == m[v] for v in m]
        assert all(z3.is_expr(x) for x in rs)

    return rs

    # @classmethod
    # def mk_template_NOTUSED(cls, terms, rv, prefix=None, ret_coef_vs=False):
    #     """
    #     get a template from terms.
    #     Examples:
    #     # >>> var('a,b,x,y')
    #     (a, b, x, y)
    #     # >>> Miscs.mk_template([1, a, b, x, y],0,prefix=None)
    #     (a*uk_1 + b*uk_2 + uk_3*x + uk_4*y + uk_0 == 0,
    #      a*uk_1 + b*uk_2 + uk_3*x + uk_4*y + uk_0 == 0)
    #     # >>> Miscs.mk_template([1, x, y],0, op=operator.gt,prefix=None,ret_coef_vs=True)
    #     (uk_1*x + uk_2*y + uk_0 > 0, [uk_0, uk_1, uk_2])
    #     # >>> Miscs.mk_template([1, a, b, x, y],None,prefix=None)
    #     (a*uk_1 + b*uk_2 + uk_3*x + uk_4*y + uk_0,
    #      a*uk_1 + b*uk_2 + uk_3*x + uk_4*y + uk_0)
    #     # >>> Miscs.mk_template([1, a, b, x, y],0,prefix='hi')
    #     (a*hi1 + b*hi2 + hi3*x + hi4*y + hi0 == 0,
    #      a*hi1 + b*hi2 + hi3*x + hi4*y + hi0 == 0)
    #     # >>> var('x1')
    #     x1
    #     # >>> Miscs.mk_template([1, a, b, x1, y],0,prefix='x')
    #     Traceback (most recent call last):
    #     ...
    #     AssertionError: name conflict
    #     """

    #     assert rv is not None and isinstance(rv, int), rv

    #     if not prefix:
    #         prefix = "uk_"
    #     uks = [sympy.Symbol(prefix + str(i)) for i in range(len(terms))]

    #     assert not set(terms).intersection(set(uks)), "name conflict"

    #     template = sum(map(sympy.prod, zip(uks, terms)))

    #     if rv != 0:  #
    #         template = template - rv

    #     return template, uks if ret_coef_vs else template

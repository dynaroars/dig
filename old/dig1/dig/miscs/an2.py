from vu_common import isnum, is_iterable, vset
import itertools

"""
Implementations of algorithms for the array/function nesting (AN) problems 
in my thesis.
The structure of the array/function is a k-ary tree, e.g., A[i][j][k] is a 
tree A with 3 children node.
The data of array/function has a dict structure where the key is the output 
of the array/function and the associated value is the list of all inputs 
result in that output.

For example,
The function mult is repr by the dict
{8:[(2,4), (4,2), (1,8), (8,1)],
 4:[(2,2), (1,4), (4,1)],
...
}

Thus, an output is a scalar (int,double, char, etc) while 
an input (arr indices or function arguments) is a tuple of scalars.
"""


is_fun_or_arr_elem = lambda k,v: is_output(k) and \
                     isinstance(v,(list,tuple)) and all(is_input(v_) for v_ in v)
is_fun_or_arr = lambda v: isinstance(v,dict) and \
                all(is_fun_or_arr_elem(k,v) for k,v in v.iteritems())



def result_str(vs):
    tuple_str = lambda ts: "({})".format(",".join(map(str,ts)))
    return "[{}]".format(", ".join(map(tuple_str,vs)))


def sat(vs,a):
    """
    Return a list of inputs resulting in the output values in vss.
    In terms of arrays, this means the indices in the array
    that give the values of vs (e.g., equal to vs)
    
    sage: b = {1:[(0,),(3,),(6,)], -3:[(1,)], 5:[(2,)], 0:[(4,)], 7:[(5,)]}
    sage: list(sat((1,5),b))
    [((0,), (2,)), ((3,), (2,)), ((6,), (2,))]
    sage: list(sat((1,),b))
    [((0,),), ((3,),), ((6,),)]
    sage: list(sat((1,7),b))
    [((0,), (5,)), ((3,), (5,)), ((6,), (5,))]
    sage: list(sat((1,4),b))
    []


    #a = [[7,3], [0,5]]
    #b = [[5,1,2],[7,3],[0,5]]
    #c = [1,2,8,1]
    sage: a = {7:[(0,0)],3:[(0,1)],0:[(1,0)],5:[(1,1)]}
    sage: b = {5:[(0,0), (2,1)], 1:[(0,1)], 2:[(0,2)], 7:[(1,0)], 3:[(1,1)], 0:[(2,0)]}
    sage: c = {1:[(0,),(3,)],2:[(1,),(2,)]}
    sage: data = {'a':a,'b':b, 'c':c}
    sage: result_str(reach([7,3,0],KTree.create(('b',[('c',[None])])),data))
    '[(b[c[0]],b[c[0]],b[c[1]]), (b[c[0]],b[c[0]],b[c[2]]), (b[c[0]],b[c[3]],b[c[1]]), (b[c[0]],b[c[3]],b[c[2]]), (b[c[3]],b[c[0]],b[c[1]]), (b[c[3]],b[c[0]],b[c[2]]), (b[c[3]],b[c[3]],b[c[1]]), (b[c[3]],b[c[3]],b[c[2]])]'

    sage: result_str(reach([7,3,5],KTree.create(('b',[('c',[None])])),data))
    '[(b[c[0]],b[c[0]],b[c[1]]), (b[c[0]],b[c[0]],b[c[2]]), (b[c[0]],b[c[3]],b[c[1]]), (b[c[0]],b[c[3]],b[c[2]]), (b[c[3]],b[c[0]],b[c[1]]), (b[c[3]],b[c[0]],b[c[2]]), (b[c[3]],b[c[3]],b[c[1]]), (b[c[3]],b[c[3]],b[c[2]])]'

    sage: result_str(reach([7,3,5],KTree.create(('b',[('c',[])])),data))
    '[(b[1],b[1],b[0]), (b[1],b[1],b[2])]'
    """

    assert is_iterable(vs) and all(is_scalar(v) for v in vs), vs
    assert is_fun_or_arr(a), a

    try:
        return itertools.product(*(a[v] for v in vs))
    except KeyError:
        return []


def reach(vs,tree,data):
    """
    sage: a = {7: [(0,)], 1:[(1,)], -3:[(2,)]}
    sage: b = {1: [(0,),(3,),(6,)], -3:[(1,)], 5:[(2,)], 0:[(4,)], 7:[(5,)]}
    sage: c = {8: [(0,)], 5:[(1,)], 6:[(2,), (3,)], 2:[(4,)], 1:[(5,)], 4:[(6,)]}
    sage: data = {'a':a, 'b': b, 'c':c}
    
    sage: result_str(reach([7],KTree.create(('b',[('c',[None])])),data))
    '[(b[c[1]])]'

    sage: result_str(reach([7,1],KTree.create(('b',[('c',[None])])),data))
    '[(b[c[1]],b[c[2]]), (b[c[1]],b[c[3]])]'
    
    sage: result_str(reach([7,1,-3],KTree.create(('b',[('c',[None])])),data))
    '[(b[c[1]],b[c[2]],b[c[5]]), (b[c[1]],b[c[3]],b[c[5]])]'

    sage: result_str(reach([7,1,-3,'notexist'],KTree.create(('b',[('c',[None])])),data))
    '[]'
    sage: result_str(reach([7,1,-3,100],KTree.create(('b',[('c',[None])])),data))
    '[]'
    """
    if tree.is_leaf: 
        return [tuple(KTree(v,[]) for v in vs)]

    ss = sat(vs,data[tree.root])
    rs = []
    for s in ss:
        gs = []
        for z,c in zip(zip(*s),tree.children):  #z=(1,2,8)
            gs_ = reach(z,c,data)
            gs.append(gs_)

        rs_ = comb_results(tree.root, gs)
        rs.extend(rs_)
    return rs


def comb_results(root,vs):
    """
    Note |vs| = |root.children|

    sage: l = [tuple(map(KTree.create, [1,2,8]))]
    sage: r = map(lambda l: tuple(map(KTree.create,l)), [[9,7,4],[0,5,6]])

    sage: result_str(comb_results('a',[l,r]))
    '[(a[1,9],a[2,7],a[8,4]), (a[1,0],a[2,5],a[8,6])]'
    """
    combs = itertools.product(*vs)
    return (tuple(KTree(root,z) for z in zip(*c)) for c in combs)
        



###### GENERATING COUNTING TREES #####
def gen_count_ktrees_ordered(trees, is_commute=False):
    """
    When nchildren = 2
    sage: [len(gen_count_ktrees_ordered(range(i))) for i in range(7)]
    [1, 1, 4, 30, 336, 5040, 95040]
    """

    if len(trees) == 0: return [None]

    rs = []
    for i in range(len(trees)):
        root = trees[i]
        rest = trees[:i] + trees[i+1:]
        nchildren = 2
        parts = gen_nodes_parts(rest,nchildren,is_commute)
        for part in parts:
            ctrees = [gen_count_ktrees_ordered2(p) for p in part]
            rs_ = [tuple([root] + list(c))
                   for c in itertools.product(*ctrees)]
            rs.extend(rs_)         
   
    return rs




def enum_nestings(trees, data):
    """
    Enumerate nestings, i.e., counting trees, of size l
    """

    rs = (itertools.combinations(vs,l) for l in range(len(trees)))
    
        


def denum_nestings_l(trees, l, data):
    return itertools.combinations(trees,l)

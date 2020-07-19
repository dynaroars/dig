import itertools
import vu_common as CM
from sageutil import is_sage_expr
from an_data_structure import KTree, IOput, is_scalar

##### Reachability Analysis #####
"""
A[i][j] = 3B[2C[i+1][i+j]-7]+5

A = [[47,5,128],[137,59,59]]
B = [8,0,25,18,40,48,46,14,25,44,9,13,7,41]
C = [[2,-11,1,91],[7,4,10,-5],[8,8,5,5]]

A = {
(0,0):47,
(0,1):5,
(0,2):128,
(1,0):137,
(1,1):59,
(1,2):59
}

B = {
(0,):8,
(1,):0,
(2,):25,
(3,):18,
(4,):40,
(5,):48,
(6,):46,
(7,):14,
(8,):25,
(9,):44,
(10,):9,
(11,):13,
(12,):7,
(13,):41
}


C = {
(0,0):2,
(0,1):-11,
(0,2):1,
(0,3):91,
(1,0):7,
(1,1):4,
(1,2):10,
(1,3):-5,
(2,0):8,
(2,1):8,
(2,2):5,
(2,3):5}

"""
def solve_eqts(avs,bvs,c,d):
    """
    solve for c,d in a[i] = c+d*b[i]
    #[5 = c+d*0, 137 = c + d*44, 59 = c+d*18] => c=5,d=3

    sage: c,d = var('c d')
    sage: rs = solve_eqts([5,137,59],[0,44,18],c,d)
    sage: rs[c], rs[d]
    (3, 5)
    """
    if __debug__:
        assert (isinstance(avs,(tuple,list)) and 
                all(is_scalar(v) and CM.isnum(v) for v in avs)), avs
        assert (isinstance(bvs,(tuple,list)) and 
                all(is_scalar(v) and CM.isnum(v) for v in bvs)), bvs
        assert len(avs) == len(bvs)
        assert is_sage_expr(c),c
        assert is_sage_expr(d),d
        
    
    eqts = [a == d + c*b for a,b in zip(avs,bvs)]
    
    try:
        sol = solve(eqts,c,d,solution_dict=True)
        if len(sol) >= 2:
            print '{} results {} sols {}'.format(eqts,len(sol),sol)

        return sol[0]
    except Exception:
        return None

def sat2(vs,iops):
    """
    Inputs
    vs = [nums]
    a = [IOput]

    Output:
    [(t,u)] 
    where t is a tuple of size |vs| 
    and u is a dict (of sol)

    EXAMPLES: 

    #A[i] = B[i]+3
    A=[10,11,5]
    B=[7,8,2]

    sage: iops = list(IOput.create([((0,),7), ((1,),8), ((2,),2)]))

    sage: print str_of_sat2rs(sat2([10,11,5],iops))
    (0,) -> 7 (1,) -> 8 (2,) -> 2 has sol 'c:1, d:3'

    sage: print str_of_sat2rs(sat2([11,5],iops))
    (0,) -> 7 (1,) -> 8 has sol 'c:-6, d:53'
    (0,) -> 7 (2,) -> 2 has sol 'c:6/5, d:13/5'
    (1,) -> 8 (0,) -> 7 has sol 'c:6, d:-37'
    (1,) -> 8 (2,) -> 2 has sol 'c:1, d:3'
    (2,) -> 2 (0,) -> 7 has sol 'c:-6/5, d:67/5'
    (2,) -> 2 (1,) -> 8 has sol 'c:-1, d:13'

    sage: print str_of_sat2rs(sat2([10,11],iops))
    (0,) -> 7 (1,) -> 8 has sol 'c:1, d:3'
    (0,) -> 7 (2,) -> 2 has sol 'c:-1/5, d:57/5'
    (1,) -> 8 (0,) -> 7 has sol 'c:-1, d:18'
    (1,) -> 8 (2,) -> 2 has sol 'c:-1/6, d:34/3'
    (2,) -> 2 (0,) -> 7 has sol 'c:1/5, d:48/5'
    (2,) -> 2 (1,) -> 8 has sol 'c:1/6, d:29/3'

    #A[i][j] = 3B[2C[i+1][i+j]-7]+5
    A = [[47,5,128],[137,59,59]]
    B = [8,0,25,18,40,48,46,14,25,44,9,13,7,41]
    C = [[2,-11,1,91],[7,4,10,-5],[8,8,5,5]]
    
    sage: iops_b = list(IOput.create([\
    ((0,),8),\
    ((1,),0),\
    ((2,),25),\
    ((3,),18),\
    ((4,),40),\
    ((5,),48),\
    ((6,),46),\
    ((7,),14),\
    ((8,),25),\
    ((9,),44),\
    ((10,),9),\
    ((11,),13),\
    ((12,),7),\
    ((13,),41)\
    ]))

    #take a long time bc 2184 permutations
    #sage: print str_of_sat2rs(sat2([5,137,59],iops_b))
    (1,) -> 0 (9,) -> 44 (3,) -> 18 has sol 'c:3, d:5'

    sage: iops_c = list(IOput.create([\
    ((0,0),2),   \
    ((0,1),-11), \
    ((0,2),1),   \
    ((0,3),91),  \
    ((1,0),7),   \
    ((1,1),4),   \
    ((1,2),10),  \
    ((1,3),-5),  \
    ((2,0),8),   \
    ((2,1),8),   \
    ((2,2),5),   \
    ((2,3),5)    \
    ])) 

    1,9,3 ,  C[1][1], C[2][1], C[2][3]  

    #sage: print str_of_sat2rs(sat2([1,9,3],iops_c))
    (0, 0) -> 2 (1, 2) -> 10 (1, 1) -> 4 has sol 'c:1, d:-1'
    (0, 2) -> 1 (2, 2) -> 5 (0, 0) -> 2 has sol 'c:2, d:-1'
    (0, 2) -> 1 (2, 3) -> 5 (0, 0) -> 2 has sol 'c:2, d:-1'
    (1, 0) -> 7 (1, 3) -> -5 (1, 1) -> 4 has sol 'c:-2/3, d:17/3'
    (1, 1) -> 4 (2, 0) -> 8 (2, 2) -> 5 has sol 'c:2, d:-7'
    (1, 1) -> 4 (2, 0) -> 8 (2, 3) -> 5 has sol 'c:2, d:-7'
    (1, 1) -> 4 (2, 1) -> 8 (2, 2) -> 5 has sol 'c:2, d:-7'
    (1, 1) -> 4 (2, 1) -> 8 (2, 3) -> 5 has sol 'c:2, d:-7'
    (1, 2) -> 10 (0, 0) -> 2 (2, 0) -> 8 has sol 'c:-1, d:11'
    (1, 2) -> 10 (0, 0) -> 2 (2, 1) -> 8 has sol 'c:-1, d:11'
    (2, 0) -> 8 (1, 1) -> 4 (1, 0) -> 7 has sol 'c:-2, d:17'
    (2, 1) -> 8 (1, 1) -> 4 (1, 0) -> 7 has sol 'c:-2, d:17'
    (2, 2) -> 5 (0, 1) -> -11 (0, 2) -> 1 has sol 'c:-1/2, d:7/2'
    (2, 2) -> 5 (0, 2) -> 1 (1, 1) -> 4 has sol 'c:-2, d:11'
    (2, 3) -> 5 (0, 1) -> -11 (0, 2) -> 1 has sol 'c:-1/2, d:7/2'
    (2, 3) -> 5 (0, 2) -> 1 (1, 1) -> 4 has sol 'c:-2, d:11'
    """
    assert (isinstance(vs,(tuple,list)) and 
            all(is_scalar(v) and CM.isnum(v) for v in vs)), vs
    assert CM.is_iterable(iops), iops

    rs = []
    c,d = var('c d')
    
    for iops in itertools.permutations(iops,len(vs)):
        outps = [io.outp for io in iops]
        sol = solve_eqts(vs,outps,c,d)
        if sol:
            rs.append((iops,sol))
    
    return rs

def str_of_sat2rs(rs):
    f = lambda v: " ".join(map(str,v))

    #[(c,1), (d,3)]
    g = lambda v: sorted(tuple(v.iteritems()), key=lambda x:str(x[0]))
    h = lambda v: ", ".join(("{}:{}".format(c,d) for c,d in v))
    hg = lambda v: "'{}'".format(h(g(v)))

    return "\n".join("{} has sol {}".format(f(r[0]),hg(r[1])) for r in rs)


# def sat(vs,a):
#     """
#     Return a list of inputs resulting in the output values in vss.
#     In terms of arrays, this means the indices in the array
#     that give the values of vs (e.g., equal to vs)
    
#     sage: b = {1:[(0,),(3,),(6,)], -3:[(1,)], 5:[(2,)], 0:[(4,)], 7:[(5,)]}
#     sage: list(sat((1,5),b))
#     [((0,), (2,)), ((3,), (2,)), ((6,), (2,))]
#     sage: list(sat((1,),b))
#     [((0,),), ((3,),), ((6,),)]
#     sage: list(sat((1,7),b))
#     [((0,), (5,)), ((3,), (5,)), ((6,), (5,))]
#     sage: list(sat((1,4),b))
#     []


#     #a = [[7,3], [0,5]]
#     #b = [[5,1,2],[7,3],[0,5]]
#     #c = [1,2,8,1]
#     sage: a = {7:[(0,0)],3:[(0,1)],0:[(1,0)],5:[(1,1)]}
#     sage: b = {5:[(0,0), (2,1)], 1:[(0,1)], 2:[(0,2)], 7:[(1,0)], 3:[(1,1)], 0:[(2,0)]}
#     sage: c = {1:[(0,),(3,)],2:[(1,),(2,)]}
#     sage: data = {'a':a,'b':b, 'c':c}
#     sage: result_str(reach([7,3,0],KTree.create(('b',[('c',[None])])),data))
#     '[(b[c[0]],b[c[0]],b[c[1]]), (b[c[0]],b[c[0]],b[c[2]]), (b[c[0]],b[c[3]],b[c[1]]), (b[c[0]],b[c[3]],b[c[2]]), (b[c[3]],b[c[0]],b[c[1]]), (b[c[3]],b[c[0]],b[c[2]]), (b[c[3]],b[c[3]],b[c[1]]), (b[c[3]],b[c[3]],b[c[2]])]'

#     sage: result_str(reach([7,3,5],KTree.create(('b',[('c',[None])])),data))
#     '[(b[c[0]],b[c[0]],b[c[1]]), (b[c[0]],b[c[0]],b[c[2]]), (b[c[0]],b[c[3]],b[c[1]]), (b[c[0]],b[c[3]],b[c[2]]), (b[c[3]],b[c[0]],b[c[1]]), (b[c[3]],b[c[0]],b[c[2]]), (b[c[3]],b[c[3]],b[c[1]]), (b[c[3]],b[c[3]],b[c[2]])]'

#     sage: result_str(reach([7,3,5],KTree.create(('b',[('c',[])])),data))
#     '[(b[1],b[1],b[0]), (b[1],b[1],b[2])]'
#     """

#     assert CM.is_iterable(vs) and all(is_scalar(v) for v in vs), vs
#     assert is_fun_or_arr(a), a

#     try:
#         return itertools.product(*(a[v] for v in vs))
#     except KeyError:
#         return []


# def reach(vs,tree,data):
#     """
#     sage: a = {7: [(0,)], 1:[(1,)], -3:[(2,)]}
#     sage: b = {1: [(0,),(3,),(6,)], -3:[(1,)], 5:[(2,)], 0:[(4,)], 7:[(5,)]}
#     sage: c = {8: [(0,)], 5:[(1,)], 6:[(2,), (3,)], 2:[(4,)], \
#     1:[(5,)], 4:[(6,)]}
#     sage: data = {'a':a, 'b': b, 'c':c}
    
#     sage: result_str(reach([7],KTree.create(('b',[('c',[None])])),data))
#     '[(b[c[1]])]'

#     sage: result_str(reach([7,1],KTree.create(('b',[('c',[None])])),data))
#     '[(b[c[1]],b[c[2]]), (b[c[1]],b[c[3]])]'
    
#     sage: result_str(reach([7,1,-3],KTree.create(('b',[('c',[None])])),data))
#     '[(b[c[1]],b[c[2]],b[c[5]]), (b[c[1]],b[c[3]],b[c[5]])]'

#     sage: result_str(reach([7,1,-3,'notexist'],KTree.create(('b',[('c',[None])])),data))
#     '[]'
#     sage: result_str(reach([7,1,-3,100],\
#     KTree.create(('b',[('c',[None])])),data))
#     '[]'
#     """
#     if tree.is_leaf: 
#         return [tuple(KTree(v,[]) for v in vs)]

#     ss = sat(vs,data[tree.root])
#     rs = []
#     for s in ss:
#         gs = []
#         for z,c in zip(zip(*s),tree.children):  #z=(1,2,8)
#             gs_ = reach(z,c,data)
#             gs.append(gs_)

#         rs_ = comb_results(tree.root, gs)
#         rs.extend(rs_)
#     return rs


# def comb_results(root,vs):
#     """
#     Note |vs| = |root.children|

#     sage: l = [tuple(map(KTree.create, [1,2,8]))]
#     sage: r = map(lambda l: tuple(map(KTree.create,l)), [[9,7,4],[0,5,6]])

#     sage: result_str(comb_results('a',[l,r]))
#     '[(a[1,9],a[2,7],a[8,4]), (a[1,0],a[2,5],a[8,6])]'
#     """
#     combs = itertools.product(*vs)
#     return (tuple(KTree(root,z) for z in zip(*c)) for c in combs)





# ##### #####
def result_str(vs):
    tuple_str = lambda ts: "({})".format(",".join(map(str,ts)))
    return "[{}]".format(", ".join(map(tuple_str,vs)))


# def enum_count_trees_combs(trees,data):
#     """
#     sage: at = KTree.create(('a',[None]))
#     sage: bt = KTree.create(('b',[None]))
#     sage: ct = KTree.create(('c',[None]))
#     sage: trees = [at,bt,ct]

#     sage: a = {7: [(0,)], 1:[(1,)], -3:[(2,)]}
#     sage: b = {1: [(0,),(3,),(6,)], -3:[(1,)], 5:[(2,)], 0:[(4,)], 7:[(5,)]}
#     sage: c = {8: [(0,)], 5:[(1,)], 6:[(2,), (3,)], 2:[(4,)], \
#     1:[(5,)], 4:[(6,)]}
#     sage: data = {'a':a, 'b': b, 'c':c}


#     """
#     assert all(isinstance(tree,KTree) for tree in trees), trees
#     assert all(is_fun_or_arr(d) for d in data.itervalues()), data

#     rs = []
#     for i in range(len(trees)):
#         lh_tree = trees[i]
#         rh_trees = trees[:i] + trees[i+1:]
#         ctrees = gen_count_ktrees_ordered(rh_trees)

#         lh_vs = data[lh_tree.root].keys()
#         crs = []
#         for ctree in ctrees:
#             crs_ = reach(lh_vs,ctree,data)
#             crs.extend(crs_)

#         rs_ = (lh_tree,lh_vs,crs)
#         rs.append(rs_)

#     return rs




            

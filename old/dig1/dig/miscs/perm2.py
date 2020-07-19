import vu_common as CM
import itertools

class BTree(object):
    def __init__(self,name,children):
        self.name = name
        self.children = children
        self.nchildren = len(children)

    def __str__(self):
        if self.name is None:
            return "Leaf"
        else:
            s = ",".join("%s".format(c) for c in self.children)
            return "%s[s]".format(self.name,s)

def gen_nodes_parts(nodes, k, is_commute=False):
    """
    Divides n nodes into k parts

    sage: gen_nodes_parts([],5)
    [([], [], [], [], [])]
    sage: gen_nodes_parts([1,2,3],0)
    []
    sage: gen_nodes_parts([1,2],1)
    [([1, 2],)]
    sage: gen_nodes_parts([1,2],2)
    [([], [1, 2]), ([1], [2]), ([2], [1]), ([1, 2], [])]
    sage: gen_nodes_parts([1,2],3)
    [([], [], [1, 2]),
    ([], [1], [2]),
    ([], [2], [1]),
    ([], [1, 2], []),
    ([1], [], [2]),
    ([1], [2], []),
    ([2], [], [1]),
    ([2], [1], []),
    ([1, 2], [], [])]
    sage: gen_nodes_parts([1,2,4],3)
    [([], [], [1, 2, 4]),
    ([], [1], [2, 4]),
    ([], [2], [1, 4]),
    ([], [4], [1, 2]),
    ([], [1, 2], [4]),
    ([], [1, 4], [2]),
    ([], [2, 4], [1]),
    ([], [1, 2, 4], []),
    ([1], [], [2, 4]),
    ([1], [2], [4]),
    ([1], [4], [2]),
    ([1], [2, 4], []),
    ([2], [], [1, 4]),
    ([2], [1], [4]),
    ([2], [4], [1]),
    ([2], [1, 4], []),
    ([4], [], [1, 2]),
    ([4], [1], [2]),
    ([4], [2], [1]),
    ([4], [1, 2], []),
    ([1, 2], [], [4]),
    ([1, 2], [4], []),
    ([1, 4], [], [2]),
    ([1, 4], [2], []),
    ([2, 4], [], [1]),
    ([2, 4], [1], []),
    ([1, 2, 4], [], [])]

    sage: [len(gen_nodes_parts(range(i),2)) for i in range(6)]
    [1, 2, 4, 8, 16, 32]

    sage: [len(gen_nodes_parts(range(i),3)) for i in range(6)]
    [1, 3, 9, 27, 81, 243]
    
    sage: [len(gen_nodes_parts(range(i),3,is_commute=True)) for i in range(6)]
    [1, 1, 2, 5, 14, 41]
    """
    assert k >= 0
    if len(nodes) == 0: return [((),)*k]
    if k == 0: return []

    rs = []
    l = len(nodes)+1
    for i in range(l):
        gs = itertools.combinations(nodes,i)
        for g in gs:
            rest = [node for node in nodes if node not in g]
            p_rest = gen_nodes_parts(rest,k-1,is_commute)
            rs_ = [tuple([g] + list(p)) for p in p_rest]
            rs.extend(rs_)

    if is_commute:
        rs = CM.vset(rs,idfun=frozenset);

    return rs



def gen_count_ktrees_ordered(trees, is_commute=False):
    """
    When nchildren = 2
    sage: [len(gen_count_btrees_ordered(range(i))) for i in range(7)]
    [1, 1, 4, 30, 336, 5040, 95040]
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
        print is_commute, len(rest), nchildren, len(parts)

        for part in parts:
            ctrees = [gen_count_ktrees_ordered(p) for p in part]
            rs_ = [tuple([root] + list(c))
                   for c in itertools.product(*ctrees)]
            rs.extend(rs_)         
   
    return rs

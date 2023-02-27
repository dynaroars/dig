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



@cached_function
def catalan(n):
    """
    return the Catalan number n for (unordered) tree counting
    C(n) = C(0)*C(n-1) + C(1)*C(n-2) + ... C(n-1)*C(0)
    Note: cached_function makes it much faster (requires SAGE)
    Note: Sage has its own catalan_number function

    sage: [catalan(i) for i in range(10)]
    [1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862]
    """
    
    if n == 0 or n == 1: return 1
    return sum(catalan(k)*catalan(n-k-1) for k in range(n))


def gen_count_btrees(trees):
    """
    return counting (unordered) trees from a set of nodes.  
    The number of generated trees is the Catalan number


    sage: [len(gen_count_btrees(range(i))) for i in range(10)]
    [1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862]

    sage: gen_count_btrees(['a','b'])
    [('a', None, ('b', None, None)), ('a', ('b', None, None), None)]
    """

    if len(trees) == 0: return [None] #leaf

    root = trees[0]
    rest = trees[1:]

    rs = []
    for i in range(len(rest)+1):
        ltrees = gen_count_btrees(rest[:i])
        rtrees = gen_count_btrees(rest[i:])
        trees_ = [tuple([root]+list(c)) 
                 for c in itertools.product(ltrees,rtrees)]
        rs = rs + trees_

    return rs


def gen_count_btrees_ordered(trees):
    """
    return counting (ordered) trees from a set of nodes.  
    The number of generated trees is the Catalan number

    sage: gen_count_btrees_ordered(['a','b'])
    [('a', None, ('b', None, None)),
    ('a', ('b', None, None), None),
    ('b', None, ('a', None, None)),
    ('b', ('a', None, None), None)]

    sage: [len(gen_count_btrees_ordered(range(i))) for i in range(6)]
    [1, 1, 4, 30, 336, 5040]
    """

    if len(trees) == 0: return [None] #leaf

    rs = []
    for i in range(len(trees)):
        root = trees[i]
        rest = trees[:i] + trees[i+1:]

        for j in range(len(rest)+1):
            combs = itertools.combinations(rest,j)
            combs = ((c, [o for o in rest if o not in c]) 
                     for c in combs)
            
            for l,r in combs:
                ltrees = gen_count_btrees_ordered(l)
                rtrees = gen_count_btrees_ordered(r)
                trees_ = [tuple([root]+list(c)) 
                          for c in itertools.product(ltrees,rtrees)]
                rs.extend(trees_)

    return rs
    

def catalan_ordered(n):
    """
    The number of ordered tree counting.
    C(n) = n! * Catalan(n)
    """
    return factorial(n) * catalan_number(n)

    

@cached_function
def count_part(n,k):
    """
    Number of ways to distribute n items into k bins
    """
    assert n >= 0
    assert k >= 0

    if n == 0: return 1
    if k == 0: return 0

    return sum(count_part(n-i,k-1) for i in range(n+1))

@cached_function
def gen_parts(n,k):

    assert n >= 0
    assert k >= 0
    if n == 0: return [[0]*k]
    if k == 0: return []

    rs = []
    for i in range(n+1):
        ps = [[i] + l
              for l in gen_parts(n-i,k-1)]
        rs.extend(ps)

    assert len(rs) == count_part(n,k)
    return rs
                    

def gen_parts_tuples(n,k):
    """
    sage: gen_parts_tuples(3,4)
    [(0, 0, 0, 3),
    (0, 0, 1, 2),
    (0, 0, 2, 1),
    (0, 0, 3, 0),
    (0, 1, 0, 2),
    (0, 1, 1, 1),
    (0, 1, 2, 0),
    (0, 2, 0, 1),
    (0, 2, 1, 0),
    (0, 3, 0, 0),
    (1, 0, 0, 2),
    (1, 0, 1, 1),
    (1, 0, 2, 0),
    (1, 1, 0, 1),
    (1, 1, 1, 0),
    (1, 2, 0, 0),
    (2, 0, 0, 1),
    (2, 0, 1, 0),
    (2, 1, 0, 0),
    (3, 0, 0, 0)]
    sage: gen_parts_tuples(1,2)
    [(1, 0), (0, 1)]
    sage: gen_parts_tuples(3,1)
    [(3,)]
    sage: gen_parts_tuples(3,2)
    [(3, 0), (2, 1), (1, 2), (0, 3)]
    sage: gen_parts_tuples(4,3)
    [(4, 0, 0),
    (3, 1, 0),
    (3, 0, 1),
    (2, 2, 0),
    (2, 1, 1),
    (2, 0, 2),
    (1, 3, 0),
    (1, 2, 1),
    (1, 1, 2),
    (1, 0, 3),
    (0, 4, 0),
    (0, 3, 1),
    (0, 2, 2),
    (0, 1, 3),
    (0, 0, 4)]
    """
    return map(tuple,gen_parts(n,k))



def gen_count_ktrees(trees):
    """
    return counting (unordered) k-ary trees from a set of nodes.  
    The number of generated trees is the Catalan number

    # nchildren =2
    # sage: [len(gen_count_ktrees(range(i))) for i in range(10)]
    # [1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862]

    # nchildren =3
    sage: [len(gen_count_ktrees(range(i))) for i in range(10)]
    [1, 1, 3, 12, 55, 273, 1428, 7752, 43263, 246675]
    """

    if len(trees) == 0: return [None] #leaf

    root = trees[0]
    nchildren = 3

    rest = trees[1:]

    parts_tuples = gen_parts_tuples(len(rest),nchildren)
    
    rs = []
    for parts in parts_tuples:
        cidx = 0
        ctrees = []
        for i in parts:
            trees_ = gen_count_ktrees(rest[cidx:cidx+i])
            ctrees.append(trees_)
            cidx = cidx+i

        
        rs_ = [tuple([root]+list(c)) 
               for c in itertools.product(*ctrees)]
        rs.extend(rs_)

    return rs
    

def dist_nodes(nodes,parts):
    """
    Distribute ordered nodes among parts

    Examples:

    sage:  dist_nodes([8],(1,))
    [([8],)]

    sage:  dist_nodes([1,2],(1,1))
    [([1], [2]), ([2], [1])]

    sage: dist_nodes([1,2,3,4],(2,2))
    [([1, 2], [3, 4]),
    ([1, 3], [2, 4]),
    ([1, 4], [2, 3]),
    ([2, 3], [1, 4]),
    ([2, 4], [1, 3]),
    ([3, 4], [1, 2])]

    sage: dist_nodes([1,2,3,4],(2,1,1))
    [([1, 2], [3], [4]),
     ([1, 2], [4], [3]),
     ([1, 3], [2], [4]),
     ([1, 3], [4], [2]),
     ([1, 4], [2], [3]),
     ([1, 4], [3], [2]),
     ([2, 3], [1], [4]),
     ([2, 3], [4], [1]),
     ([2, 4], [1], [3]),
     ([2, 4], [3], [1]),
     ([3, 4], [1], [2]),
     ([3, 4], [2], [1])]
    sage: dist_nodes([1,2,3,4,5],(2,1,2))
    [([1, 2], [3], [4, 5]),
     ([1, 2], [4], [3, 5]),
     ([1, 2], [5], [3, 4]),
     ([1, 3], [2], [4, 5]),
     ([1, 3], [4], [2, 5]),
     ([1, 3], [5], [2, 4]),
     ([1, 4], [2], [3, 5]),
     ([1, 4], [3], [2, 5]),
     ([1, 4], [5], [2, 3]),
     ([1, 5], [2], [3, 4]),
     ([1, 5], [3], [2, 4]),
     ([1, 5], [4], [2, 3]),
     ([2, 3], [1], [4, 5]),
     ([2, 3], [4], [1, 5]),
     ([2, 3], [5], [1, 4]),
     ([2, 4], [1], [3, 5]),
     ([2, 4], [3], [1, 5]),
     ([2, 4], [5], [1, 3]),
     ([2, 5], [1], [3, 4]),
     ([2, 5], [3], [1, 4]),
     ([2, 5], [4], [1, 3]),
     ([3, 4], [1], [2, 5]),
     ([3, 4], [2], [1, 5]),
     ([3, 4], [5], [1, 2]),
     ([3, 5], [1], [2, 4]),
     ([3, 5], [2], [1, 4]),
     ([3, 5], [4], [1, 2]),
     ([4, 5], [1], [2, 3]),
     ([4, 5], [2], [1, 3]),
      ([4, 5], [3], [1, 2])]
    """

    assert sum(parts) == len(nodes)
    assert len(parts) >= 1

    part_current = parts[0]
    cnodes = itertools.combinations(nodes, part_current)
    
    if len(parts) == 1: return [tuple([list(cnodes.next())])]

    part_rest = parts[1:]
    rs = []
    for cn in cnodes:
        node_rest = [node for node in nodes if node not in cn]
        ps = dist_nodes(node_rest, part_rest)
        rs_ = [tuple([list(cn)] + list(p)) for p in ps]
        rs.extend(rs_)

    return rs


def gen_count_ktrees_ordered(trees):
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
        parts_tuples = gen_parts_tuples(len(rest),nchildren)

        for pt in parts_tuples:
            dists_tuples = dist_nodes(rest,pt)
            for dt in dists_tuples:
                ctrees = [gen_count_ktrees_ordered(t) for t in dt]
                rs_ = [tuple([root] + list(c))
                       for c in itertools.product(*ctrees)]
                rs.extend(rs_)
    return rs
        

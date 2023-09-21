import common as CM
from sage.all import *

def gp(ls):
    """
    generates permutations of the given list ls
    the len of the result is  |ls|!
    """
    
    if len(ls)==1: return [tuple(ls)]

    rs = []
    for l in ls:
        ls_ = list(set(ls) - set([l]))
        gps = gp(ls_)
        gps = [tuple([l]+list(g)) for g in gps]
        rs = rs + gps

    assert len(rs)==factorial(len(ls))
    return rs

def count_bin_unorder(ls):
    """
    
    in: [elem]
    out: [BT]
    BT:  None or (elem,BT,BT)

    T_n = catalan_n
    Recurrence form = sum_{i=0}^{n-1} T_i * T_{n-i-1}

    """

    if len(ls)==0: return [None]
        

    root = ls[0]
    ls_ = ls[1:]
    print 'ls_', ls_

    rs = []
    for k in range(len(ls)):
        print 'k', k
        ls1=count_bin_unorder(ls_[:k])
        print 'ls1',ls1
        ls2=count_bin_unorder(ls_[k:])
        print 'ls2',ls2

        rs_ = [tuple([root]+c) for c in CartesianProduct(ls1,ls2)]
        rs = rs + rs_

    return rs


def count_bin_order(ls):
    """
    
    in: [elem]
    out: [BT]
    BT:  None or (elem,BT,BT)

    T_n = n! * catalan_n
    Recurrence form = n* sum_{i=0}^{n-1} choose((n-1),i) T_i * T_{n-i-1}
    """

    if len(ls)==0: return [None]

    rs = []        
    for l in ls:
        root = l
        ls_ = list(set(ls) - set([root]))
        #print 'ls_', ls_

        rs0 = []
        for k in range(len(ls)):
            #print '\nk', k

            cl = Combinations(ls_,k)
            #print 'cl',list(cl)

            rs_ = []
            for c in cl:
                g1 = c
                g2 = list(set(ls_) - set(c))
                #print 'g1',g1,', g2',g2
                ls1 = count_bin_order(g1)
                ls2 = count_bin_order(g2)
                rs__ = [tuple([root]+c) for c in CartesianProduct(ls1,ls2)]
                rs_ = rs_ + rs__

            rs0 = rs0 + rs_

        rs = rs+rs0
        assert len(set(rs))==len(rs)
        
    return rs


@cached_function
def count_bin_order1(nodes):
    """
    
    in: (nodes)
    out: (BT)
    BT:  None or (elem,BT,BT)

    T_n = n! * catalan_n
    Recurrence form = n* sum_{i=0}^{n-1} choose((n-1),i) T_i * T_{n-i-1}
    """
    assert isinstance(nodes,tuple)
    
    if len(nodes) == 0:
        return [None] #leaf

    rs = []        
    for root in nodes:
        nodes_ = tuple(set(nodes) - set([root]))

        rs0 = []
        for k in range(len(nodes)): #0 .. |nodes|-1

            gs = Combinations(nodes_,k)

            rs_ = []
            for g1 in gs:
                g2 = tuple(set(nodes_) - set(g1))
                nodes1 = count_bin_order1(tuple(g1))
                nodes2 = count_bin_order1(tuple(g2))
                rs__ = [tuple([root]+c) for c in CartesianProduct(nodes1,nodes2)]
                rs_ = rs_ + rs__

            rs0 = rs0 + rs_

        rs = rs+rs0
        

    assert len(rs) == factorial(len(nodes))*catalan_number(len(nodes))
    return rs


def count_part(n,k):
    assert n >= 0
    assert k >= 0
    if n == 0: return 1
    if k == 0: return 0


    return sum([count_part(i,k-1) for i in range(n+1)])



def gen_parts(ns,k,ordered=True):
    """
    sage:  gen_parts(('a','b'),5,ordered=False)
    [((), (), (), (), ('a', 'b')), ((), (), (), ('a',), ('b',))]

    sage:  gen_parts(('a',),5,ordered=False)
    [((), (), (), (), ('a',))]

    sage:  gen_parts(('a',),5,ordered=True)
    [((), (), (), (), ('a',)), ((), (), (), ('a',), ()), ((), (), ('a',), (), ()), ((), ('a',), (), (), ()), (('a',), (), (), (), ())]
    """
    assert isinstance(ns,tuple)
    assert k >= 0
    
    if len(ns)==0: return [((),)*k]
    if k == 0: return []

    rs = []
    rl = len(ns) if ordered else len(ns)//2
    for i in range(rl+1):
        gs = Combinations(ns,i)
        for g in gs:
            rests = set(ns)-set(g)
            p_rests = gen_parts(tuple(rests),k-1)
            rs_ = [tuple([tuple(g)]+list(p)) for p in p_rests]
            rs.append(rs_)
            
    rs = CM.flatten(rs,list)
    
    if ordered == False:
        #if order doesn't matter, e.g.,  ((),(a,b)) == ((a,b),())
        rs = CM.vset(rs,idfun=Set)
        
    return rs


def get_arity(node):
    return {'a':2,'b':3,'c':2,'d':2,'e':2}[node]

def is_ordered(node):
    return {'a':True,'b':True,'c':True,'d':True}[node]

#@cached_function
def gen_trees(nodes):
    """
    in: (nodes)
    out: [BT]
    BT:  None or (elem,BT,BT)

    T_n = n! * catalan_n
    Recurrence form = n* sum_{i=0}^{n-1} choose((n-1),i) T_i * T_{n-i-1}
    """
    assert isinstance(nodes,tuple)
    
    if len(nodes) == 0:
        return [None] #leaf

    ts = []
    for root in nodes:

        rests = tuple(set(nodes) - set([root]))

        cpl = []

        if get_arity(root) == 1:
            cp = gen_trees(rests)
            ts.append([(root,c) for c in cp])
        else:
            for k in range(len(nodes)):
                #print k

                gs = Combinations(rests,k)
               
                t_ = [[tuple(gs1),tuple(set(rests)-set(gs1))] for gs1 in gs]
                assert [len(t__)==2 for t__ in t_]
                print t_
                t_ = [map(gen_trees,t__) for t__ in t_]
                t_ = [CartesianProduct(*t__) for t__ in t_]
                cpl.append(t_)

            cpl = CM.flatten(cpl,list)

            #print 'len(cpl)',len(cpl)
            #print 'cpl' , cpl
            ts.append([[tuple([root]+c) for c in cp] for cp in cpl])
            #print ts


    ts = CM.flatten(ts,list)
    assert len(ts) == factorial(len(nodes))*catalan_number(len(nodes))
    assert isinstance(ts,list)
    return ts



def fuzz_catalan(k,n): return binomial(k*n,n)/(k*n-n+1)
    

def gt(nodes):
    """
    in: (nodes)
    out: [BT]
    BT:  None or (elem,BT,BT)

    T_n = n! * fuz_catalan_n
    """
    assert isinstance(nodes, tuple)
    
    if len(nodes) == 0:
        return [None] #leaf

    ts = []
    for root in nodes:
        rests = tuple(set(nodes) - set([root]))

        #partition into k sets of nodes from (k is the arity of root)
        cpl = []
        pts = gen_parts(tuple(rests),get_arity(root),ordered=is_ordered(root))
        print 'pts',pts
        cpl = [CartesianProduct(*map(gt,pt)) for pt in pts]
        print 'cpl',cpl
        ts_ = [[tuple([root]+c) for c in cp] for cp in cpl]
        print 'ts_', ts_
        ts.append(ts_)
        
        CM.pause()
    ts = CM.flatten(ts,list)
    assert isinstance(ts,list)

    if CM.vall_same(nodes,idfun=lambda x: get_arity(x)) and \
        CM.vall(nodes,lambda x:  is_ordered(x)):
        
        #when all nodes have same arities and all are non-commutative
        fact_fuz_catalan = factorial(len(nodes))*fuzz_catalan(get_arity(nodes[0]),len(nodes))
        assert len(ts) == fact_fuz_catalan

    return ts

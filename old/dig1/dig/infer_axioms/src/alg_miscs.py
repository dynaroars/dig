import itertools

def permutate(es, idxs, keys=None):
    """
    >>> permutate((0,1,2,3),(0,2,3,1))
    (0, 2, 3, 1)

    >>> permutate((2,2,1), (0,2,1))
    (1, 1, 2)

    >>> permutate((2,3,1,3,3), (3,4,1,0,2))
    (1, 0, 4, 0, 0)

    """
    assert len(es) == len(idxs)
    assert keys is None or len(keys) == len(idxs)
    if keys is None: keys = range(len(idxs))

    vals = (keys[i] for i in idxs)  
    M = dict(zip(keys, vals))  # {'a': 'a', 'b': 'c', 'c': 'b'}

    return tuple(M[e] for e in es)

def gen_args(n):
    """
    >>> gen_args(3)
    [(0, 0, 0), (0, 0, 1), (0, 1, 0), (0, 1, 1), (0, 1, 2)]
    >>> len(gen_args(5))
    52
    >>> gen_args(1)
    [(0,)]
    >>> gen_args(2)
    [(0, 0), (0, 1)]
    >>> gen_args(0)
    []
    """
    
    if n <= 0: return []

    ls = range(n)
    combs = itertools.product(ls, repeat=n)
    #ignore the first one which is 0,1,2..
    perms = list(itertools.permutations(ls))[1:]  

    rs = [(0,) * len(ls)]  #0,0,0,0 ...
    cache = set()
    for e in combs:
        #if all elems are same, e.g., 1 1 1 then
        #they all reduce to 0 0 0 ... 
        if all(e_ == e[0] for e_ in e): continue
            
        if e not in cache:
            rs.append(e)            
            cache.add(e)
            
            for perm in perms:
                p = permutate(e, perm, ls)
                cache.add(p)
    return rs

def powerset(s):
    "powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
    return itertools.chain.from_iterable(
        itertools.combinations(s, r) for r in range(len(s)+1))

def gen_parts(nodes, k, is_commute):
    """
    Divides n nodes into k parts

    >>> assert gen_parts([1,2,3], 2, True) == [((), (1, 2, 3)), ((1,), (2, 3)), ((2,), (1, 3)), ((3,), (1, 2))]
    
    >>> gen_parts([1,2,3], 2, False) 
    [((), (1, 2, 3)), ((1,), (2, 3)), ((2,), (1, 3)), ((3,), (1, 2)), ((1, 2), (3,)), ((1, 3), (2,)), ((2, 3), (1,)), ((1, 2, 3), ())]

    >>> assert gen_parts([], 3, True) == [((), (), ())]
    >>> assert gen_parts([1], 3, True) == [((), (), (1,))]
    >>> gen_parts([1], 3, False)
    [((), (), (1,)), ((), (1,), ()), ((1,), (), ())]
    >>> assert gen_parts([1,2,3], 1, True) == [((1, 2, 3),)]
    >>> assert gen_parts([1,2,3], 1, False) == [((1, 2, 3),)]
    >>> assert not gen_parts([1,2,3], 0, True)
    >>> assert not gen_parts([1,2,3], 0, False)
    >>> assert len(gen_parts(range(9), 4, True)) == 11051
    >>> assert len(gen_parts(range(5), 4, False)) == 1024
    >>> assert len(gen_parts(range(4), 7, True)) == 15
    >>> assert len(gen_parts(range(4), 7, False)) == 2401

    >>> assert not gen_parts([], 0, True)
    """
    def gen_parts_rec(nodes, k, cache, is_commute):
        assert k >= 0
        
        if not nodes: return [((),)*k]
        elif k == 0: return []
        else:
            try:
                key = tuple(nodes + [k, is_commute])
            except TypeError:
                key = tuple(list(nodes) + [k, is_commute])

            if key in cache:
                return cache[key]

            parts = []
            for g in powerset(nodes):
                rest = [node for node in nodes if node not in g]
                p_rest = gen_parts_rec(rest, k-1, cache, is_commute)
                parts_ = [tuple([g] + list(p)) for p in p_rest]
                parts.extend(parts_)

            if is_commute:
                s = set()
                parts_ = []
                for part in parts:
                    p = frozenset(part)
                    if p not in s:
                        s.add(p)
                        parts_.append(part)
                parts = parts_

            cache[key] = parts
            return parts
    
    if not nodes and k == 0: return []
    return gen_parts_rec(nodes, k, {}, is_commute)

if __name__ == "__main__":
    import doctest
    doctest.testmod()
                

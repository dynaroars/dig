"""
Todo: 
1. neighboring technique (remove (v,v) with just v)
2. assign value btw 0,1 based on their frequency 
3. performance

"""
import numpy as np
from collections import OrderedDict
import itertools

import vu_common as CM

class VCell(tuple):
    def __init__(self,locs):
        tuple.__init__(self,locs)
        self.val = None

    def __hash__(self):
        return hash(self+(self.val,))

    @staticmethod
    def mk(locs,val=None):
        p = VCell(locs)
        p.val = val
        return p

    @cached_function
    def is_concave(pts1,pts2):
        """
        Check if connecting points1 and points2 result in a concave shape
        
        sage: VCell.is_concave(tuple(map(VCell.mk,[(0,1),(0,2),(1,2)])),tuple(map(VCell.mk,[(1,0),(2,0),(2,1)])))
        True

        sage: VCell.is_concave(tuple(map(VCell.mk,[(0,1),(0,2),(1,2),(1,1)])),tuple(map(VCell.mk,[(1,0),(2,0),(2,1)])))
        False

        sage: VCell.is_concave(tuple(map(VCell.mk,[(0,1),(0,2),(1,2),(1,0)])),tuple(map(VCell.mk,[(1,0),(2,0),(2,1)])))        
        True

        sage: VCell.is_concave(tuple(map(VCell.mk,[(0,1),(0,2),(1,2),(1,0),(2,0),(2,1)])),tuple(map(VCell.mk,[(1,1)])))        
        False
        """
        pts = pts1 + pts2
        P = Polyhedron(pts)

        xs,ys = zip(*P.vertices_list())
        x_dims = min(xs),max(xs)+1
        y_dims = min(ys),max(ys)+1
        sq_pts = map(VCell.mk,VMatrix.get_idxs_range([x_dims,y_dims]))
        s1 = set(sq_pts)
        s2 = set(pts)
        other_pts = s1 - s2
        return any(P.contains(p) for p in other_pts)
    
    @staticmethod
    def get_linkage(pts):
        """
        """

        # initially each pt is in its own group
        groups = OrderedDict((i,[pt]) for i,pt in enumerate(pts))

        # then we start merging them
        dists = OrderedDict()
        max_id = len(groups)-1
        linkage = []
        pivot = None
        while len(groups) > 1:
            VCell.compute_dists(pivot,groups.items(),dists)
            min_d = min(d for (g,(d,_)) in dists.iteritems())
            min_d_gs = [(g,(d,c)) for (g,(d,c)) in dists.iteritems()
                        if d == min_d]
            
            (g1,g2),(dist,concave)=min_d_gs[0]
            
            if min_d!=Infinity and concave != False and len(min_d_gs) > 1:
                for (gi,gj),_ in min_d_gs:
                    is_concave=VCell.is_concave(
                        tuple(groups[gi]),tuple(groups[gj]))

                    dists[(gi,gj)]=(min_d,is_concave)
                    if is_concave==False:
                        g1,g2 = gi,gj
                        concave = is_concave
                        break

            linkage.append((g1,g2,(dist,concave)))

            for k in dists.iterkeys():
                if g1 in k or g2 in k:
                    del dists[k]
            
            max_id += 1
            groups[max_id] = groups.pop(g1)+groups.pop(g2)
            pivot = (max_id,groups[max_id])
            
        return linkage

    @staticmethod
    def str_of_linkage(linkage):
        return '\n'.join("{}. {} {} {}".format(i,g1,g2,dist)
                         for i,(g1,g2,dist) in enumerate(linkage))

    @staticmethod
    def compute_dists(pivot,groups,dists):
        """
        if pivot is avail, compute dist btw pivot and groups
        otherwise, compute dist btw all pairs in groups

        groups = [(gid,elems)]
        """
        if pivot:
            i_key,i_pts = pivot[0],pivot[1]
            for group in groups:
                j_key,j_pts = group[0],group[1]
                if i_key == j_key:
                    continue                
                key=(i_key,j_key)
                assert key not in dists
                dists[key] = (VCell.get_dist_2groups(i_pts,j_pts),None)
        else:
            for i in range(len(groups)):
                i_key,i_pts = groups[i][0],groups[i][1]
                for j in range(i):
                    j_key,j_pts = groups[j][0],groups[j][1]
                    key = (i_key,j_key)
                    assert key not in dists
                    dists[key] = (VCell.get_dist_2groups(i_pts,j_pts),None)

                
    @cached_function
    def f_neighbor(pt1,pt2):
        """
        sage: VCell.f_neighbor(VCell.mk((1,2,3),2),VCell.mk((1,2,3),100))
        9604
        sage: VCell.f_neighbor(VCell.mk((1,2,3),2),VCell.mk((1,2,3),4))
        4
        sage: VCell.f_neighbor(VCell.mk((1,2,3),2),VCell.mk((1,2,3),2))
        0
        sage: VCell.f_neighbor(VCell.mk((1,2,3),2),VCell.mk((1,2,1),2))
        +Infinity
        sage: VCell.f_neighbor(VCell.mk((1,2,3),2),VCell.mk((1,2,2),2))
        0
        sage: VCell.f_neighbor(VCell.mk((1,2,3),2),VCell.mk((1,2,2),4))
        4        
        """
        d = np.sum(np.square(np.subtract(pt1,pt2)))
        if d <= len(pt1): #neighbor
            return np.sum(np.square(np.subtract(pt1.val,pt2.val)))
        else:
            return Infinity

        
    @staticmethod
    def get_dist_2groups(group1,group2):
        """
        Compute distance btw 2 groups
        """
        dist = min(VCell.f_neighbor(pt1,pt2)
                   for pt1,pt2 in itertools.product(group1,group2))
        return dist


class VMatrix(object):
    def __init__(self,matrix):
        if not isinstance(matrix,np.ndarray):
            matrix = np.array(matrix)

        self.matrix = matrix

        #list of indices [(0,0),(0,1),..] and corresp vals [1,0,..]
        self._idxs = []
        self._vals = []
        self._pts = []
        
    @property
    def idxs(self):
        if not self._idxs:
            self._idxs = VMatrix.get_idxs(self.matrix.shape)

        return self._idxs

    @property
    def vals(self):
        if not self._vals:
            vals = []
            for idx in self.idxs:
                v = self.matrix[idx]
                vals.append(v)
            self._vals = vals

        return self._vals

    @property
    def pts(self):
        if not self._pts:
            self._pts = [VCell.mk(idx,val)
                          for idx,val in zip(self.idxs,self.vals)]

        return self._pts
            
            
    def __str__(self):
        return self.matrix.__str__()


    def get_clusters(self,k):
        linkage = VCell.get_linkage(self.pts)
        # print 'linkage'
        # print HCluster.str_of_linkage(linkage)
        if k is not None:
            clusters = HCluster.get_clusters_k(linkage,k)
        else:
            clusters = HCluster.get_clusters_auto(linkage,cdiff=0.01)
        

        cl = OrderedDict()
        for i,(k,vs) in enumerate(clusters.iteritems()):
            cl[i]=[self.idxs[v] for v in vs]

        return cl
        
    def get_invs(self,k):
        cls = self.get_clusters(k)
        lmatrix = self.get_label_matrix(cls)
        print lmatrix
        
    def get_label_matrix(self,clusters):
        lmatrix = np.zeros(self.matrix.shape,dtype=np.int)
        for label,vs in clusters.iteritems():
            for idx in vs:
                lmatrix[idx] = label

        return lmatrix

    @staticmethod
    def get_idxs_range(range_dims):
        start,end = range_dims[0]
        if len(range_dims)==1:
            return [[i] for i in range(start,end)]
        else:
            idxs = []
            next_idxs = VMatrix.get_idxs_range(range_dims[1:])
            for i in range(start,end):
                for idx in next_idxs:
                    idxs.append([i]+idx)
            return idxs
        
    @staticmethod
    def get_idxs(dims):
        """
        Return indices of a d1xd2x..xdn matrices
        """
        range_dims = zip([0]*len(dims),dims) #((0,d1),(0,d2)..)
        idxs = VMatrix.get_idxs_range(range_dims)
        return map(tuple,idxs)


    @staticmethod
    def reduce(matrices):
        assert matrices
        
        # if len(set(matrices)) == 1:
        #     return matrices[0]

        assert len(set(m.matrix.shape for m in matrices))

        mbase = matrices[0]

        M = np.zeros(mbase.matrix.shape,dtype=np.int)
        unset_val = max(np.amax(m.matrix) for m in matrices)+1

        for idx in mbase.idxs:
            idxs_vs = [m.matrix[idx] for m in matrices]
            M[idx] = idxs_vs[0] if len(set(idxs_vs)) == 1 else unset_val
            
        return VMatrix(M)
    
class HCluster(object):

    @staticmethod
    def get_clusters_k(linkage,k):
        if k is None: #guess clusters size
            dists = set([dist for (_,__,(dist,_)) in linkage])
            k = len(dists)
            
        d = OrderedDict((i,[i]) for i in range(len(linkage)+1))
        n = len(linkage)+1 - k

        for i in range(n):
            c0 = int(linkage[i][0])
            c1 = int(linkage[i][1])
            d[max(d)+1] = d[c0] + d[c1]
            del d[c0], d[c1]

        return d

    @staticmethod
    def get_clusters_auto(linkage,cdiff):
        """
        Note: if cdiff == 0 then only cluster exact ones
        """

        d = OrderedDict((i,[i]) for i in range(len(linkage)+1))

        for i in range(len(linkage)):
            ldiff = float(linkage[i][2][0])
            if cdiff is not None:
                if ldiff > cdiff:
                    break
            else:  #use integer diff
                if not ldiff.is_integer():
                    break

            c0 = int(linkage[i][0])
            c1 = int(linkage[i][1])
            d[max(d)+1]=d[c0] + d[c1]
            del d[c0], d[c1]

        return d


####

def test_create_matrix_lt(n,m):
    L =  np.random.randint(0, 2, (n, m))

    M = np.zeros(L.shape,dtype=np.int)
    for i in range(n):
        for j in range(m):
            if i > j:
                M[i][j]=L[i][j]
            elif i == j:
                M[i][j]=1
            else:
                M[i][j]=0
    return M


def test_create_matrix1(n,m):
    M = np.zeros((n,m),dtype=np.int)
    for i in range(n):
        for j in range(m):
            if i > j:
                M[i][j]=0
            elif i == j:
                M[i][j]=1
            else:
                M[i][j]=0
    return M


def test_create_matrix2():
    M = [[1,0,0,0,1,1,1],
         [0,0,0,0,1,1,1],
         [0,0,0,0,1,1,1],
         [0,0,0,0,0,0,0],
         [1,1,1,0,0,0,0],
         [1,1,1,0,0,0,0],
         [1,1,1,0,0,0,0]]
    return np.array(M)


def test_create_matrix3():
    M = [[1,0,0,0,1,1,1],
         [0,0,0,0,1,1,1],
         [0,0,0,0,1,1,1],
         [0,0,0,0,0,0,0],
         [1,1,1,0,0,0,0],
         [1,1,1,0,0,0,0],
         [1,1,1,0,0,0,0]]
    return np.array(M)

def test_create_matrix4():
    M = [[1,0,0,1,1,],
         [0,0,0,1,1,],
         [0,0,0,1,1,],
         [0,0,0,0,0,],
         [1,1,1,0,0,],
         [1,1,1,0,0,]]
    return np.array(M)

    


def test_array_init(N):
    """
    A = [3,5,7,9,11]
    A[i]=2*i+3

    3=5
    """
    A = np.zeros(N,dtype=int)
    assert N>=0
    for i in range(0,N):
        A[i]=2*i+3
    return A

def test_array_seq_init(N):
    """
    sage: test_array_seq_init(5)
    [7 10 13 16 19]
    Can do: find matching btw each elements of a
    """
    assert N>0
    A = np.zeros(N,dtype=int)
    A[0] = 7
    for i in range(1,N):
        A[i]=A[i-1]+3

    return A

def test_array_palindrom(a):
    """
    Can do: find matching btw each cells of a 
    [1,2,3,3,2,1] => a[i]==a[len(a)-i-1]
    idx 0 = idx 5, 1 = 4, 2 = 3
    group1: i=0,1,2
    group2: j=5,4,3

    
    j=l+ai+c where l is len(a)=6
    5=6+0a+c
    4=6+1a+c
    3=6+2a+c

    solve for a,c gives a=-1,c=-1
    """
    return all(a[i] == a[len(a)-i-1] for i in range(len(a)//2))

    
def test_array_heap(a):
    """
    Inequality, wont do
    """
    pass
    
def ex1(x):
    xy = []
    y = 5
    if x>y:
        x = y
    while True:
        xy.append((x,y))
        if not x <= 10:
            break
        if x >= 5:
            y = y + 1
        x = x + 1


    return xy
        
def ex2(x):
    if x>=0:
        y = x+1
    else:
        y = x-1
    b = 1 if (y<10) else 0
    return x,y,b

def ex2_doer(n):
    data = []
    for _ in range(n):
        data.append(ex2(random.choice(range(-50,50))))

    return data

def ex3_strncpy(n,s):
    if n>=s:
        d = s
    else:
        d = n+random.choice(range(10))
    return n,s,d

def ex3_strncpy_doer(n):
    data = []
    for _ in range(n):
        n = random.choice(range(0,20))
        s = random.choice(range(0,20))
        data.append(ex3_strncpy(n,s))

    return data

def ex4_max_doer(n):
    data = []
    for _ in range(n):
        inp = [random.choice(range(0,20)) for _ in range(2)]
        r = max(inp)
        data.append(tuple(inp + [r]))
    return data
    
def get_matrix_invs(matrices,k=None,seed=None):
    if seed is not None:
        np.random.seed(seed)
    matrices = map(VMatrix,matrices)
    matrix = VMatrix.reduce(matrices)
    print matrix
    matrix.get_invs(k)


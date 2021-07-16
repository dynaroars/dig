import operator
import copy
import multiprocessing as mp
import csv
import pdb
import sys
import datetime
import time
import itertools
import os
import functools

from pathlib import Path
from collections.abc import Iterable
from collections import OrderedDict, namedtuple

from sage.all import cached_function
import sage.all

# import settings
# import helpers.vcommon as CM

DBG = pdb.set_trace

# mlog = CM.getLogger(__name__, settings.logger_level)


def myprod(l): return functools.reduce(operator.mul, l, 1)


def is_sage_expr(x):
    return isinstance(x, sage.symbolic.expression.Expression)


class NestedArray:
    """
    Find NestedArray Invariant of the form  A[i] = B[e] where e = e1 | C[e]

    Examples:

    ###sage: logger.set_level(VLog.DEBUG)


    # paper_nested

    ### sage: var('A B C')
    (A, B, C)

    ### sage: tcs = [OrderedDict(
        [(A, [7, 1, -3]), (C, [8, 5, 6, 6, 2, 1, 4]), (B, [1, -3, 5, 1, 0, 7, 1])])]
    ### sage: xinfo = {'All': ['A', 'B', 'C'], 'Assume': [], 'Const': [], 'Expect': [
        'A[i]=B[C[2i+1]]'], 'ExtFun': [], 'ExtVar': [], 'Global': [], 'Input': [], 'Output': []}
    ### sage: na = NestedArray(terms=[],tcs=tcs,xinfo=xinfo)
    dig:Info:*** NestedArray ***
    ### sage: na.go()
    dig:Info:Select traces
    ...
    dig_arrays:Info:Preprocessing arrays
    dig_arrays:Info:Generate arr exps (nestings)
    dig_arrays:Info:Apply reachability analysis to 2 nestings to find valid ones
    ...
    dig_arrays:Info:Potential rels: 2
    dig:Info:Refine 2 invs
    dig:Info:Detected 2 invs for NestedArray:
    0: A[i1] == B[-2*i1 + 5]
    1: A[i1] == B[C[2*i1 + 1]]


    dig_arrays:Debug:Nesting A[i1] == B[C[(i1)_]] has 1 rel(s)
    dig_arrays:Debug:lambda A,B,C,i1: A[i1] == B[C[2*i1 + 1]]
    dig_arrays:Debug:Nesting A[i1] == B[(i1)_] has 1 rel(s)
    dig_arrays:Debug:lambda A,B,i1: A[i1] == B[-2*i1 + 5]


    # aes_addroundkey_vn
    ### sage: var('a b r Alogtable Logtable')
    (a, b, r, Alogtable, Logtable)

    ### sage: xinfo = {'All': ['Alogtable', 'Logtable', 'a', 'b', 'r'], 'Assume': [], 'Const': [], 'Expect': [
        'r[i] = Alogtable(mod255(add(Logtable(a[i]),Logtable(b[i]))))'], 'ExtFun': ['add', 'mod255'], 'ExtVar': [], 'Global': [], 'Input': ['a', 'b'], 'Output': []}

    ### sage: tcs1 = [OrderedDict([(r, [118]), (a, [29]), (b, [132]), (Alogtable, [1, 3, 5, 15, 17, 51, 85, 255, 26, 46, 114, 150, 161, 248, 19, 53, 95, 225, 56, 72, 216, 115, 149, 164, 247, 2, 6, 10, 30, 34, 102, 170, 229, 52, 92, 228, 55, 89, 235, 38, 106, 190, 217, 112, 144, 171, 230, 49, 83, 245, 4, 12, 20, 60, 68, 204, 79, 209, 104, 184, 211, 110, 178, 205, 76, 212, 103, 169, 224, 59, 77, 215, 98, 166, 241, 8, 24, 40, 120, 136, 131, 158, 185, 208, 107, 189, 220, 127, 129, 152, 179, 206, 73, 219, 118, 154, 181, 196, 87, 249, 16, 48, 80, 240, 11, 29, 39, 105, 187, 214, 97, 163, 254, 25, 43, 125, 135, 146, 173, 236, 47, 113, 147, 174, 233, 32, 96, 160, 251, 22, 58, 78, 210, 109, 183, 194, 93, 231, 50, 86, 250, 21, 63, 65, 195, 94, 226, 61, 71, 201, 64, 192, 91, 237, 44, 116, 156, 191, 218, 117, 159, 186, 213, 100, 172, 239, 42, 126, 130, 157, 188, 223, 122, 142, 137, 128, 155, 182, 193, 88, 232, 35, 101, 175, 234, 37, 111, 177, 200, 67, 197, 84, 252, 31, 33, 99, 165, 244, 7, 9, 27, 45, 119, 153, 176, 203, 70, 202, 69, 207, 74, 222, 121, 139, 134, 145, 168, 227, 62, 66, 198, 81, 243, 14, 18, 54, 90, 238, 41, 123, 141, 140, 143, 138, 133, 148, 167, 242, 13, 23, 57, 75, 221, 124, 132, 151, 162, 253, 28, 36,
                              108, 180, 199, 82, 246, 1]), (Logtable, [0, 0, 25, 1, 50, 2, 26, 198, 75, 199, 27, 104, 51, 238, 223, 3, 100, 4, 224, 14, 52, 141, 129, 239, 76, 113, 8, 200, 248, 105, 28, 193, 125, 194, 29, 181, 249, 185, 39, 106, 77, 228, 166, 114, 154, 201, 9, 120, 101, 47, 138, 5, 33, 15, 225, 36, 18, 240, 130, 69, 53, 147, 218, 142, 150, 143, 219, 189, 54, 208, 206, 148, 19, 92, 210, 241, 64, 70, 131, 56, 102, 221, 253, 48, 191, 6, 139, 98, 179, 37, 226, 152, 34, 136, 145, 16, 126, 110, 72, 195, 163, 182, 30, 66, 58, 107, 40, 84, 250, 133, 61, 186, 43, 121, 10, 21, 155, 159, 94, 202, 78, 212, 172, 229, 243, 115, 167, 87, 175, 88, 168, 80, 244, 234, 214, 116, 79, 174, 233, 213, 231, 230, 173, 232, 44, 215, 117, 122, 235, 22, 11, 245, 89, 203, 95, 176, 156, 169, 81, 160, 127, 12, 246, 111, 23, 196, 73, 236, 216, 67, 31, 45, 164, 118, 123, 183, 204, 187, 62, 90, 251, 96, 177, 134, 59, 82, 161, 108, 170, 85, 41, 157, 151, 178, 135, 144, 97, 190, 220, 252, 188, 149, 207, 205, 55, 63, 91, 209, 83, 57, 132, 60, 65, 162, 109, 71, 20, 42, 158, 93, 86, 242, 211, 171, 68, 17, 146, 217, 35, 32, 46, 137, 180, 124, 184, 38, 119, 153, 227, 165, 103, 74, 237, 222, 197, 49, 254, 24, 13, 99, 140, 128, 192, 247, 112, 7])])]


    ### sage: na = NestedArray(terms=[],tcs=tcs1,xinfo=xinfo)
    dig:Info:*** NestedArray ***
    ### sage: na.go()
    dig:Info:Select traces
    ...
    dig_arrays:Info:Preprocessing arrays
    dig_arrays:Info:Generate arr exps (nestings)
    dig_arrays:Info:Apply reachability analysis to 12 nestings to find valid ones
    ...
    dig_arrays:Info:Potential rels: 1
    dig:Info:Refine 1 invs
    dig:Info:Detected 1 invs for NestedArray:
    0: r[i1] == Alogtable[mod255(add(Logtable[a[i1]],Logtable[b[i1]]))]

    ### sage: tcs2 = [OrderedDict([(r, [209]), (a, [12]), (b, [85]), (Alogtable, [1, 3, 5, 15, 17, 51, 85, 255, 26, 46, 114, 150, 161, 248, 19, 53, 95, 225, 56, 72, 216, 115, 149, 164, 247, 2, 6, 10, 30, 34, 102, 170, 229, 52, 92, 228, 55, 89, 235, 38, 106, 190, 217, 112, 144, 171, 230, 49, 83, 245, 4, 12, 20, 60, 68, 204, 79, 209, 104, 184, 211, 110, 178, 205, 76, 212, 103, 169, 224, 59, 77, 215, 98, 166, 241, 8, 24, 40, 120, 136, 131, 158, 185, 208, 107, 189, 220, 127, 129, 152, 179, 206, 73, 219, 118, 154, 181, 196, 87, 249, 16, 48, 80, 240, 11, 29, 39, 105, 187, 214, 97, 163, 254, 25, 43, 125, 135, 146, 173, 236, 47, 113, 147, 174, 233, 32, 96, 160, 251, 22, 58, 78, 210, 109, 183, 194, 93, 231, 50, 86, 250, 21, 63, 65, 195, 94, 226, 61, 71, 201, 64, 192, 91, 237, 44, 116, 156, 191, 218, 117, 159, 186, 213, 100, 172, 239, 42, 126, 130, 157, 188, 223, 122, 142, 137, 128, 155, 182, 193, 88, 232, 35, 101, 175, 234, 37, 111, 177, 200, 67, 197, 84, 252, 31, 33, 99, 165, 244, 7, 9, 27, 45, 119, 153, 176, 203, 70, 202, 69, 207, 74, 222, 121, 139, 134, 145, 168, 227, 62, 66, 198, 81, 243, 14, 18, 54, 90, 238, 41, 123, 141, 140, 143, 138, 133, 148, 167, 242, 13, 23, 57, 75, 221, 124, 132, 151, 162, 253, 28, 36,
                              108, 180, 199, 82, 246, 1]), (Logtable, [0, 0, 25, 1, 50, 2, 26, 198, 75, 199, 27, 104, 51, 238, 223, 3, 100, 4, 224, 14, 52, 141, 129, 239, 76, 113, 8, 200, 248, 105, 28, 193, 125, 194, 29, 181, 249, 185, 39, 106, 77, 228, 166, 114, 154, 201, 9, 120, 101, 47, 138, 5, 33, 15, 225, 36, 18, 240, 130, 69, 53, 147, 218, 142, 150, 143, 219, 189, 54, 208, 206, 148, 19, 92, 210, 241, 64, 70, 131, 56, 102, 221, 253, 48, 191, 6, 139, 98, 179, 37, 226, 152, 34, 136, 145, 16, 126, 110, 72, 195, 163, 182, 30, 66, 58, 107, 40, 84, 250, 133, 61, 186, 43, 121, 10, 21, 155, 159, 94, 202, 78, 212, 172, 229, 243, 115, 167, 87, 175, 88, 168, 80, 244, 234, 214, 116, 79, 174, 233, 213, 231, 230, 173, 232, 44, 215, 117, 122, 235, 22, 11, 245, 89, 203, 95, 176, 156, 169, 81, 160, 127, 12, 246, 111, 23, 196, 73, 236, 216, 67, 31, 45, 164, 118, 123, 183, 204, 187, 62, 90, 251, 96, 177, 134, 59, 82, 161, 108, 170, 85, 41, 157, 151, 178, 135, 144, 97, 190, 220, 252, 188, 149, 207, 205, 55, 63, 91, 209, 83, 57, 132, 60, 65, 162, 109, 71, 20, 42, 158, 93, 86, 242, 211, 171, 68, 17, 146, 217, 35, 32, 46, 137, 180, 124, 184, 38, 119, 153, 227, 165, 103, 74, 237, 222, 197, 49, 254, 24, 13, 99, 140, 128, 192, 247, 112, 7])])]
    ### sage: na = NestedArray(terms=[],tcs=tcs2,xinfo=xinfo)
    dig:Info:*** NestedArray ***
    ### sage: na.go()
    dig:Info:Select traces
    ...
    dig_arrays:Info:Preprocessing arrays
    dig_arrays:Info:Generate arr exps (nestings)
    dig_arrays:Info:Apply reachability analysis to 137 nestings to find valid ones
    ...
    dig_arrays:Info:Potential rels: 11
    dig:Info:Refine 11 invs
    dig:Info:Detected 11 invs for NestedArray:
    0: r[i1] == Alogtable[add(Logtable[a[i1]],Logtable[b[i1]])]
    1: r[i1] == Alogtable[add(Logtable[a[i1]],Logtable[mod255(b[i1])])]
    2: r[i1] == Alogtable[add(Logtable[a[i1]],mod255(Logtable[b[i1]]))]
    3: r[i1] == Alogtable[add(Logtable[mod255(a[i1])],Logtable[b[i1]])]
    4: r[i1] == Alogtable[add(mod255(Logtable[a[i1]]),Logtable[b[i1]])]
    5: r[i1] == Alogtable[mod255(add(Logtable[a[i1]],Logtable[b[i1]]))]
    6: r[i1] == mod255(Alogtable[add(Logtable[a[i1]],Logtable[b[i1]])])
    7: r[i1] == Alogtable[add(Logtable[mod255(a[i1])],Logtable[mod255(b[i1])])]
    8: r[i1] == Alogtable[add(Logtable[mod255(a[i1])],mod255(Logtable[b[i1]]))]
    9: r[i1] == Alogtable[add(mod255(Logtable[a[i1]]),Logtable[mod255(b[i1])])]
    10: r[i1] == Alogtable[add(mod255(Logtable[a[i1]]),mod255(Logtable[b[i1]]))]


    # sage: from dig import DIG
    # sage: ig = InvGen("Traces/AES/Nested/aes_addroundkey_vn.tc",verbose=1)
    # *** InvGen ***
    # ...
    # *** ReadFile ***
    # read 'Traces_ICSE2012/AES/Nested/aes_addroundkey_vn.tc'
    # number of traces (tcs) read: 100
    # read 'Traces_ICSE2012/AES/Nested/aes_addroundkey_vn.ext'
    # 0. |_tcs|: 100
    # 1. |_tcs2|: 0
    # 2. _vs: [r_, rk, st]
    # 3. _xinfo:
    # 0. All: ['r_', 'rk', 'st']
    # 1. Assume: []
    # 2. Const: []
    # 3. Expect: ['r[i][j]= xor(st[i,j],rk[i,j])']
    # 4. ExtFun: ['xor']
    # 5. Global: []
    # 6. Input: ['st', 'rk']
    # 7. Output: ['r_']
    # ...

    # sage: _ =  ig.getInvs(inv_typ='nested',seed=1)
    # seed 1 (test 0.829402 0.595912 0.429361)
    # sample_traces: chose |tcs1|=1, |tcs2|=99 (attempted 1/100 tcs)
    # ...
    # *** NestedArray ***
    # * gen_extfuns: ext funs ['xor']
    # * getExtFunReps(['xor'],|avals|=32,doCartesianProd=False)
    # * fun: xor, fvals 152, idxs 224
    # 0. All: ['r_', 'rk', 'st']
    # 1. Assume: []
    # 2. Const: []
    # 3. Expect: ['r[i][j]= xor(st[i,j],rk[i,j])']
    # 4. ExtFun: ['xor']
    # 5. Global: []
    # 6. Input: ['st', 'rk']
    # 7. Output: ['r_']
    # 8. ZDims:
    # 0. r_: 2
    # 1. rk: 2
    # 2. st: 2
    # 3. xor: 2
    # Generate array expressions (nestings)
    # * gen_aexps [r_,xor,st,rk]: 1 expressions generated
    # * Find valid nestings using reachability analysis
    # 0. r_[i1][i2] == xor(st[(i1,i2)_][(i1,i2)_],rk[(i1,i2)_][(i1,i2)_]) has 1 relation(s)
    # lambda r_,rk,xor,st,i1,i2: r_[i1][i2] == xor(st[i1][i2],rk[i1][i2])
    # * Relations: 1
    # ...
    # Refine 1 candidate invariants
    # * rfilter(|ps|=1,|tcs|=100)
    # rfilter (before 1, after 1, diff 0)
    # ...
    # Detected Invariants for NestedArray:
    # 0: lambda r_,rk,xor,st,i1,i2: r_[i1][i2] == xor(st[i1][i2],rk[i1][i2])


    # na = NestedArray(terms=ig.ss,tcs1=[ig.tcs[0]],tcs2=ig.tcs[1:],xinfo=ig.xinfo,verbose=1)
    # na.solve()


    # paper_nested.tc example
    # sage: var('A B C')
    (A, B, C)
    # sage: na = NestedArray(terms=None,tcs=[{C: [8, 5, 6, 6, 2, 1, 4], B: [1, -3, 5, 1, 0, 7, 1], A: [7, 1, -3]}],xinfo={'All': ['A', 'B', 'C'], 'Const': [], 'Assume': [], 'Global': [], 'Expect': [], 'ExtFun': [], 'Input': [], 'Output': []})
    *** NestedArray ***
    0. All: ['A', 'B', 'C']
    1. Assume: []
    2. Const: []
    3. Expect: []
    4. ExtFun: []
    5. Global: []
    6. Input: []
    7. Output: []
    8. ZDims:
    0. A: 1
    1. B: 1
    2. C: 1


    # sage: na = NestedArray(terms=None,tcs=[{'R': [128, 127, 126, 125], 'N':[128]}], xinfo={'All': ['R'], 'Const': [], 'Assume': [], 'Global': [], 'Expect': ['R[i]=sub(N,i)'], 'ExtFun': ['sub'], 'Input': [], 'Output': ['R']})
    *** NestedArray ***
    * gen_extfuns: 1 ext funs ['sub']
    * getExtFunReps(['sub'],|avals|=5)
    * fun: sub, fvals 15, idxs 25
    # sage: na.go()
    Generate array expressions (nestings)* gen_aexps [R,sub,N]:
    2 expressions generated
    * Find valid nestings using reachability analysis
    0. R[i1] == sub(N[(i1)_],(i1)_) has 1 relation(s)
    lambda R,sub,N,i1: R[i1] == sub(N[0],i1)
    1. R[i1] == sub((i1)_,(i1)_) has 1 relation(s)
    lambda R,sub,i1: R[i1] == sub(128,i1)
    * Relations: 2
    Time elapsed: 0.0424 s (solve)
    Refine 2 candidate invariants
    * rfilter skips
    Time elapsed: 0.0001 s (refine)
    Detected Invariants for NestedArray:
    0: lambda R,sub,N,i1: R[i1] == sub(N[0],i1)
    1: lambda R,sub,i1: R[i1] == sub(128,i1)

    """

    def __init__(self, tcs, xinfo):
        assert isinstance(tcs, list) and tcs and all(
            isinstance(tc, dict) for tc in tcs), tcs
        assert isinstance(xinfo, dict), xinfo

        self.tcs = tcs
        self.xinfo = xinfo
        print('orig tcs', self.tcs)

    def preprocess(self):
        """
        Preprocess input data
        1) transforms external functions to special arrays
        1) change arr repr to value->index repr to speed up arr idx lookup
        2) generate nodes
        """

        evs = ExtFun.gen_extvars(self.xinfo)
        # arrays only
        evs = [OrderedDict((k, ev[k]) for k in ev if isinstance(v, list))
               for ev in evs]
        evs = Miscs.keys_to_str(evs)

        if evs:  # add to traces
            self.tcs = [merge_dict(evs + [tc]) for tc in self.tcs]
            self.tcs_extra = [merge_dict(evs + [tc]) for tc in self.tcs_extra]

        mytcs = []
        for tc in self.tcs:
            # arrs reprent ext funs (already in new format)
            efs = ExtFun.gen_extfuns(tc, self.xinfo)

            # convert normal arr format to new format
            arrs = {k: Miscs.get_idxs(v) for k, v in tc.items()}
            # arrs = OrderedDict(arrs)

            d = CM.merge_dict(efs + [arrs])
            mytcs.append(d)

        self.tcs = mytcs
        #print('preprocess', self.tcs)
        self.trees = [Tree(k, [None] * len(list(c.items())[0][1]), ExtFun(k).commute)
                      for k, c in self.tcs[0].items()]

    def solve(self):  # nested arrays

        print('Preprocessing arrays')

        # add ext funs, generate nodes, modify tcs
        self.preprocess()

        print("Generate arr exps (nestings)")
        aexps = AEXP.gen_aexps(self.trees, self.xinfo, self.tcs[0])
        print(
            f"Apply reachability to {len(aexps)} nestings to find invs")

        for a in aexps:
            a.peelme(self.tcs[0])

        # def wprocess(ae, Q):
        #     r = ae.peelme(data=self.tcs[0])
        #     if r:
        #         mlog.debug('Nesting {} has {} rel(s)\n{}'
        #                    .format(ae, len(r), '\n'.join(r)))

        #     Q.put(r)

        # Q = mp.Queue()
        # workers = [mp.Process(target=wprocess, args=(ae, Q)) for ae in aexps]

        # for w in workers:
        #     w.start()

        # wrs = []
        # for _ in workers:
        #     wrs.extend(Q.get())

        # print('Potential rels: {}'.format(len(wrs)))
        # self.sols = map(InvNestedArray, wrs)

    def refine(self):
        # No inferrence for array invs
        # Don't do ranking either since array equations is very long
        from dig_refine import Refine
        rf = Refine(ps=self.sols)
        rf.rfilter(tcs=self.tcs_extra)
        self.sols = rf.ps


tracefile = Path("../tests/traces/paper_nested.csv")
ss = {}
traces = []
with open(tracefile) as csvfile:
    myreader = csv.reader(csvfile, delimiter=';')
    for row in myreader:
        row = [field.strip() for field in row]

        if not row or row[0].startswith("#"):
            continue
        loc, contents = row[0], row[1:]
        if loc not in ss:
            ss[loc] = contents
        else:
            contents = list(map(eval, contents))
            traces.append(contents)


class Tree(namedtuple("Tree", ("root", "children", "commute"))):
    """
    leaf: Tree(None,None,False)
    tree: Tree('a',[Tree],False/True)
    """

    def __new__(cls, root=None, children=[], commute=False):

        if root is None:  # leaf
            assert not children, children
            assert not commute, commute
        else:
            assert isinstance(children, list) and children, children
            assert all(isinstance(c, Tree)
                       or c is None for c in children), children
            assert isinstance(commute, bool), commute

            children = [c if isinstance(c, Tree) else Tree() for c in children]
            commute = False if len(children) <= 1 else commute

        return super().__new__(cls, root, children, commute)

    @property
    def is_leaf(self):
        return self.root is None

    def __str__(self, leaf_content=None):
        """
        Examples:
        >>> print(Tree())
        None

        >>> print(Tree('a',[Tree('b',[None]), None]))
        a[b[None]][None]

        >>> print(Tree('a',[None, None]))
        a[None][None]

        >> print(Tree('a',[None,Tree('b',[None])]))
        a[None][b[None]]

        ### sage: print(Tree({'root':'xor','children':[None, \
        {'root':'b','children':[None]}, {'root':x,'children':[None]}]})
        xor(None,b[None],x[None]))

        ### sage: print Tree(x^2 + 7)
        x^2 + 7

        ### sage: print Tree(x).__str__(leaf_content='hi')
        hi

        ### sage: var('y')
        y
        ### sage: print Tree(x).__str__(leaf_content={x:y+7})
        y + 7
        """
        if self.is_leaf:
            if leaf_content:
                return str(leaf_content)
            else:
                return str(self.root)
        else:
            children = ''.join("[{}]".format(c.__str__(leaf_content))
                               for c in self.children)
            return f"{self.root}{children}"

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

        ### sage: t = Tree({'root':'a','children':[None,None]})
        ### sage: nodes = [Tree({'root':'b','children':[None,None]})]
        ### sage: map(str,t.gen_root_trees(
            nodes, vss=None, blacklist = {}, data={}))
        ['a[b[None][None]][b[None][None]]',
        'a[b[None][None]][None]',
        'a[None][b[None][None]]',
        'a[None][None]']

        ### sage: t = Tree({'root':'B','children':[None]})

        ### sage: nodes = [ \
        Tree({'root':'C','children':[None,None]}), \
        Tree({'root':'D','children':[None]})]

        ### sage: vss=[(8,),(15,),(7,)]
        ### sage: data = {'C':{8: [(2, 6)], 10: [(3, 7), (8, 2)], 3: [(1, 2)], 4: [(0, 4)], 2: [(2, 0), (1, 7)]},\
        'D':{8: [(7,)], 1: [(9,)], 2: [(8,)], 3: [(5,)]}, 'B':{8: [(10,), (4,)], 7: [(2,)], 15: [(8,), (3,)]}}

        ### sage: map(str,t.gen_root_trees(nodes,vss=vss, blacklist={}, data=data))
        ['B[C[D[None]][None]]', 'B[C[None][None]]', 'B[None]']

        """
        assert (isinstance(nodes, list) and
                all(isinstance(t, Tree) and t.is_node for t in nodes)), nodes

        assert vss is None or \
            (isinstance(vss, list) and
             all(isinstance(v, tuple) for v in vss)), vss

        assert isinstance(blacklist, dict), blacklist

        # print('START!!')
        # print('self', self, len(self.children))
        # print('nodes', ';'.join(map(str, nodes)))
        # print('vss', vss)
        # print('data', data)

        if vss:
            children_vss = Miscs.reach(vss, data[self.root])
            if not children_vss:
                # print('no children_vss')
                return []
        else:
            children_vss = [None] * len(self.children)
        #print('children_vss', children_vss)

        if nodes:
            children = nodes + [Tree()]

            children = [c for c in children
                        if self.root not in blacklist or
                        c.root not in blacklist[self.root]]

            # recursive call
            # print('children', ', '.join(map(str, children)))

            def gt(t, nodes_, vss_):
                if t.is_leaf:
                    return [t]
                else:
                    return t.gen_root_trees(nodes_, vss_, blacklist, data)

            # print('0', len(children), children,
            # len(children_vss), children_vss)
            children = [[gt(c, [node for node in nodes if node != c], vs) for c in children]
                        for vs in children_vss]
            #print('1', len(children), children)
            children = [list(itertools.chain(*c)) for c in children]
            #print('2',  len(children), children)
            # DBG()
            # assert len(children) == len(
            #     self.children), (len(children), len(self.children))

            combs = list(itertools.product(*children))
            #print('combs', len(combs), combs)

            if self.commute:
                """
                (T1, T2, T3) is equiv to (T1, T3, T2)
                """
                combs = vset(combs, idfun=Set)

            rs = [Tree(self.root, list(c), self.commute) for c in combs]
        else:
            rs = [Tree(self.root, [Tree()] * len(self.children), self.commute)]

        #print('rs',  ';'.join(map(str, rs)))
        return rs

    # @property
    # def leaf_tree(self):
    #     return Tree(None)

    @property
    def is_node(self):
        """
        >>> assert Tree('a',[None,None]).is_node is True
        >>> assert not Tree('a',[Tree('b',[None]), None]).is_node
        """
        return all(c.is_leaf for c in self.children)

    ###

    def get_non_leaf_nodes(self, nl_nodes=[]):
        """
        Returns the *names* of the non-leaves nodes

        ### sage: print Tree({'root':'a','children':[None,None]}).get_non_leaf_nodes()
        ['a']

        ### sage: Tree({'root':'a','children':[None, \
        {'root':'b','children':[None,None]}, \
        {'root':'c','children':[None]}, \
        {'root':'d','children':[None,None]}]}).get_non_leaf_nodes()
        ['a', 'b', 'c', 'd']
        """
        if self.is_leaf:
            return nl_nodes
        else:
            nl_nodes_ = [c.get_non_leaf_nodes(nl_nodes)
                         for c in self.children]
            nl_nodes = [self.root] + list(itertools.chain(*nl_nodes_))
            return nl_nodes

    def get_leaves(self):
        """
        TOCHECK

        Examples:

        ### sage: Tree.leaf_tree().get_leaves()
        [(None, None, [])]

        ### sage: rs = Tree({'root':'A','children': [ \
        {'root':'C','children':[None,None]}, \
        {'root':'D','children':[None]}]}).get_leaves()

        ### sage: [(str(p),idx,tid) for p,idx,tid in rs]
        [('C[None][None]', 0, ['A', 0, 'C', 0]),
        ('C[None][None]', 1, ['A', 0, 'C', 1]),
        ('D[None]', 0, ['A', 1, 'D', 0])]
        """

        def _get_leaves(t, p, idx, tid):

            assert isinstance(t, Tree)

            if t.is_leaf:  # leaf
                return [(p, idx, tid)]
            else:
                results = [_get_leaves(child, t, idx_, tid + [t.root, idx_])
                           for idx_, child in enumerate(t.children)]

                results = CM.vflatten(results, list)
                return results

        return _get_leaves(self, p=None, idx=None, tid=[])

    def gen_formula(self, v, data):
        """
        Generate a formula recursively to represent the data structure of tree based on
        input value v and data.


        ### sage: var('_B_0_C_0__i0 _B_0_C_0__i1')
        (_B_0_C_0__i0, _B_0_C_0__i1)


        ### sage: Tree({'root':'B','children':[\
        {'root':'C', 'children':[_B_0_C_0__i0 + 2*_B_0_C_0__i1]}]}).gen_formula(v=81,\
        data = {'C':{0: [(0,), (3,)], 1: [(4,)], 7: [(2,), (5,)], 8: [(6,)], 9: [(1,), (8,)], 17: [(7,)]},\
        'B':{81: [(17,)], 74: [(6,), (8,)], 71: [(5,), (7,)]}})
        _B_0_C_0__i0 + _B_0_C_0__i1*2 == 7


        ### sage: Tree({'root':'B','children':[\
        {'root':'C', 'children':[_B_0_C_0__i0 + 2*_B_0_C_0__i1]}]}).gen_formula(v=81, \
        data = {'C':{0: [(0,), (3,)], 1: [(4,)], 7: [(2,), (5,)], 8: [(6,)], 9: [(1,), (8,)], 17: [(7,)]},\
        'B':{81: [(17,), (9,)], 74: [(6,), (8,)], 71: [(5,), (7,)]}})
        Or(_B_0_C_0__i0 + _B_0_C_0__i1*2 == 7,
        Or(_B_0_C_0__i0 + _B_0_C_0__i1*2 == 1,
        _B_0_C_0__i0 + _B_0_C_0__i1*2 == 8))


        ### sage: Tree({'root':'add','children':[\
        {'root':'C', 'children':[{'root':'_add_0_C_','children':[100,200]}]},\
        {'root':'D', 'children':[{'root':'_add_1_D_','children':[100,200]}]}]}).gen_formula(v=17, \
        data = {'C':{0:[(0,)],17:[(1,)],8:[(2,)],3:[(3,),(4,)]},\
        'D':{1:[(0,)],9:[(1,),(3,)],0:[(2,)]},\
        'add':{17:[(8,9),(17,0)],8:[(8,0)],12:[(3,9),(0,12)],3:[(3,0)]}})


        """

        if is_sage_expr(self.root):
            return self.root == v

        elif isinstance(self.root, dict) and 'first_idx' in self.root:
            # special case {'first_idx':i,'coef':z}
            if v == 0:
                t0 = self.root['coef'] == 0
                t1 = self.root['first_idx'] == 1
                return Miscs._f([t0, t1], 'and', is_real=False)
            else:
                return self.root['coef'] == v
        else:
            try:
                idxs = data[self.root][v]
            except KeyError:  # not reachable, no rel
                return None

            orRs = []
            for idx in idxs:
                andRs = []
                for v_, a_ in zip(idx, self.children):
                    p_ = a_.gen_formula(v_, data)

                    if p_ is None:
                        andRs = None
                        break
                    andRs.append(p_)

                if andRs is not None:
                    assert len(andRs) > 0
                    andRs = Miscs._f(andRs, 'and', is_real=False)
                    orRs.append(andRs)

            orRs = Miscs._f(orRs, 'or', is_real=False)
            return orRs

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

# class MyTree:

#     def __init__(self, args):
#         """
#         Tree is a leaf (None or Expression)  or a dict {'root':, 'children':[..]}

#         ### sage: Tree({'root':None,'children':[None,None]})
#         Traceback (most recent call last):
#         ...
#         AssertionError: args['roots'] cannot be None

#         ### sage: var('y')
#         y
#         ### sage: print Tree({'root':'B', 'children':[{'root':'C','children':[x + 2*y]}]})
#         B[C[x + 2*y]]

#         """

#         if isinstance(args, dict) and 'coef' not in args and 'first_idx' not in args:

#             assert 'root' in args and 'children' in args, 'improper tree format: {}'.format(
#                 map(str, args))
#             assert args.get('root') is not None, "args['roots'] cannot be None"
#             assert isinstance(args.get('children'), list), args
#             assert args.get('children'), args.get('children')

#             self.root = args.get('root')
#             self.children = [c if isinstance(c, Tree) else Tree(c)
#                              for c in args.get('children')]

#             if 'commute' not in args or len(self.children) == 1:
#                 self.commute = False
#             else:
#                 self.commute = args.get('commute')

#         else:  # leaf
#             self.root = args
#             self.children = None
#             self.commute = False
#             # self.data = {}

#     def __eq__(self, other):
#         """
#         ### sage: var('y')
#         y
#         ### sage: Tree(x+y+7) == Tree(7+x+y)
#         True
#         ### sage: Tree(
#             {'root':x+y+7,'children':[None]}) == Tree({'root':x+y+7,'children':[None,None]})
#         False
#         ### sage: Tree({'root':x+y+7,'children':[None]}
#                    ) == Tree({'root':x+y+7,'children':[None]})
#         True
#         """
#         return type(other) is type(self) and self.__dict__ == other.__dict__

#     def __ne__(self, other):
#         """
#         ### sage: var('y')
#         y
#         ### sage: Tree(x+y+7) != Tree(7+x+y)
#         False
#         ### sage: Tree(x+y+7) != Tree(x+y)
#         True
#         """
#         return not self.__eq__(other)

#     def __hash__(self):
#         return hash(self.__str__())

#     def __str__(self, leaf_content=None):
#         """
#         Examples:
#         ### sage: print Tree(None)
#         None

#         ### sage: print Tree({'root':'a','children':[None,None]})
#         a[None][None]

#         ### sage: print Tree({'root':'a','children':[None,{'root':'b','children':[None]}]})
#         a[None][b[None]]

#         ### sage: print Tree({'root':'xor','children':[None, \
#         {'root':'b','children':[None]}, {'root':x,'children':[None]}]})
#         xor(None,b[None],x[None])

#         ### sage: print Tree(x^2 + 7)
#         x^2 + 7

#         ### sage: print Tree(x).__str__(leaf_content='hi')
#         hi

#         ### sage: var('y')
#         y
#         ### sage: print Tree(x).__str__(leaf_content={x:y+7})
#         y + 7

#         ### sage: print Tree({'root':'x','children':[None]})
#         x[None]
#         ### sage: print Tree({'root':x,'children':[None]})
#         x[None]
#         """
#         try:
#             children = [c.__str__(leaf_content=leaf_content)
#                         for c in self.children]

#             if self.root in ExtFun.efdict:
#                 rs = '({})'.format(','.join(children))
#             else:
#                 rs = ''.join(['[{}]'.format(c) for c in children])

#             rs = str(self.root) + rs
#             return rs

#         except Exception:
#             if leaf_content is None:
#                 return str(self.root)
#             else:
#                 if isinstance(leaf_content, dict):
#                     if is_sage_expr(self.root):
#                         return str(self.root(leaf_content))
#                     else:
#                         str(self.root)
#                 else:
#                     return str(leaf_content)

#     # def get_nchildren(self):
#     #     return len(self.children)

#     # def get_children(self):
#     #     return self.children

#     def commute(self):
#         return self.commute

#     @property
#     def leaf_tree(self):
#         return Tree(None)

#     @property
#     def is_node(self):
#         """
#         ### sage: Tree({'root':'a','children':[None,None]}).is_node()
#         True
#         """
#         return all(c.is_leaf for c in self.children)

#     @property
#     def is_leaf(self):
#         """
#         ### sage: Tree({'root':'a','children':[None,None]}).is_leaf()
#         False
#         """
#         return self.children is None

#     ###

#     def get_non_leaf_nodes(self, nl_nodes=[]):
#         """
#         Returns the *names* of the non-leaves nodes

#         ### sage: print Tree({'root':'a','children':[None,None]}).get_non_leaf_nodes()
#         ['a']

#         ### sage: Tree({'root':'a','children':[None, \
#         {'root':'b','children':[None,None]}, \
#         {'root':'c','children':[None]}, \
#         {'root':'d','children':[None,None]}]}).get_non_leaf_nodes()
#         ['a', 'b', 'c', 'd']
#         """
#         if self.is_leaf:
#             return nl_nodes
#         else:
#             nl_nodes_ = [c.get_non_leaf_nodes(nl_nodes)
#                          for c in self.children]
#             nl_nodes = [self.root] + CM.vflatten(nl_nodes_)
#             return nl_nodes

#     def get_leaves(self):
#         """
#         TOCHECK

#         Examples:

#         ### sage: Tree.leaf_tree().get_leaves()
#         [(None, None, [])]

#         ### sage: rs = Tree({'root':'A','children': [ \
#         {'root':'C','children':[None,None]}, \
#         {'root':'D','children':[None]}]}).get_leaves()

#         ### sage: [(str(p),idx,tid) for p,idx,tid in rs]
#         [('C[None][None]', 0, ['A', 0, 'C', 0]),
#         ('C[None][None]', 1, ['A', 0, 'C', 1]),
#         ('D[None]', 0, ['A', 1, 'D', 0])]
#         """

#         def _get_leaves(t, p, idx, tid):

#             assert isinstance(t, Tree)

#             if t.is_leaf:  # leaf
#                 return [(p, idx, tid)]
#             else:
#                 results = [_get_leaves(child, t, idx_, tid + [t.root, idx_])
#                            for idx_, child in enumerate(t.children)]

#                 results = CM.vflatten(results, list)
#                 return results

#         return _get_leaves(self, p=None, idx=None, tid=[])

#     def gen_root_trees(self, nodes, vss, blacklist, data):
#         """
#         Generates trees from nodes whose root is self.root

#         blacklist {a: L} disallows a[b[..]] and a[[c..]]
#         where {b,c} in L and only allows
#         [a[x[..]]] where x is not in L

#         so for example if we want to force a to be a Leaf then {a:L}
#         where L is all variables (except None).
#         This allows the removal of an extra whitelist

#         also if we have {a: L} where L is all variablles (except a) then basically
#         we disallow the tree with root 'a' since this says 'a' cannot have
#         any children (including) leaf.


#         Examples

#         ### sage: t = Tree({'root':'a','children':[None,None]})
#         ### sage: nodes = [Tree({'root':'b','children':[None,None]})]
#         ### sage: map(str,t.gen_root_trees(
#             nodes, vss=None, blacklist = {}, data={}))
#         ['a[b[None][None]][b[None][None]]',
#         'a[b[None][None]][None]',
#         'a[None][b[None][None]]',
#         'a[None][None]']

#         ### sage: t = Tree({'root':'B','children':[None]})

#         ### sage: nodes = [ \
#         Tree({'root':'C','children':[None,None]}), \
#         Tree({'root':'D','children':[None]})]

#         ### sage: vss=[(8,),(15,),(7,)]
#         ### sage: data = {'C':{8: [(2, 6)], 10: [(3, 7), (8, 2)], 3: [(1, 2)], 4: [(0, 4)], 2: [(2, 0), (1, 7)]},\
#         'D':{8: [(7,)], 1: [(9,)], 2: [(8,)], 3: [(5,)]}, 'B':{8: [(10,), (4,)], 7: [(2,)], 15: [(8,), (3,)]}}

#         ### sage: map(str,t.gen_root_trees(nodes,vss=vss, blacklist={}, data=data))
#         ['B[C[D[None]][None]]', 'B[C[None][None]]', 'B[None]']

#         """
#         assert (isinstance(nodes, list) and
#                 all(isinstance(x, Tree) and x.is_node for x in nodes)), nodes

#         assert vss is None or \
#             (isinstance(vss, list) and all(isinstance(v, tuple)
#                                            for v in vss)), vss
#         assert isinstance(blacklist, dict), blacklist

#         print('START!!')
#         print('self', self, len(self.children))
#         print('nodes', ';'.join(map(str, nodes)))
#         print('vss', vss)
#         print('data', data)

#         if vss:
#             children_vss = Miscs.reach(vss, data[self.root])
#             if not children_vss:
#                 print('no children_vss')
#                 return []
#         else:
#             children_vss = [None] * len(self.children)
#         print('children_vss', children_vss)

#         if nodes:
#             children = nodes + [self.leaf_tree]

#             children = [c for c in children
#                         if self.root not in blacklist or
#                         c.root not in blacklist[self.root]]

#             # recursive call
#             print('children', ', '.join(map(str, children)))

#             def _gt(r_, nodes_, vss_):
#                 if r_.is_leaf:
#                     return [r_]
#                 else:
#                     return r_.gen_root_trees(nodes=nodes_, vss=vss_,
#                                              blacklist=blacklist,
#                                              data=data)
#             print('0', children, children_vss)
#             children = [[_gt(c, [node for node in nodes if node != c], vs) for c in children]
#                         for vs in children_vss]
#             print('1', children)
#             children = [list(itertools.chain(*c)) for c in children]
#             print('2',  children)
#             # DBG()
#             # assert len(children) == len(
#             #     self.children), (len(children), len(self.children))

#             combs = list(itertools.product(*children))
#             print('combs', combs)

#             if self.commute():
#                 """
#                 (T1, T2, T3) is equiv to (T1, T3, T2)
#                 """
#                 combs = vset(combs, idfun=Set)

#             rs = [Tree({'root': self.root,
#                         'children': list(c),
#                         'commute': self.commute()})
#                   for c in combs]

#         else:
#             rs = [Tree({'root': self.root,
#                         'children': [self.leaf_tree] * len(self.children),
#                         'commute': self.commute()})]

#         print('rs',  ';'.join(map(str, rs)))
#         return rs

#     def gen_formula(self, v, data):
#         """
#         Generate a formula recursively to represent the data structure of tree based on
#         input value v and data.


#         ### sage: var('_B_0_C_0__i0 _B_0_C_0__i1')
#         (_B_0_C_0__i0, _B_0_C_0__i1)


#         ### sage: Tree({'root':'B','children':[\
#         {'root':'C', 'children':[_B_0_C_0__i0 + 2*_B_0_C_0__i1]}]}).gen_formula(v=81,\
#         data = {'C':{0: [(0,), (3,)], 1: [(4,)], 7: [(2,), (5,)], 8: [(6,)], 9: [(1,), (8,)], 17: [(7,)]},\
#         'B':{81: [(17,)], 74: [(6,), (8,)], 71: [(5,), (7,)]}})
#         _B_0_C_0__i0 + _B_0_C_0__i1*2 == 7


#         ### sage: Tree({'root':'B','children':[\
#         {'root':'C', 'children':[_B_0_C_0__i0 + 2*_B_0_C_0__i1]}]}).gen_formula(v=81, \
#         data = {'C':{0: [(0,), (3,)], 1: [(4,)], 7: [(2,), (5,)], 8: [(6,)], 9: [(1,), (8,)], 17: [(7,)]},\
#         'B':{81: [(17,), (9,)], 74: [(6,), (8,)], 71: [(5,), (7,)]}})
#         Or(_B_0_C_0__i0 + _B_0_C_0__i1*2 == 7,
#         Or(_B_0_C_0__i0 + _B_0_C_0__i1*2 == 1,
#         _B_0_C_0__i0 + _B_0_C_0__i1*2 == 8))


#         ### sage: Tree({'root':'add','children':[\
#         {'root':'C', 'children':[{'root':'_add_0_C_','children':[100,200]}]},\
#         {'root':'D', 'children':[{'root':'_add_1_D_','children':[100,200]}]}]}).gen_formula(v=17, \
#         data = {'C':{0:[(0,)],17:[(1,)],8:[(2,)],3:[(3,),(4,)]},\
#         'D':{1:[(0,)],9:[(1,),(3,)],0:[(2,)]},\
#         'add':{17:[(8,9),(17,0)],8:[(8,0)],12:[(3,9),(0,12)],3:[(3,0)]}})


#         """

#         if is_sage_expr(self.root):
#             return self.root == v

#         elif isinstance(self.root, dict) and 'first_idx' in self.root:
#             # special case {'first_idx':i,'coef':z}
#             if v == 0:
#                 t0 = self.root['coef'] == 0
#                 t1 = self.root['first_idx'] == 1
#                 return Miscs._f([t0, t1], 'and', is_real=False)
#             else:
#                 return self.root['coef'] == v
#         else:
#             try:
#                 idxs = data[self.root][v]
#             except KeyError:  # not reachable, no rel
#                 return None

#             orRs = []
#             for idx in idxs:
#                 andRs = []
#                 for v_, a_ in zip(idx, self.children):
#                     p_ = a_.gen_formula(v_, data)

#                     if p_ is None:
#                         andRs = None
#                         break
#                     andRs.append(p_)

#                 if andRs is not None:
#                     assert len(andRs) > 0
#                     andRs = Miscs._f(andRs, 'and', is_real=False)
#                     orRs.append(andRs)

#             orRs = Miscs._f(orRs, 'or', is_real=False)
#             return orRs

#     ##### Static methods for Tree #####

#     @ staticmethod
#     def gen_trees(nodes, vss, blacklist, data):
#         """
#         Generates nestings from a set of nodes. E.g., given nodes [a,b,c],
#         returns all nestings, e.g. [{a,[b,c],{a,[c,b]}},{b,[a,c]} ..

#         Examples:

#         ### sage: nodes = [\
#         Tree({'root':'A','children':[None]}), \
#         Tree({'root':'B','children':[None,None]}), \
#         Tree({'root':'C','children':[None,None,None]})]
#         ### sage: len(Tree.gen_trees(nodes=nodes,vss=None,blacklist={},data={}))
#         477

#         """

#         assert isinstance(nodes, list) and \
#             all(isinstance(x, Tree) and x.is_node for x in nodes)

#         assert vss is None or \
#             (isinstance(vss, list) and all(isinstance(v, tuple)
#                                            for v in vss)), vss

#         assert isinstance(blacklist, dict), blacklist

#         def _gt(t):
#             ts = t.gen_root_trees(nodes=CM.vsetdiff(nodes, [t]),
#                                   vss=vss,
#                                   blacklist=blacklist,
#                                   data=data)
#             return ts

#         trees = [_gt(node) for node in nodes]
#         trees = CM.vflatten(trees)

#         assert all(isinstance(t, Tree) for t in trees)

#         return trees


class AEXP(object):

    def __init__(self, lt, rt):
        """
        Initialize AEXP (Array Expression) which has the form left_tree = right_tree,
        e.g.  A[None][None] = B[C[None][None]][D[None]]

        Examples:
        _ = AEXP({'root':'v','children':[None]}, \
        {'root':'a','children':[{'root':'x3','children':[None,None,None]}]})

        ### sage: _ = AEXP(Tree({'root':'v','children':[None]}), \
        {'root':'a','children':[{'root':'x3','children':[None,None,None]}]})

        ### sage: _ = AEXP({'root':'v','children':[{'root':'a','children':[None]}]}, \
        {'root':'a','children':[{'root':'x3','children':[None,None,None]}]})
        Traceback (most recent call last):
        ...
        AssertionError: left tree has to be a node tree

        """
        assert isinstance(lt, Tree), lt
        assert lt.is_node, lt
        assert isinstance(rt, Tree), rt

        self.lt = lt
        self.rt = rt

    def __str__(self, leaf_content=None, do_lambda_format=False):
        """
        Returns the str of AEXP

        leaf_content: {},None,str
        Instantiates leaves of rt with leaf_content, e.g. A[x], leaf_info={x:5} => A[5]

        do_lambda_format: T/F
        Returns a lambda format of array expressions for evaluation

        Examples:

        ### sage: AEXP({'root':'v','children':[None]}, \
        {'root':'a','children':[{'root':'x3','children':[None,None,None]}]}).__str__()
        'v[i1] == a[x3[(i1)_][(i1)_][(i1)_]]'

        ### sage: AEXP({'root':'v','children':[None]}, \
        {'root':'a','children':[{'root':'x3',\
        'children':[None,None,None]}]}).__str__(do_lambda_format=True)
        'lambda v,a,x3,i1: v[i1] == a[x3[(i1)_][(i1)_][(i1)_]]'

        ### sage: AEXP({'root':'v','children':[None]}, \
        {'root':'a','children':[{'root':'x3',\
        'children':[None,None,x+7]}]}).__str__(leaf_content={x:5},do_lambda_format=True)
        'lambda v,a,x3,i1: v[i1] == a[x3[None][None][12]]'

        ### sage: var('y')
        y

        ### sage: AEXP({'root':'v','children':[None]}, \
        {'root':'a','children':[{'root':'x3',\
        'children':[None,{'root':'c',\
        'children':[x-y,None]}, x+7]}]}).__str__(leaf_content={x:5,y:7},\
        do_lambda_format=False)
        'v[i1] == a[x3[None][c[-2][None]][12]]'

        """
        l_idxs = [(i+1) for i in range(len(self.lt.children))]
        l_iformat = ''.join(f'[i{li}]' for li in l_idxs)  # [i][j]
        l_aformat = ','.join(f'i{li}' for li in l_idxs)  # i,j

        if leaf_content is None:
            r_idxs = f"({l_aformat})_"
            rt = self.rt.__str__(leaf_content=r_idxs)
        else:
            assert isinstance(leaf_content, dict), leaf_content
            rt = self.rt.__str__(leaf_content=leaf_content)

        rs = '{}{} == {}'.format(self.lt.root, l_iformat, rt)

        if do_lambda_format:
            l_idxs_ = ','.join([f'i{li}' for li in l_idxs])
            nodes = [self.lt.root] + vset(self.rt.get_non_leaf_nodes())
            lambda_ = 'lambda {},{}'.format(','.join(nodes), l_aformat)
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
        rs = all(iv in roots for iv in xinfo['Input'])
        return rs

    def gen_smt_formula(self, data):
        """
        todo: combine both gen_template & gen_formula

        returns a SMT formula from the aex wrt to data
        """
        pass

    def gen_template(self, idxs_vals=None, special=False):
        """
        special = True then it means we only have 1 data to compare against
        thus if the pass in indices of the leaves are 0's  , the result will be  z + 0*i = 0
        which then just gives z = 0, doesn't contribute to anything if we have only 1 data.
        Thus special flag turns the result z + 0*i = 0 into z = 0 and i = 1.

        Examples:

        ### sage: lt = Tree({'root':'R','children':[None,None,None]})
        ### sage: rt = Tree({'root': 'add', \
        'children': [{'root': 'C', 'children': [None]}, \
        {'root': 'D', 'children': [None]}]})
        ### sage: rs = AEXP(lt,rt).gen_template()
        ### sage: print rs.lt; print rs.rt
        R[None][None][None]
        add(C[_add_0_C_0__i1*i1 + _add_0_C_0__i2*i2 + _add_0_C_0__i3*i3 + _add_0_C_0__i0],
            D[_add_1_D_0__i1*i1 + _add_1_D_0__i2*i2 + _add_1_D_0__i3*i3 + _add_1_D_0__i0])



        ### sage: rs = AEXP({'root':'R','children':[None,None]}, \
        {'root':'add', 'children':[{'root':'C','children':[None]}, \
        {'root':'D','children':[None]}]}).gen_template()
        ### sage: print rs.lt; print rs.rt
        R[None][None]
        add(C[_add_0_C_0__i1*i1 + _add_0_C_0__i2*i2 + _add_0_C_0__i0],
            D[_add_1_D_0__i1*i1 + _add_1_D_0__i2*i2 + _add_1_D_0__i0])

        ### sage: rs = AEXP({'root':'R','children':[None,None]}, \
        {'root':'add', 'children':[None,None]}).gen_template(idxs_vals=[0,0],special=False)
        ### sage: print rs.lt; print rs.rt
        R[None][None]
        add(_add_0__i0,_add_1__i0)
        """
        assert not special or all(x == 0 for x in idxs_vals)
        assert idxs_vals is not None or not special

        if idxs_vals is None:
            ts = [1] + [sage.all.var('i{}'.format(i+1))
                        for i in range(self.lt.get_nchildren())]
        else:
            ts = [1] + list(idxs_vals)

        rt = copy.deepcopy(self.rt)  # make a copy

        leaves = rt.get_leaves()
        leaves = [(p, idx, tid) for p, idx, tid in leaves if p is not None]

        for p, idx, tid in leaves:
            prefix = '_{}__i'.format('_'.join(map(str, tid)))
            if special:
                c = {'first_idx': sage.all.var(prefix+str(1)),
                     'coef': sage.all.var(prefix+str(0))}
            else:
                c = Miscs.gen_template(ts, rv=None, prefix=prefix)

            p.children[idx] = Tree(c)
            assert isinstance(p, Tree)

        #rt.replace_leaf(tid=[], special=special, ts=ts, verbose=verbose)

        return AEXP(lt=self.lt, rt=rt)

    def peelme(self, data):
        """
        Go through each nesting (aexp), generate a SMT formula, and checks its satisfiability.


        Examples:

        ### sage: data = {'C':{1: [(5,)], 2: [(4,)], 4: [(6,)], 5: [(1,)], 6: [(2,), (3,)], 8: [(0,)]},\
        'B': {0: [(4,)], 1: [(0,), (3,), (6,)], 7: [(5,)], -3: [(1,)], 5: [(2,)]},\
        'A':{1: [(1,)], -3: [(2,)], 7: [(0,)]}}

        ### sage: AEXP({'root':'A','children':[None]}, \
        {'root': 'B','children':[{'root':'C','children':[None]}]}).peelme(data=data)
        ['lambda A,B,C,i1: A[i1] == B[C[2*i1 + 1]]']

        ### sage: data = {'C':{0:[(0,),(3,)],9:[(1,),(8,)],7:[(2,),(5,)], 1:[(4,)],8:[(6,)],17:[(7,)]},\
        'B':{71:[(5,),(7,)],74:[(6,),(8,)],81:[(17,)]},\
        'A':{71:[(0,)],74:[(1,)],81:[(2,)]}}
        ### sage: AEXP({'root':'A','children':[None]},\
        {'root':'B','children':[{'root':'C','children':[None]}]}).peelme(data=data)
        ['lambda A,B,C,i1: A[i1] == B[C[i1 + 5]]']

        ### sage: data = {'A':{17:[(0,0)],8:[(0,1)],12:[(1,0)],3:[(1,1)]},\
        'C':{0:[(0,)],17:[(1,)],8:[(2,)],3:[(3,),(4,)]},\
        'D':{1:[(0,)],9:[(1,),(3,)],0:[(2,)]},\
        'add': {17:[(8,9),(17,0)],8:[(8,0)],12:[(3,9),(0,12)],3:[(3,0)]}}
        ### sage: rs = AEXP({'root':'A','children':[None]}, \
        {'root':'add','children':[{'root':'C' , 'children':[None]}, \
        {'root':'D','children':[None]}]}).peelme(data=data)

        ### sage: print '\n'.join(sorted(rs,key=str))
        lambda A,add,C,D,i1: A[i1] == add(C[2*i1 + 2],D[1])
        lambda A,add,C,D,i1: A[i1] == add(C[2*i1 + 2],D[3])
        lambda A,add,C,D,i1: A[i1] == add(C[i1 + 2],D[1])
        lambda A,add,C,D,i1: A[i1] == add(C[i1 + 2],D[3])

        """

        def _gen_template(iv, sp):
            return self.gen_template(iv, sp)

        vi = [[(v, ids) for ids in idxs]
              for v, idxs in data[self.lt.root].items()]
        vi = CM.vflatten(vi, list)

        sts = [_gen_template(ids, sp=len(vi) == 1).rt for _, ids in vi]

        formula = [rh.gen_formula(v, data) for (v, _), rh in zip(vi, sts)]

        formula = Miscs._f(formula, 'and', is_real=False)

        if formula is None:
            return []

        #from common_z3 import get_models
        from z3util import get_models
        ms = get_models(formula, k=10)
        if not isinstance(ms, list):  # no model, formula is unsat, i.e. no relation
            return []

        assert ms

        from smt_z3py import SMT_Z3
        ds = [SMT_Z3.get_constraints(m, result_as_dict=True) for m in ms]

        # generate the full expression
        template = _gen_template(None, False)

        rs = [template.__str__(leaf_content=d, do_lambda_format=True)
              for d in ds]

        assert all(is_str(x) for x in rs)

        return rs

    ##### Static methods for AEXP #####

    @staticmethod
    def gen_aexps(nodes, xinfo, data):
        """
        arrs = [a,b,c]
        returns a=allpostrees(b,c)  , b = allpostrees(a,b)  , etc

        ### sage: nodes = map(Tree,[ \
        {'root':'A','children':[None]}, \
        {'root':'B','children':[None]}, \
        {'root':'C','children':[None]}])

        ### sage: data = {'A':{1: [(1,)], -3: [(2,)], 7: [(0,)]},\
        'B':{0: [(4,)], 1: [(0,), (3,), (6,)], 7: [(5,)], -3: [(1,)], 5: [(2,)]},\
        'C': {1: [(5,)], 2: [(4,)], 4: [(6,)], 5: [(1,)], 6: [(2,), (3,)], 8: [(0,)]}}
        ### sage: aexps = AEXP.gen_aexps(nodes, xinfo={'All': ['A', 'B', 'C'], \
        'Const': [], 'Assume': [], 'Global': [], 'ZDims': {'A': 1, 'C': 1, 'B': 1}, \
        'Expect': [], 'ExtFun': [], 'Input': [], 'Output': []}, data=data)
        ### sage: print map(str,aexps)
        ['A[i1] == B[C[(i1)_]]', 'A[i1] == B[(i1)_]']

        ### sage: nodes = map(Tree,[{'root':'A','children':[None]}, {'root':'C','children':[None]}, {'root':'B','children':[None]}])



        ### sage: aexps = AEXP.gen_aexps(nodes, xinfo={'All': ['A', 'B', 'C'], \
        'Const': [], 'Assume': [], 'Global': [], 'ZDims': {'A': 1, 'C': 1, 'B': 1}, \
        'Expect': [], 'ExtFun': [], 'Input': [], 'Output': []}, data={})
        ### sage: print '\n'.join(['{}. {}'.format(i,a) for i,a in enumerate(aexps)])
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


        ### sage: nodes = map(Tree,[ \
        {'root':'A','children':[None]}, \
        {'root':'C','children':[None]}, \
        {'root':'B','children':[None]}])

        ### sage: aexps = AEXP.gen_aexps(nodes, xinfo={'All': ['A', 'B', 'C'], \
        'Const': [], 'Assume': [], 'Global': [], 'ZDims': {'A': 1, 'C': 1, 'B': 1}, \
        'Expect': [], 'ExtFun': [], 'Input': [], 'Output': ['C']}, data={})
        ### sage: print '\n'.join(['{}. {}'.format(i,a) for i,a in enumerate(aexps)])
        0. C[i1] == A[B[(i1)_]]
        1. C[i1] == A[(i1)_]
        2. C[i1] == B[A[(i1)_]]
        3. C[i1] == B[(i1)_]

        """
        assert isinstance(nodes, list) and \
            all(isinstance(x, Tree) and x.is_node for x in nodes)
        assert isinstance(xinfo, dict)

        blacklist = AEXP.gen_blacklist(xinfo)

        # Generate nestings
        def _gt(nodes, ln):
            if ln.root not in data:
                vss = None
            else:
                vss = data[ln.root].keys()
                assert all(not isinstance(v, list) for v in vss)
                vss = [tuple([v]) for v in vss]

            rs = Tree.gen_trees(nodes, vss, blacklist, data)
            return rs

        # Construct an AEXP

        if xinfo['Output']:
            # x = a[b[...]], x in output vars and a,b not in output vars
            anodes, lnodes = \
                CM.vpartition(nodes, lambda x: x.root in xinfo['Output'])

            aexps = [[AEXP(_ga(ln), rn) for rn in _gt(anodes, ln)]
                     for ln in lnodes]

        else:
            aexps = []
            # print(nodes)
            for i, node in enumerate(nodes):
                lt = Tree(node.root, [None] * len(node.children), node.commute)

                others = Tree.uniq(nodes[:i] + nodes[i+1:], node)
                # print(node)
                # print(others)
                nestings = _gt(others, node)
                for nesting in nestings:
                    aexp = AEXP(lt, nesting)
                    aexps.append(aexp)

            # aexps = [[AEXP(_ga(ln), rn) for rn in _gt(CM.vsetdiff(nodes, [ln]), ln)]
            #          for ln in nodes]

        # filter out unlikely array expressions
        aexps = [a for a in aexps if a.is_ok(xinfo)]

        print('* gen_aexps [{}]: {} expressions generated'
              .format(','.join(map(lambda x: str(x.root), nodes)), len(aexps)))
        print('\n'.join(f'{i}. {a}' for i, a in enumerate(aexps)))
        return aexps

    @staticmethod
    def gen_blacklist(xinfo):
        """
        Use manual inputs to reduce the number of generated nestings

        Examples:

        ### sage: AEXP.gen_blacklist({'All':['R','A','B','D','E','xor','g'], \
        'Input':['A','B'],'Output':['R'],'Global':[],'Const':[], \
        'ExtFun':['xor'],'Global':['g']})
        OrderedDict([('A', ['R', 'A', 'B', 'D', 'E', 'xor', 'g']),
                     ('B', ['R', 'A', 'B', 'D', 'E', 'xor', 'g']),
                     ('xor', [None]), ('g', [None]),
                     ('R', ['R', 'A', 'B', 'D', 'E', 'xor', 'g', None])])

        """

        allVars = xinfo['All']
        inputVars = xinfo['Input']
        outputVars = xinfo['Output']
        globalVars = xinfo['Global']
        constVars = xinfo['Const']
        extFuns = [x for x in xinfo['ExtFun']]

        # Inputs must be leaves
        # e.g., a[i] = x[y[i']] is not possible
        # e.g., a[i] = xor[x[i'][y[i']]
        inputsLeaves = [{inp: allVars} for inp in inputVars]

        # Const must be leaves
        constLeaves = [{c: allVars} for c in constVars]

        # Extfuns are never leaves
        # e.g.,  r[i] = a[b[xor[i'][i']]]  is not possible
        extfunsNotLeaves = [{ef: [None]} for ef in extFuns]

        # Globals are never leaves
        globalsNotLeaves = [{gv: [None]} for gv in globalVars]

        # Outputs should never be part of the tree
        outputsNotInTree = [{oup: allVars + [None]} for oup in outputVars]

        ds = inputsLeaves+constLeaves + extfunsNotLeaves + \
            globalsNotLeaves + outputsNotInTree
        rs = CM.merge_dict(ds)

        return rs


class ExtFun(str):

    efdict = {
        'add': (lambda x, y: QQ(ZZ(x) + ZZ(y)), 2, True),
        'sub': (lambda x, y: QQ(ZZ(x) - ZZ(y)), 2, False),  # not commute
        'xor': (lambda x, y: QQ(ZZ(x).__xor__(ZZ(y))), 2, True),
        'xor_xor': (lambda x, y, z: QQ(ZZ(x).__xor__(ZZ(y)).__xor__(ZZ(z))), 3, True),
        'mod4': (lambda x: QQ(ZZ(x) % 4),   1, True),
        'mod255': (lambda x: QQ(ZZ(x) % 255), 1, True),
        'mul4': (lambda x: QQ(ZZ(x) * 4),   1, True),
        'div4': (lambda x: QQ(ZZ(x) // 4),  1, True)  # commute ??
    }

    def __new__(cls, fn):
        assert isinstance(fn, str), fn
        return super().__new__(cls, fn.strip())

    def get_fun(self):
        """
        ### sage: ExtFun('xor').get_fun()(*[7,15])
        8
        ### sage: ExtFun('xor').get_fun()(8,9)
        1
        ### sage: ExtFun('xor').get_fun()(18,-9)
        -27
        ### sage: ExtFun('sub').get_fun()(128,1)
        127
        ### sage: ExtFun('sub').get_fun()(0,1)
        -1
        ### sage: ExtFun('xor').get_fun()(10,128)
        138
        ### sage: ExtFun('xor').get_fun()(128,10)
        138
        ### sage: ExtFun('mod4').get_fun()(128)
        0
        ### sage: ExtFun('mod4').get_fun()(127)
        3
        ### sage: ExtFun('mod4').get_fun()(1377)
        1
        ### sage: ExtFun('mod4').get_fun()(1378)
        2
        ### sage: ExtFun('mod4').get_fun()(1379)
        3
        ### sage: ExtFun('mod4').get_fun()(1380)
        0
        ### sage: ExtFun('div4').get_fun()(127)
        31
        ### sage: ExtFun('div4').get_fun()(128)
        32
        ### sage: ExtFun('div4').get_fun()(126)
        31
        """
        return ExtFun.efdict[self][0]

    def get_nargs(self):
        """
        Returns the number of function arguments

        Examples:
        ### sage: ExtFun('sub').get_nargs()
        2
        ### sage: ExtFun('something').get_nargs()
        Traceback (most recent call last):
        ...
        KeyError: 'something'

        """
        return ExtFun.efdict[self][1]

    @property
    def commute(self):
        """
        Returns true if the function is commutative

        ### sage: ExtFun('sub').commute
        False
        ### sage: ExtFun('add').commute
        True
        ### sage: ExtFun('something').commute
        False
        """
        try:
            return ExtFun.efdict[self][2]
        except KeyError:
            """
            If we don't know anything about the function, then
            the default is non commutative.
            """
            return False

    def gen_data(self, avals, doDict):
        """
        Note: did not use caching because caching makes it slower.
        Probably because these functions are too simple that
        doesn't worth the caching overhead
        Examples:

        ### sage: ExtFun('add').gen_data([1,7,9,-1],doDict=False)
        [2, 8, 10, 0, 14, 16, 6, 18, -2, 1, 7, 9, -1]

        ### sage: ExtFun('add').gen_data([[1,7,9,-1]],doDict=False)
        [2, 8, 10, 0, 14, 16, 6, 18, -2, 1, 7, 9, -1]

        ### sage: ExtFun('add').gen_data([[1,7,9,-1]],doDict=True)
        OrderedDict([('add', OrderedDict([(2, [(1, 1)]), (8, [(1, 7), (9, -1)]), (10, [(1, 9)]), (0, [(1, -1)]), (14, [(7, 7)]), (16, [(7, 9)]), (6, [(7, -1)]), (18, [(9, 9)]), (-2, [(-1, -1)])]))])

        ### sage: ExtFun('sub').gen_data([[1,2],[5,6]], doDict=False)
        [0, -1, -4, -5, 1, -3, 4, 3, 5, 2, 6]
        ### sage: ExtFun('sub').gen_data([[1,2,5,6]], doDict=False)
        [0, -1, -4, -5, 1, -3, 4, 3, 5, 2, 6]
        ### sage: ExtFun('sub').gen_data([1,2,5,6], doDict=False)
        [0, -1, -4, -5, 1, -3, 4, 3, 5, 2, 6]

        ### sage: ExtFun('sub').gen_data([[1,2],[5,6]],doDict=True)
        OrderedDict([('sub', OrderedDict([(0, [(1, 1), (2, 2), (5, 5), (6, 6)]), (-1, [(1, 2), (5, 6)]), (-4, [(1, 5), (2, 6)]), (-5, [(1, 6)]), (1, [(2, 1), (6, 5)]), (-3, [(2, 5)]), (4, [(5, 1), (6, 2)]), (3, [(5, 2)]), (5, [(6, 1)])]))])

        ### sage: ExtFun('add').gen_data([[1,2,3,4],[5,6],[7,8,9]], doDict=False)
        [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 1]

        ### sage: ExtFun('add').gen_data([[1,2,3,4],[5,6],[7,8,9]], doDict=True)
        OrderedDict([('add', OrderedDict([(2, [(1, 1)]), (3, [(1, 2)]), (4, [(1, 3), (2, 2)]), (5, [(1, 4), (2, 3)]), (6, [(1, 5), (2, 4), (3, 3)]), (7, [(1, 6), (2, 5), (3, 4)]), (8, [(1, 7), (2, 6), (3, 5), (4, 4)]), (9, [(1, 8), (2, 7), (3, 6), (4, 5)]), (10, [(1, 9), (2, 8), (3, 7), (4, 6), (5, 5)]), (11, [(2, 9), (3, 8), (4, 7), (5, 6)]), (12, [(3, 9), (4, 8), (5, 7), (6, 6)]), (13, [(4, 9), (5, 8), (6, 7)]), (14, [(5, 9), (6, 8), (7, 7)]), (15, [(6, 9), (7, 8)]), (16, [(7, 9), (8, 8)]), (17, [(8, 9)]), (18, [(9, 9)])]))])
        """

        avals = vset(CM.vflatten(avals))
        alists = [avals] * self.get_nargs()
        idxs = CartesianProduct(*alists).list()
        fun_vals = [self.get_fun()(*idx) for idx in idxs]

        if doDict:  # create dict
            cs = zip(fun_vals, idxs)
            cs = [(fv, tuple(idx)) for (fv, idx) in cs]

            d = CM.create_dict(cs)

            if self.commute:
                # [(1,2),(2,1),(2,2)] => [(1,2),(2,2)]
                d = OrderedDict([(k, vset(v, Set)) for k, v in d.items()])

            rs = OrderedDict()
            rs[self] = d

            print('fun: {}, fvals {}, idxs {}'
                  .format(self, len(d.keys()), len(idxs)))

        else:  # returns fun_vals as well as the orig avals
            rs = vset(fun_vals + avals)

        return rs

    @staticmethod
    def gen_ef_data(extfuns, avals):
        """
        create representations for extfuns
        Note: the order of F matters (see example below when add,xor,xor_xor gens 63
        but xor,add,xor_xor gens 124.

        Examples

        ### sage: mlog.set_level(VLog.DEBUG)
        ### sage: rs = ExtFun.gen_ef_data(map(ExtFun,['add','xor','xor_xor']),[1,2,256,9]); len(rs[0].values()[0])
        dig_miscs:Debug:gen_ef_data([add,xor,xor_xor],|avals|=4)
        dig_miscs:Debug:fun: add, fvals 30, idxs 64
        dig_miscs:Debug:fun: xor, fvals 8, idxs 64
        dig_miscs:Debug:fun: xor_xor, fvals 16, idxs 1331
        30

        ### sage: rs = ExtFun.gen_ef_data(map(ExtFun,['xor','add','xor_xor']),[1,2,256,9]); len(rs[0].values()[0])
        dig_miscs:Debug:gen_ef_data([xor,add,xor_xor],|avals|=4)
        dig_miscs:Debug:fun: xor, fvals 8, idxs 64
        dig_miscs:Debug:fun: add, fvals 30, idxs 64
        dig_miscs:Debug:fun: xor_xor, fvals 95, idxs 2197
        8
        """

        print('gen_ef_data([{}],|avals|={})'
              .format(','.join(map(str, extfuns)), len(CM.vflatten(avals))))

        if len(extfuns) == 1:
            F_avals = [avals]
        else:
            assert vall_uniq(map(lambda f: f, extfuns)), \
                'extfuns list cannot contain duplicate'

            F_rest = [CM.vsetdiff(extfuns, [f]) for f in extfuns]

            F_avals = [ExtFun.get_outvals(tuple(fs), tuple(avals))
                       for fs in F_rest]

        F_d = [fn.gen_data(f_aval, doDict=True)
               for fn, f_aval in zip(extfuns, F_avals)]

        return F_d

    @cached_function
    def get_outvals(extfuns, avals):
        """
        Recursive function that returns the all possible input values

        [f,g,h],[avals] =>  f(g(h(avals)))

        Examples:

        ### sage: ExtFun.get_outvals(tuple(map(ExtFun,['sub'])),tuple([1,2,256]))
        [0, -1, -255, 1, -254, 255, 254, 2, 256]
        ### sage: ExtFun.get_outvals(tuple(map(ExtFun,['xor_xor'])),tuple([1,2,256]))
        [1, 2, 256, 259]
        ### sage: ExtFun.get_outvals(tuple(map(ExtFun,['xor_xor','add'])),tuple([1,2,256]))
        [2, 3, 257, 4, 258, 512, 1, 256]
        ### sage: ExtFun.get_outvals(tuple(map(ExtFun,['add','xor_xor'])),tuple([1,2,256]))
        [1, 2, 256, 259]
        """

        assert len(extfuns) >= 1
        assert all(isinstance(f, ExtFun) for f in extfuns)

        if len(extfuns) > 1:
            avals = ExtFun.get_outvals(extfuns[1:], avals)
        else:
            avals = extfuns[0].gen_data(avals, doDict=False)

        return avals

    @staticmethod
    def gen_extfuns(tc, xinfo):
        """
        Returns a list of dicts representing extfuns
        The values of the extfuns are customized over the given tc

        Examples:

        ### sage: mlog.set_level(VLog.DEBUG)

        ### sage: ExtFun.gen_extfuns(tc={'X':[1,7,9,15]}, xinfo={'ExtFun':['add'],'Output':[]})
        dig_miscs:Debug:gen_extfuns: 1 ext funs [add]
        dig_miscs:Debug:gen_ef_data([add],|avals|=4)
        dig_miscs:Debug:fun: add, fvals 9, idxs 16
        [OrderedDict([('add', OrderedDict([(2, [(1, 1)]), (8, [(1, 7)]), (10, [(1, 9)]), (16, [(1, 15), (7, 9)]), (14, [(7, 7)]), (22, [(7, 15)]), (18, [(9, 9)]), (24, [(9, 15)]), (30, [(15, 15)])]))])]


        ### sage: _ = ExtFun.gen_extfuns({'x': [0, 1, 3], 'y': [2, 5, 1], 'z': [153, 173, 184, 65]}, \
        {'Output': ['z'], 'ExtFun': ['sub', 'add']})
        dig_miscs:Debug:gen_extfuns: 2 ext funs [sub, add]
        dig_miscs:Debug:gen_ef_data([sub,add],|avals|=5)
        dig_miscs:Debug:fun: sub, fvals 21, idxs 100
        dig_miscs:Debug:fun: add, fvals 21, idxs 121

        ### sage: ExtFun.gen_extfuns({'x': [0, 1, 3], 'y': [2, 5, 1], 'z': [153, 173, 184, 65]}, \
        {'Output': ['z'], 'ExtFun': ['xor', 'mod255']})
        dig_miscs:Debug:gen_extfuns: 2 ext funs [xor, mod255]
        dig_miscs:Debug:gen_ef_data([xor,mod255],|avals|=5)
        dig_miscs:Debug:fun: xor, fvals 8, idxs 25
        dig_miscs:Debug:fun: mod255, fvals 8, idxs 8
        [OrderedDict([('xor', OrderedDict([(0, [(2, 2), (5, 5), (1, 1), (0, 0), (3, 3)]), (7, [(2, 5)]), (3, [(2, 1), (0, 3)]), (2, [(2, 0), (1, 3)]), (1, [(2, 3), (1, 0)]), (4, [(5, 1)]), (5, [(5, 0)]), (6, [(5, 3)])]))]), 
        OrderedDict([('mod255', OrderedDict([(0, [(0,)]), (7, [(7,)]), (3, [(3,)]), (2, [(2,)]), (1, [(1,)]), (4, [(4,)]), (5, [(5,)]), (6, [(6,)])]))])]


        ### sage: ExtFun.gen_extfuns({'x': [0, 1, 3], 'y': [2, 5, 1], 'z': [153, 173, 184, 65]}, \
        {'Output': ['z'], 'ExtFun': ['xor', 'mod255']})
        dig_miscs:Debug:gen_extfuns: 2 ext funs [xor, mod255]
        dig_miscs:Debug:gen_ef_data([xor,mod255],|avals|=5)
        dig_miscs:Debug:fun: xor, fvals 8, idxs 25
        dig_miscs:Debug:fun: mod255, fvals 8, idxs 8
        [OrderedDict([('xor', OrderedDict([(0, [(2, 2), (5, 5), (1, 1), (0, 0), (3, 3)]), (7, [(2, 5)]), (3, [(2, 1), (0, 3)]), (2, [(2, 0), (1, 3)]), (1, [(2, 3), (1, 0)]), (4, [(5, 1)]), (5, [(5, 0)]), (6, [(5, 3)])]))]), 
         OrderedDict([('mod255', OrderedDict([(0, [(0,)]), (7, [(7,)]), (3, [(3,)]), (2, [(2,)]), (1, [(1,)]), (4, [(4,)]), (5, [(5,)]), (6, [(6,)])]))])]


        ### sage: ExtFun.gen_extfuns({'R':[128,127,126,125], 'N':[128],'x': [0, 7]},{'Output': ['R'], 'ExtFun': ['sub']}) 
        dig_miscs:Debug:gen_extfuns: 1 ext funs [sub]
        dig_miscs:Debug:gen_ef_data([sub],|avals|=6)
        dig_miscs:Debug:fun: sub, fvals 25, idxs 36
        [OrderedDict([('sub', OrderedDict([(0, [(0, 0), (7, 7), (128, 128), (1, 1), (2, 2), (3, 3)]), (-7, [(0, 7)]), (-128, [(0, 128)]), (-1, [(0, 1), (1, 2), (2, 3)]), (-2, [(0, 2), (1, 3)]), (-3, [(0, 3)]), (7, [(7, 0)]), (-121, [(7, 128)]), (6, [(7, 1)]), (5, [(7, 2)]), (4, [(7, 3)]), (128, [(128, 0)]), (121, [(128, 7)]), (127, [(128, 1)]), (126, [(128, 2)]), (125, [(128, 3)]), (1, [(1, 0), (2, 1), (3, 2)]), (-6, [(1, 7)]), (-127, [(1, 128)]), (2, [(2, 0), (3, 1)]), (-5, [(2, 7)]), (-126, [(2, 128)]), (3, [(3, 0)]), (-4, [(3, 7)]), (-125, [(3, 128)])]))])]


        """
        assert isinstance(tc, dict), tc
        assert isinstance(xinfo, dict) and 'ExtFun' in xinfo, xinfo

        extfuns = [ExtFun(x) for x in xinfo['ExtFun']]

        if not extfuns:
            return []

        print('gen_extfuns: {} ext funs [{}]'
              .format(len(extfuns), ','.join(extfuns)))

        # don't consider values of 'output' arrays
        avals = [tc[a] for a in tc if a not in xinfo['Output']]

        # the range of the outputs are also included to have e.g. R[i] = sub(N,i)
        lo = map(len, [tc[a] for a in tc if a in xinfo['Output']])

        if lo:
            avals = avals + [range(max(lo))]

        avals = vset(CM.vflatten(avals))

        # generate new arrays representing external functions
        ds = ExtFun.gen_ef_data(extfuns, avals)

        return ds

    @staticmethod
    def parse_extvar(ev):
        """
        Return a tuple (var, value)

        Examples:
        ### sage: ExtFun.parse_extvar('mpi 3.14')
        OrderedDict([(mpi, 157/50)])

        ### sage: ExtFun.parse_extvar(' r [1, 2,  3] ')
        OrderedDict([(r, [1, 2, 3])])

        ### sage: ExtFun.parse_extvar('0wrongvarname 3')
        Traceback (most recent call last):
        ...
        AssertionError: 0wrongvarname
        """
        ev = ev.strip()

        assert ev.count(' ') >= 1, ev

        idx = ev.find(' ')

        vname = ev[:idx].strip()
        vname = ReadFile.strToVar(vname)

        vval = ev[idx:].strip()
        vval = ReadFile.formatter(vval)
        vval = ReadFile.strToRatOrList(vval, is_num_val=None)
        return OrderedDict([(vname, vval)])

    @staticmethod
    def gen_extvars(xinfo):
        """
        Returns a list of dicts representing extvars

        [{v1: 3.14},  {v2: [1,2,3]}]

        ### sage: mlog.set_level(VLog.DETAIL)

        ### sage: ExtFun.gen_extvars({'ExtVar' : ['mpi 3.1415', ' t 20.5 ',  'arr [1,[2,3,4]]']})
        dig_miscs:Debug:gen_extvar: 3 ext funs found in xinfo['ExtVar']
        dig_miscs:Detail:mpi 3.1415,  t 20.5 , arr [1,[2,3,4]]
        [OrderedDict([(mpi, 6283/2000)]), OrderedDict([(t, 41/2)]), OrderedDict([(arr, [1, [2, 3, 4]])])]

        ### sage: ExtFun.gen_extvars({'ExtVar' : []})
        []


        """
        assert isinstance(xinfo, dict) and 'ExtVar' in xinfo, xinfo

        extvars = xinfo['ExtVar']
        if not extvars:
            return []

        print(
            f"gen_extvar: {len(extvars)} ext funs found in xinfo['ExtVar']")

        print(', '.join(extvars))
        extvars = map(ExtFun.parse_extvar, extvars)
        return extvars


def gen_deg(nss, ntcs, nts, max_deg=7):
    """
    Generates a degree wrt to a (maximum) number of terms and traces

    nss: number of symbols (variables)
    ntcs: number of traces
    nts: number of (max) terms

    Examples:

    ### sage: [(i,gen_deg(i,ntcs=Infinity,nts=100)) for i in range(1,14)]
    [(1, 7),
    (2, 7),
    (3, 6),
    (4, 4),
    (5, 3),
    (6, 3),
    (7, 2),
    (8, 2),
    (9, 2),
    (10, 2),
    (11, 2),
    (12, 2),
    (13, 1)]

    ### sage: [(i,gen_deg(i,ntcs=Infinity,nts=200)) for i in range(1,14)]
    [(1, 7),
    (2, 7),
    (3, 7),
    (4, 5),
    (5, 4),
    (6, 3),
    (7, 3),
    (8, 3),
    (9, 2),
    (10, 2),
    (11, 2),
    (12, 2),
    (13, 2)]

    ### sage: [(i, gen_deg(i,ntcs=i,nts=200)) for i in range(1,14)]
    [(1, 1),
    (2, 1),
    (3, 1),
    (4, 1),
    (5, 1),
    (6, 1),
    (7, 1),
    (8, 1),
    (9, 1),
    (10, 1),
    (11, 1),
    (12, 1),
    (13, 1)]

    ### sage: [(i, gen_deg(i,ntcs=100,nts=200)) for i in range(1,14)]
    [(1, 7),
    (2, 7),
    (3, 6),
    (4, 4),
    (5, 3),
    (6, 3),
    (7, 2),
    (8, 2),
    (9, 2),
    (10, 2),
    (11, 2),
    (12, 2),
    (13, 1)]


    ### sage: [(i, gen_deg(i,ntcs=50,nts=100)) for i in range(1,14)] 
    [(1, 7),
    (2, 7),
    (3, 4),
    (4, 3),
    (5, 2),
    (6, 2),
    (7, 2),
    (8, 2),
    (9, 1),
    (10, 1),
    (11, 1),
    (12, 1),
    (13, 1)]
    """
    assert nss >= 1, nss
    assert ntcs >= nss, (ntcs, nss)
    assert nts >= nss, (nts, nss)
    assert max_deg >= 1, max_deg

    for d in range(1, max_deg+1):
        if d == max_deg:
            return d

        # look ahead
        nterms = binomial(nss + d+1, d+1)
        if nterms > nts or nterms > ntcs:
            return d


def gen_terms(deg, ss):
    """
    Generates a list of terms from the given list of vars and deg
    the number of terms is len(rs) == binomial(len(ss)+d, d)

    Note: itertools is faster than Sage's MultichooseNK(len(ss)+1,deg)


    Examples:

    ### sage: ts = gen_terms(3,list(var('a b')))
    ### sage: assert ts == [1, a, b, a^2, a*b, b^2, a^3, a^2*b, a*b^2, b^3]

    ### sage: ts = gen_terms(3,var('a b c d e f'))
    ### sage: ts
    [1, a, b, c, d, e, f,
    a^2, a*b, a*c, a*d, a*e, a*f,
    b^2, b*c, b*d, b*e, b*f, c^2, c*d, c*e, c*f,
    d^2, d*e, d*f, e^2, e*f, f^2, a^3, a^2*b, a^2*c, a^2*d, a^2*e,
    a^2*f, a*b^2, a*b*c, a*b*d, a*b*e, a*b*f, a*c^2, a*c*d, a*c*e,
    a*c*f, a*d^2, a*d*e, a*d*f, a*e^2, a*e*f, a*f^2,
    b^3, b^2*c, b^2*d, b^2*e, b^2*f, b*c^2, b*c*d, b*c*e, b*c*f, b*d^2,
    b*d*e, b*d*f, b*e^2, b*e*f, b*f^2, c^3, c^2*d, c^2*e, c^2*f, c*d^2,
    c*d*e, c*d*f, c*e^2, c*e*f, c*f^2, d^3, d^2*e, d^2*f, d*e^2, d*e*f,
    d*f^2, e^3, e^2*f, e*f^2, f^3]

    """
    assert deg >= 0, deg
    assert ss and all(s.is_symbol() for s in ss), ss

    ss_ = ([SR(1)] if isinstance(ss, list) else (SR(1),)) + ss
    combs = itertools.combinations_with_replacement(ss_, deg)
    ts = [myprod(c) for c in combs]
    return ts


def _gen_terms_mpp(ts, blacklist):
    """
    Generate mpp terms of the form
    max(c1+x1,...,cn+xn,c0) >= xi,
    where ci are in cs (e.g., 0,-oo for max plus)

    ### sage: var('x y z t s w')
    (x, y, z, t, s, w)

    ### sage: ts = _gen_terms_mpp([x,y,z,t,s],[]); len(ts)
    145

    ### sage: ts = _gen_terms_mpp([x,y,z],[]); ts; len(ts)
    [([x, y, 0], z),
    ([x, y], z),
    ([x, z, 0], y),
    ([x, z], y),
    ([x, 0], y),
    ([x, 0], z),
    ([x], y),
    ([x], z),
    ([y, z, 0], x),
    ([y, z], x),
    ([y, 0], x),
    ([y, 0], z),
    ([y], z),
    ([z, 0], x),
    ([z, 0], y),
    ([0], x),
    ([0], y),
    ([0], z)]
    18


    ### sage: ts = _gen_terms_mpp([x,y,z],['z']); ts; len(ts)
    [([x, y, 0], z),
    ([x, y], z),
    ([x, 0], z),
    ([x], z),
    ([y, 0], z),
    ([y], z),
    ([z, 0], x),
    ([z, 0], y),
    ([0], x),
    ([0], y)]
    10

    ### sage: ts = _gen_terms_mpp([x,y,z],['x','y']); ts; len(ts)
    [([x, y, 0], z),
    ([x, y], z),
    ([x, 0], z),
    ([x], z),
    ([y, 0], z),
    ([y], z),
    ([z, 0], x),
    ([z, 0], y),
    ([0], z)]
    9

    ### sage: ts = _gen_terms_mpp([x,y,z],['x','y','z']); len(ts)
    0

    ### sage: ts = _gen_terms_mpp([x,y,z,w],[]); ts; len(ts)
    [([x, y, z, 0], w),
    ([x, y, z], w),
    ([x, y, w, 0], z),
    ([x, y, w], z),
    ([x, y, 0], z),
    ([x, y, 0], w),
    ([x, y], z),
    ([x, y], w),
    ([x, z, w, 0], y),
    ([x, z, w], y),
    ([x, z, 0], y),
    ([x, z, 0], w),
    ([x, z], y),
    ([x, z], w),
    ([x, w, 0], y),
    ([x, w, 0], z),
    ([x, w], y),
    ([x, w], z),
    ([x, 0], y),
    ([x, 0], z),
    ([x, 0], w),
    ([x], y),
    ([x], z),
    ([x], w),
    ([y, z, w, 0], x),
    ([y, z, w], x),
    ([y, z, 0], x),
    ([y, z, 0], w),
    ([y, z], x),
    ([y, z], w),
    ([y, w, 0], x),
    ([y, w, 0], z),
    ([y, w], x),
    ([y, w], z),
    ([y, 0], x),
    ([y, 0], z),
    ([y, 0], w),
    ([y], z),
    ([y], w),
    ([z, w, 0], x),
    ([z, w, 0], y),
    ([z, w], x),
    ([z, w], y),
    ([z, 0], x),
    ([z, 0], y),
    ([z, 0], w),
    ([z], w),
    ([w, 0], x),
    ([w, 0], y),
    ([w, 0], z),
    ([0], x),
    ([0], y),
    ([0], z),
    ([0], w)]
    54


    ### sage: ts = _gen_terms_mpp([x,y,z,w],['z','w']); ts; len(ts)
    [([x, y, 0], z),
    ([x, y, 0], w),
    ([x, y], z),
    ([x, y], w),
    ([x, 0], z),
    ([x, 0], w),
    ([x], z),
    ([x], w),
    ([y, 0], z),
    ([y, 0], w),
    ([y], z),
    ([y], w),
    ([z, w, 0], x),
    ([z, w, 0], y),
    ([z, w], x),
    ([z, w], y),
    ([z, 0], x),
    ([z, 0], y),
    ([w, 0], x),
    ([w, 0], y),
    ([0], x),
    ([0], y)]
    22

    ### sage: ts = _gen_terms_mpp([x,y,z,w],['x','y','z']); ts; len(ts)
    [([x, y, z, 0], w),
    ([x, y, z], w),
    ([x, y, 0], w),
    ([x, y], w),
    ([x, z, 0], w),
    ([x, z], w),
    ([x, 0], w),
    ([x], w),
    ([y, z, 0], w),
    ([y, z], w),
    ([y, 0], w),
    ([y], w),
    ([z, 0], w),
    ([z], w),
    ([w, 0], x),
    ([w, 0], y),
    ([w, 0], z),
    ([0], w)]
    18


    ### sage: ts = _gen_terms_mpp([x,y],[]); ts; len(ts)
    [([x, 0], y), ([x], y), ([y, 0], x), ([0], x), ([0], y)]
    5
    """

    assert is_iterable(ts), ts
    assert is_iterable(blacklist), blacklist

    if len(blacklist) > 0 and all(str(t) in blacklist for t in ts):
        return []

    ts_ext = list(ts) + [0]
    d = {}
    rs = []
    ccs = itertools.product(*([[0, oo]]*len(ts_ext)))
    for cs in ccs:
        lh = [c+t for c, t in zip(ts_ext, cs) if t != oo]

        # ignore oo >= x1 + c
        if not lh:
            continue

        # ignore x >= x + c ~> 0 >= c
        # ignore [y],x if [x],y already in
        if len(lh) == 1:
            l0 = lh[0]
            ts_ = []

            for t in ts:
                if l0 != t and (t, l0) not in d:
                    ts_.append(t)
                    d[(l0, t)] = None

        else:
            # ignore (lh, xi)  if xi in lh, e.g., [x,y,0] x
            # this is because [x,y,0] x  is implied by [y,0] x
            ts_ = [t for t in ts if t not in lh]

        rs.extend([(lh, t) for t in ts_])

    if blacklist:
        return rs

    # remove ones in the blacklist
    # using dict as below is much faster
    S1 = dict([(t, None) for t in ts if str(t) in blacklist])
    S2 = dict([(t, None) for t in ts if str(t) not in blacklist])

    S1[0] = None
    S2[0] = None

    def is_ok(s1, s2):
        """
        Ok when
        subset(l,b1) and subset(r,b2)
        or subset(l,b2) and subset(r,b1)
        """
        def is_subset(s0, s1): return all(s in s1 for s in s0)

        if is_subset(s1+s2, S1):  # if all involved vars in blacklist
            return False

        if is_subset(s1, S1) and is_subset(s2, S2):
            return True

        if is_subset(s1, S2) and is_subset(s2, S1):
            return True

        return False

    rs = [(l, r) for (l, r) in rs if is_ok(l, [r])]

    return rs


# def gen_terms_fixed_coefs(ts, subset_siz, blacklist, is_mpp):
#     """
#     Generates a list of terms with fixed coefficients
#     Generate |cs|^|ts| exprs

#     ts= [x,y,z]  , cs = [0,1]  |exrs| 2^3 = 8

#     ### sage: var('x y z t s u')
#     (x, y, z, t, s, u)

#     ### sage: gen_terms_fixed_coefs([x,y^2],2,[],is_mpp=False)
#     [-y^2 - x, -x, y^2 - x, -y^2, y^2, -y^2 + x, x, y^2 + x]


#     ### sage: gen_terms_fixed_coefs([x,z],2,[],is_mpp=False)
#     [-x - z, -x, -x + z, -z, z, x - z, x, x + z]

#     ### sage: len(gen_terms_fixed_coefs([x,y,z,t,s,u],5,[],is_mpp=False))
#     664

#     ### sage: ts = gen_terms_fixed_coefs([x,y,z],2,[],is_mpp=True); ts; len(ts)
#     [([x], y), ([0], x), ([0], y), ([x], z), ([0], z), ([y], z), ([x, 0], y), ([y, 0], x), ([x, 0], z), ([z, 0], x), ([y, 0], z), ([z, 0], y)]
#     12


#     ### sage: ts = gen_terms_fixed_coefs([x,y,z],3,[],is_mpp=True); ts; len(ts)
#     [([x], y), ([x], z), ([y], z), ([0], x), ([0], y), ([0], z), ([x, y], z), ([x, z], y), ([x, 0], y), ([x, 0], z), ([y, z], x), ([y, 0], x), ([y, 0], z), ([z, 0], x), ([z, 0], y), ([x, y, 0], z), ([x, z, 0], y), ([y, z, 0], x)]
#     18

#     ### sage: ts = gen_terms_fixed_coefs([x,y],1,[],is_mpp=True); ts; len(ts)
#     [([0], x), ([0], y)]
#     2

#     ### sage: gen_terms_fixed_coefs([x],2,[],is_mpp=False)
#     dig_miscs:Warn:|ts|=1 < subset size=2
#     []

#     """

#     if __debug__:
#         assert vall_uniq(ts) and all(is_sage_expr(t) for t in ts), ts


#         if subset_siz > len(ts):
#             mlog.warn("|ts|={} < subset size={}"
#                         .format(len(ts),subset_siz))
#             return []


#     rs = []
#     for ts_subset in itertools.combinations(ts, subset_siz):
#         if is_mpp:
#             rs.extend(_gen_terms_mpp(ts_subset,blacklist=blacklist))
#         else:
#             css = itertools.product(*([[-1,0,1]]*len(ts_subset)))

#             r = (sum(c*t for c,t in zip(ts_subset,cs))
#                  for cs in css if not all(c == 0 for c in cs))

#             rs.extend(r)


#     if is_mpp:
#         rs = vset(rs,idfun=repr)
#         rs = sorted(rs, key=lambda (lh,_) : len(lh))
#     else:
#         rs = vset(rs)
#     return rs


# def get_traces(tcs, ntcs, ntcs_extra):
#     """
#     ntcs : number of traces
#     ntcs_extra : number of extra traces

#     Examples:
#     ### sage: l=range(10)
#     ### sage: mlog.set_level(VLog.DEBUG)

#     ### sage: set_random_seed(0)
#     ### sage: l1,l2= get_traces(l,7,3); l1,l2,l
#     dig_miscs:Debug:Total traces 10, request (ntcs 7, ntcs_extra 3)
#     dig_miscs:Debug:mk_traces: |tcs1|=7, |tcs2|=3
#     ([5, 9, 8, 6, 7, 3, 2], [0, 4, 1], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9])

#     ### sage: mlog.set_level(VLog.WARN)

#     ### sage: set_random_seed(0)
#     ### sage: l1,l2= get_traces(l,3,7); l1,l2
#     ([5, 9, 8], [6, 7, 3, 2, 0, 4, 1])

#     ### sage: set_random_seed(0)
#     ### sage: l1,l2= get_traces(l,10,2); l1,l2
#     ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [])

#     ### sage: set_random_seed(0)
#     ### sage: l1,l2= get_traces(l,13,3); l1,l2
#     ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [])

#     ### sage: set_random_seed(0)
#     ### sage: l1,l2= get_traces(l,8,5); l1,l2
#     ([5, 9, 8, 6, 7, 3, 2, 0], [4, 1])

#     ### sage: set_random_seed(0)
#     ### sage: l1,l2= get_traces(l,0,3); l1,l2
#     ([], [5, 9, 8])

#     ### sage: l1,l2= get_traces(l,3,0); l1,l2
#     ([3, 0, 2], [])

#     """

#     assert isinstance(tcs, list) and tcs, tcs
#     assert ntcs >= 0, ntcs
#     assert ntcs_extra >= 0, ntcs_extra

#     print('Total traces {}, '
#                'request (ntcs {}, ntcs_extra {})'
#                .format(len(tcs), ntcs, ntcs_extra))

#     if len(tcs) <= ntcs:
#         tcs1 = tcs[:]
#         tcs2 = []
#     else:
#         # preserve the original tcs content
#         idxs = range(len(tcs))
#         shuffle(idxs)
#         tcs1 = [tcs[i] for i in idxs[:ntcs]]
#         tcs2 = [tcs[i] for i in idxs[ntcs:ntcs+ntcs_extra]]

#     print('mk_traces: |tcs1|={}, |tcs2|={} '
#                .format(len(tcs1), len(tcs2)))

#     return tcs1, tcs2


def adjust_arr_sizs(arrs, max_num_elems):
    """
    ### sage: mlog.set_level(VLog.WARN)

    ### sage: arrs = adjust_arr_sizs({'A':range(100),'B':range(200),'C':range(300)}, 200)
    ### sage: [len(c) for _, c in sorted(arrs.iteritems(), key= lambda (a,_): a)]
    [33, 67, 100]

    ### sage: arrs = adjust_arr_sizs({'A':[[1,2] for _ in range(50)],'B':range(200), 'C':range(300)}, 200)
    ### sage: [len(c) for _, c in sorted(arrs.iteritems(), key= lambda (a,_): a)]
    [16, 67, 100]


    """
    assert is_instance(arrs, dict), arrs

    arrslensdims = []

    for a, c in arrs.iteritems():
        l = len(c)
        dl = 0  # [1,2,3] -> dl = 0

        if isinstance(c[0], list):  # two dims
            # [[1],[2],[3]]  -> dl = 1, #[[1,2],[3,4]] -> dl = 2
            dl = len(c[0])
            l = l * dl

        arrslensdims.append((a, l, dl))

    sum_len = sum(l for _, l, _ in arrslensdims)

    if sum_len <= max_num_elems:
        return arrs

    arrs_new = OrderedDict()
    for a, l, dl in arrslensdims:
        l = round((max_num_elems*l)/sum_len)

        if dl >= 2:
            l = l / dl

        l = int(l)

        if len(arrs[a]) > l:
            # don't print this since otherwise too many outputs
            # print('Adjust size of arr {}, old {}, new {}'
            #             .format(a, len(arrs[a]), l))
            arrs_new[a] = arrs[a][:l]
        else:
            arrs_new[a] = arrs[a][:]

    return arrs_new


# def is_growing_quickly(xs, ys, min_d):
#     """
#     Obtain growth rate of ys with respect to the counter xs

#     # sage: get_growth_rate([1,2,3,4],[1,2,3,4])
#     # [1.00000000000000, 1.00000000000000, 1.00000000000000]
#     # sage: get_growth_rate([1,2,3,4],[1,2,3,5])
#     # [1.00000000000000, 1.00000000000000, 1.16096404744368]
#     # sage: get_growth_rate([4,1,2,3],[5,1,2,3])
#     # [1.00000000000000, 1.00000000000000, 1.16096404744368]

#     # sage: xs = range(10); get_grow_rate(xs,[x**3 for x in xs])
#     # [3.00000000000000,
#     # 3.00000000000000,
#     # 3.00000000000000,
#     # 3.00000000000000,
#     # 3.00000000000000,
#     # 3.00000000000000,
#     # 3.00000000000000,
#     # 3.00000000000000]
#     # sage: xs = range(2); get_grow_rate(xs,[x**3 for x in xs])
#     # []

#     """
#     if __debug__:
#         assert (is_list(xs) and is_list(ys) and
#                 len(xs) >= 10 and len(xs) == len(ys)), (xs,ys)
#         assert all(x>=2 for x in xs), xs # ctr values are non-neg (2+ for log)

#     zip_xs_ys = itertools.izip(xs,ys)
#     zip_xs_ys = sorted(zip_xs_ys, key = lambda (x,y): x)
#     ds = [log(y,x).n() for x,y in zip_xs_ys]

#     #if it's not increasing, then return false
#     if any(a > b for a,b in zip(ds,ds[1:])):
#         return False

#     #if not increasing quickly, return false
#     if any(d < min_d for d in ds):
#         return False

#     return True

# def elim_ss(ss, tcs, min_d):
#     """
#     ss = monomials
#     """

#     ctr_ss = [s for s in tcs[0] if 'dummy_ctr' in str(s)]
#     if is_empty(ctr_ss):
#         return ss

#     if len(ctr_ss) >= 2:
#         mlog.warn("more than 2 ctr symbols, use the 1st one '{}'"
#                     .format(ctr_ss[0]))

#     ctr_s = ctr_ss[0]

#     best_ctr_idxs = []
#     ctr_idxs = []
#     n_reset = 0
#     for i,t in enumerate(tcs):
#         if len(best_ctr_idxs) > 50:
#             break

#         cur_ctr_v = tcs[i][ctr_s]
#         assert cur_ctr_v >= 0 #ctr values are non-neg

#         if i>=1 and tcs[i-1][ctr_s] > cur_ctr_v:
#             if len(ctr_idxs) > len(best_ctr_idxs):
#                 best_ctr_idxs = ctr_idxs

#             ctr_idxs = []

#             n_reset = n_reset + 1
#             if n_reset >= 10:
#                 break

#         if cur_ctr_v >= 2: #only interested in value 2+
#             ctr_idxs.append(i)

#     if len(best_ctr_idxs) < 10:  #not enough data
#         return ss

#     tcs = [tcs[i] for i in best_ctr_idxs]
#     s_tcs = dict([(s,[s.subs(t) for t in tcs]) for s in ss + [ctr_s]])

#     xs = s_tcs[ctr_s]
#     blacklist = [s for s in ss
#                  if is_growing_quickly(xs,s_tcs[s],min_d)]

#     if not is_empty(blacklist):
#         print('Remove {} fast-growing terms {}'
#                      .format(len(blacklist),blacklist))

#     return [s for s in ss if s not in blacklist]


class Miscs(object):

    @staticmethod
    def keys_to_str(ls):
        """
        Convert key in dictionary to str, {a:5} => {'a' => 5}

        Input: list of dicts (could be some non-dict elem)
        Output: list of dicts with keys as string

        Examples:

        ### sage: Miscs.keys_to_str([{var('a'):5},{var('b'):7},5])
        [OrderedDict([('a', 5)]), OrderedDict([('b', 7)]), 5]

        """
        return [(OrderedDict([(str(k), c) for k, c in l.iteritems()]))
                if isinstance(l, dict) else l
                for l in ls]

    @staticmethod
    def get_sols(sols, sol_format):
        """
        Construct a list of properties from the inputs sols and sol_format


        Examples:

        #when sols are in dict form
        ### sage: var('uk_0,uk_1,uk_2,uk_3,uk_4,r14,r15,a,b,y')
        (uk_0, uk_1, uk_2, uk_3, uk_4, r14, r15, a, b, y)

        ### sage: Miscs.get_sols([{uk_0: -2*r14 + 7/3*r15, uk_1: -1/3*r15, \
        uk_4: r14, uk_2: r15, uk_3: -2*r14}],\
        uk_1*a + uk_2*b + uk_3*x + uk_4*y + uk_0 == 0)
        [-2*x + y - 2 == 0, -1/3*a + b + 7/3 == 0]

        #when sols are not in dict form
        ### sage: Miscs.get_sols([[uk_0== -2*r14 + 7/3*r15, \
        uk_1== -1/3*r15, uk_4== r14, uk_2== r15, uk_3== -2*r14]],\
        uk_1*a + uk_2*b + uk_3*x + uk_4*y + uk_0 == 0)
        [-2*x + y - 2 == 0, -1/3*a + b + 7/3 == 0]

        ### sage: Miscs.get_sols([],uk_1*a + uk_2*b + uk_3*x + uk_4*y + uk_0 == 0)
        []
        """
        assert is_sage_expr(sol_format), sol_format

        if sols is None or is_empty(sols):
            return []

        if len(sols) > 1:
            logger.warn('get_sols: len(sols) = {}'.format(len(sols)))
            logger.warn(sols)

        def f_eq(d):
            if isinstance(d, list):
                f_ = sol_format
                for d_ in d:
                    f_ = f_.subs(d_)
                rhsVals = vset([d_.rhs() for d_ in d])
                uk_vars = get_vars(rhsVals)
            else:
                f_ = sol_format(d)
                uk_vars = get_vars(d.values())  # e.g., r15,r16 ...

            if is_empty(uk_vars):
                return f_

            iM = identity_matrix(len(uk_vars))  # standard basis
            rs = [dict(zip(uk_vars, l)) for l in iM.rows()]
            rs = [f_(r) for r in rs]
            return rs

        sols = CM.vflatten([f_eq(s) for s in sols])

        # remove trivial (tautology) str(x) <=> str(x)
        sols = [s for s in sols
                if not (s.is_relational() and str(s.lhs()) == str(s.rhs()))]

        return sols

    #############################

    @staticmethod
    def _f(ls, op, is_real):
        """

        """
        if any(l is None for l in ls) or not ls:
            return None

        import z3
        from smt_z3py import SMT_Z3

        rs = [SMT_Z3.to_z3exp(l, is_real=is_real) if is_sage_expr(l) else l
              for l in ls]

        if len(rs) == 1:
            rs = rs[0]
        else:
            rs = z3.And(rs) if op == 'and' else z3.Or(rs)

        return rs

    @staticmethod
    def travel(A):
        """
        Examples:

        ### sage: Miscs.travel([1,[0,[5]],8,[8]])
        [([0], 1), ([1, 0], 0), ([1, 1, 0], 5), ([2], 8), ([3, 0], 8)]
        """
        assert isinstance(A, list) and A, A

        def _travel(A, idx, rs):
            for i, c in enumerate(A):
                myi = idx+[i]
                if isinstance(c, list):
                    rs = _travel(c, myi, rs)
                else:
                    rs = rs + [(myi, c)]
            return rs

        return _travel(A, [], [])

    @staticmethod
    def get_idxs(A):
        """
        Return the (nested) order of A in dict format where dkey is value v
        of A and the dvalue is the list of indices I of A containing v

        Examples:

        ### sage: assert Miscs.get_idxs([1,[0,[5]],8,[8]]) == \
        OrderedDict([(1, [(0,)]), (0, [(1, 0)]), (5, [(1, 1, 0)]), (8, [(2,), (3, 0)])])
        ### sage: assert Miscs.get_idxs([]) == OrderedDict()
        """

        vals_idxs = [(v, tuple(idx)) for idx, v in Miscs.travel(A)]
        rs = CM.create_dict(vals_idxs)
        return rs

    @staticmethod
    def reach(vss, rdata):
        """
        Checks if values in vss can be found from rdata and performs
        branching if necessary in the case of multiple occurences.

        The output is a list of size == dim of rdata.

        Examples:

        ### sage: Miscs.reach([(8,), (15,), (7,)], \
        rdata = {8:[(10,), (4,)], 15:[(8,), (3,)], 7:[(2,)]})
        [[(10, 4), (8, 3), (2,)]]

        #10 is found at either (3,) or (8,), written as (3,8)
        #The output is a list of size 1 since the dim of rdata is 1
        ### sage: Miscs.reach([(10,)], rdata = {10:[(3,), (8,)]})
        [[(3, 8)]]

        #10 is found at either (3,7) or (8,2), written as [(3,8)],[(7,2)]
        ### sage: Miscs.reach([(10,)], rdata = {10:[(3,7),(8,2)]})
        [[(3, 8)], [(7, 2)]]

        #10 or 4 is found at either (3,7),(8,2) or (0,4), written as [(3,8,0)],[(7,2,4)]
        ### sage: Miscs.reach([(10,4)], \
        rdata = {4:[(0,4)], 10:[(3,7),(8,2)]})
        [[(3, 8, 0)], [(7, 2, 4)]]

        #10 or 4 is found at either (3,7),(8,2) or (0,4), written as [(3,8,0)],[(7,2,4)]
        #8 or 3 is found at either (2,6) or (1,2), written as [(2,1)],[(6,2)]
        #2 is found at either (2,0) or (1,7),  written as [(2,1)],[(0,7)]
        #all together, written as [[(3,8,0),(2,1),(2,1)], [(7,2,4),(6,2),(0,7)]]
        #The output is 2 lists. Each list has 3 (# of inputs) tuples.

        ### sage: Miscs.reach([(10,4),(8,3),(2,)], \
        rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})
        [[(3, 8, 0), (2, 1), (2, 1)], [(7, 2, 4), (6, 2), (0, 7)]]

        ### sage: Miscs.reach([(10,4),(8,3),(8,3)], \
        rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})
        [[(3, 8, 0), (2, 1), (2, 1)], [(7, 2, 4), (6, 2), (6, 2)]]

        ### sage: Miscs.reach([(10,5),(8,3),(2,)], \
        rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})
        [[(3, 8), (2, 1), (2, 1)], [(7, 2), (6, 2), (0, 7)]]

        ### sage: Miscs.reach([(10,4),(8,13),(2,)], \
        rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})
        [[(3, 8, 0), (2,), (2, 1)], [(7, 2, 4), (6,), (0, 7)]]

        ### sage: Miscs.reach([(100,14),(8,13),(2,)], \
        rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})
        []

        ### sage: Miscs.reach([(100,4),(8,13),(2,)], \
        rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})
        [[(0,), (2,), (2, 1)], [(4,), (6,), (0, 7)]]

        ### sage: Miscs.reach([(100,4),(8,13),(100,)], \
        rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})
        []

        """
        assert isinstance(vss, list) and all(
            isinstance(vs, tuple) for vs in vss), vss

        def _getIdxs(vs): return [rdata[v] for v in vs if v in rdata]
        rs = [_getIdxs(vs) for vs in vss]

        if any(not r_ for r_ in rs):
            return []
        else:
            rs = [CM.vflatten(r_, list) for r_ in rs]
            rs = [zip(*r_) for r_ in rs]
            rs = zip(*rs)
            rs = [list(r_) for r_ in rs]
            assert len(rs) == len(rdata[list(rdata.keys())[0]][0])
            return rs


class CM:
    @staticmethod
    def create_dict(l):
        """
        given a list of set of type [(k1,v1),..,(kn,vn)]
        generates a dict where keys are k's and values are [v's]
        e.g.,

        >>> ###d = create_dict([('a',1),['b',2],('a',3),('c',4),('b',10)]); 
        OrderedDict([('a', [1, 3]), ('b', [2, 10]), ('c', [4])])
        >>> ###d['x']
        Traceback (most recent call last):
        ...
        KeyError: 'x'
        """
        return functools.reduce(lambda d, kv: d.setdefault(kv[0], []).append(kv[1]) or d, l, {})

    @staticmethod
    def merge_dict(l):
        return functools.reduce(lambda x, y: OrderedDict(list(x.items()) + list(y.items())), l, {})

    @staticmethod
    def vsetdiff(seq1, seq2):
        """
        Set diff operation that preserves order, return seq1 - seq2

        EXAMPLES:

        ### sage: var('y')
        y
        ### sage: vsetdiff([x^2>=1,x-y==3,x+y==9,x-y==3],[2])
        [x^2 >= 1, x - y == 3, x + y == 9, x - y == 3]
        ### sage: vsetdiff([x^2>=1,x-y==3,x+y==9,x-y==3],[x-y==3])
        [x^2 >= 1, x + y == 9]
        ### sage: vsetdiff([x^2>=1],[x-y==3])
        [x^2 >= 1]
        ### sage: vsetdiff([],[x-y==3])
        []
        ### sage: vsetdiff([1,2,3],[2])
        [1, 3]

        """
        assert isinstance(seq1, list)
        assert isinstance(seq2, list)

        seq2 = set(seq2)  # since  membership testing in set is quick

        return [s for s in seq1 if s not in seq2]

    def vflatten(l, ltypes=(list, tuple)):
        ltype = type(l)
        l = list(l)
        i = 0
        while i < len(l):
            while isinstance(l[i], ltypes):
                if not l[i]:
                    l.pop(i)
                    i -= 1
                    break
                else:
                    l[i:i + 1] = l[i]
            i += 1
        return ltype(l)


# print('TEST 0')
# t = Tree('a', [None, None])
# print(t)
# nodes = [Tree('b', [None, None])]
# print(list(map(str, t.gen_root_trees(nodes, vss=None, blacklist={}, data={}))))


# print('TEST 1')
# t = Tree({'root':'B','children':[None]})

# nodes = [ \
#           Tree({'root':'C','children':[None,None]}), \
#           Tree({'root':'D','children':[None]})]

# vss=[(8,),(15,),(7,)]
# data = {'C':{8: [(2, 6)], 10: [(3, 7), (8, 2)], 3: [(1, 2)], 4: [(0, 4)], 2: [(2, 0), (1, 7)]},\
#         'D':{8: [(7,)], 1: [(9,)], 2: [(8,)], 3: [(5,)]}, 'B':{8: [(10,), (4,)], 7: [(2,)], 15: [(8,), (3,)]}}

# print(list(map(str,t.gen_root_trees(nodes,vss=vss, blacklist={}, data=data))))

# rs = Miscs.reach([(100, 4), (8, 13), (2,)],
#                  rdata={4: [(0, 4)], 8: [(2, 6)], 10: [(3, 7), (8, 2)], 3: [(1, 2)], 2: [(2, 0), (1, 7)]})
# print(rs)
# #[[(0,), (2,), (2, 1)], [(4,), (6,), (0, 7)]]

# DBG()

# print('TEST 3')
# C = Tree({'root': 'C', 'children': [None]})
# B = Tree({'root': 'B', 'children': [None, None, None]})
# vss = [(7,), (1,), (-3,)]
# data = OrderedDict([('A', OrderedDict([(7, [(0,)]), (1, [(1,)]), (-3, [(2,)])])), ('C', OrderedDict([(8, [(0,)]), (5, [(1,)]), (6, [(2,), (3,)]),
#                    (2, [(4,)]), (1, [(5,)]), (4, [(6,)])])), ('B', OrderedDict([(1, [(0,), (3,), (6,)]), (-3, [(1,)]), (5, [(2,)]), (0, [(4,)]), (7, [(5,)])]))])

# print(list(map(str, B.gen_root_trees([C], vss, {}, data))))

# print('TEST 3A')
# C = Tree({'root': 'C', 'children': [None]})
# B = Tree({'root': 'B', 'children': [None, None]})
# vss = [(7,), (1,)]
# data = OrderedDict([('A', OrderedDict([(7, [(0,)]), (1, [(1,)]), (-3, [(2,)])])), ('C', OrderedDict([(8, [(0,)]), (5, [(1,)]), (6, [(2,), (3,)]),
#                    (2, [(4,)]), (1, [(5,)]), (4, [(6,)])])), ('B', OrderedDict([(1, [(0,), (3,), (6,)]), (-3, [(1,)]), (5, [(2,)]), (0, [(4,)]), (7, [(5,)])]))])

# print(list(map(str, B.gen_root_trees([C], vss, {}, data))))


print('TEST 2')
tcs = [{'A': [7, 1, -3], 'C': [8, 5, 6, 6, 2, 1, 4], 'B': [1, -3, 5, 1, 0, 7, 1]}]
xinfo = {'All': ['A', 'B', 'C'], 'Assume': [], 'Const': [], 'Expect': [
    'A[i]=B[C[2i+1]]'], 'ExtFun': [], 'ExtVar': [], 'Global': [], 'Input': [], 'Output': []}
na = NestedArray(tcs=tcs, xinfo=xinfo)
na.solve()


# print('TEST 4')
# C = Tree('C', [None])
# print(C)

# vss = [(5,), (0, 3, 6), (1,)]
# data = OrderedDict([('A', OrderedDict([(7, [(0,)]), (1, [(1,)]), (-3, [(2,)])])), ('C', OrderedDict([(8, [(0,)]), (5, [(1,)]), (6, [(2,), (3,)]),
#                    (2, [(4,)]), (1, [(5,)]), (4, [(6,)])])), ('B', OrderedDict([(1, [(0,), (3,), (6,)]), (-3, [(1,)]), (5, [(2,)]), (0, [(4,)]), (7, [(5,)])]))])

# print(list(map(str, C.gen_root_trees([], vss, {}, data))))

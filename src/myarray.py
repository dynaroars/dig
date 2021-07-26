import settings
from abc import ABCMeta, abstractmethod
import operator

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
from collections import OrderedDict, namedtuple, defaultdict

import sage.all
from sage.all import QQ, ZZ

import helpers.vcommon as CM

from helpers.miscs import Miscs as HM
from helpers.miscs import MP
from helpers.z3utils import Z3
import z3

DBG = pdb.set_trace

mlog = CM.getLogger(__name__, settings.logger_level)

special_str = "_special"


def myprod(l): return functools.reduce(operator.mul, l, 1)


class Inv:
    __metaclass__ = ABCMeta

    def __init__(self, p, p_str=None):
        assert p_str is None or isinstance(p_str, str), p_str

        self.p = p
        if p_str is None:
            p_str = str(p)

        self.p_str = Inv.rm_lambda(p_str)

    def __eq__(self, other): return self.p.__eq__(other.p)
    def __ne__(self, other): return self.p.__ne__(other.p)
    def __hash__(self): return self.p.__hash__()
    def __str__(self): return self.p_str
    def __repr__(self): return self.p.__repr__()

    @staticmethod
    def rm_lambda(s):
        return s[s.find(':') + 1:].strip()  # no lambda

    @abstractmethod
    def get_score(): return

    @abstractmethod
    def seval(self): return

    @staticmethod
    def print_invs(ps, nice_format=True):
        """
        # sage: var('y')
        y

        # sage: Inv.print_invs(map(InvEqt, [3*x==2,x*x==1]))
        0: 3*x == 2
        1: x^2 == 1

        # sage: Inv.print_invs(map(InvExp,[3*x==2,x>=2, x*x+y == 2*y*y,('lambda expr: max(x,y) >= 0', 'If(x>=y,x>=0,y>=0)')]),nice_format=False)
        # [3*x == 2, x^2 + y == 2*y^2, x >= 2, If(x>=y,x>=0,y>=0)]

        """
        assert (isinstance(ps, list) and
                all(isinstance(p, Inv) for p in ps)), map(type, ps)

        if ps:
            # sort by alphabetical string first
            ps = sorted(ps, key=lambda p: p.p_str)
            ps = sorted(ps, key=lambda p: p.get_score())  # then sort by score

            ps_poly_eqt = []
            ps_other = []

            for p in ps:
                if '==' in str(p):
                    ps_poly_eqt.append(p)
                else:
                    ps_other.append(p)

            ps = ps_poly_eqt + ps_other

            if nice_format:
                def str_(p): return p.p_str

                rs = '\n'.join('{:>5}: {}'
                               .format(i, str_(p)) for i, p in enumerate(ps))
            else:
                rs = '[{}]'.format(', '.join(map(str, ps)))

            print(rs)


class InvArray(Inv):
    __metaclass__ = ABCMeta

    def __init__(self, p):
        """
        Ex:
        flat arr: 'lambda A, B, A0: (A[A0]) + (-7*B[2*A0]) + (-3*A0) == 0
        nested arr: 'lambda A,B,i1: A[i1] == B[-2*i1 + 5]'
        """
        assert (isinstance(p, str) and
                all(s in p for s in ['lambda', '[', ']'])), p

        super(InvArray, self).__init__(p)

    def get_score(self):
        return len(self.p_str)

    def seval(self, tc):
        return InvArray.eval_lambda(self.p, idx_info=self.idx_info, tc=tc)

    @staticmethod
    def eval_lambda(f, idx_info, tc):
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

        assert isinstance(f, str) and 'lambda' in f, f
        assert (idx_info is None or
                isinstance(idx_info, list) and
                all(isinstance(v, dict) for v in idx_info)), indx_info
        assert isinstance(tc, dict), tc
        assert all(isinstance(k, str) for k in tc), tc.keys()

        f = sage.all.sage_eval(f)
        vs = f.__code__.co_varnames

        arrs = [v for v in vs if v in tc]  # A,B
        extfuns = [v for v in vs if v in ExtFun.efdict]
        idxStr = [v for v in vs if v not in arrs+extfuns]  # i,j,k

        d_tc = {v: tc[v] for v in arrs}
        d_extfun = {v: ExtFun(v).fun for v in extfuns}
        d_ = HM.merge_dict([d_tc, d_extfun])

        if idx_info is None:  # obtain idxsVals from the pivot array
            pivotContents = tc[arrs[0]]
            idxVals = [idx for idx, _ in Miscs.travel(pivotContents)]
            idx_info = [dict(zip(idxStr, idxV)) for idxV in idxVals]

        ds = [HM.merge_dict([d_, idx_info_]) for idx_info_ in idx_info]

        try:
            return all(f(**d) for d in ds)
        except IndexError:
            return False
        except TypeError:
            return False
        except NameError as msg:
            logger.warn(msg)
            return False


class InvNestedArray(InvArray):
    def __init__(self, p):
        """
        Ex:
        'lambda a,b,c,i,j: a[i][j]==2*b[i]+c[j]'
        """
        assert isinstance(p, str) and all(
            s in p for s in ['lambda', '[', ']']), p
        super(InvNestedArray, self).__init__(p.strip())
        self.idx_info = None  # no info about idx (only for FlatArr)


class NestedArray:
    """
    Find NestedArray Invariant of the form  A[i] = B[e] where e = e1 | C[e]

    Examples:

    # sage: logger.set_level(VLog.DEBUG)


    # paper_nested

    # sage: var('A B C')
    (A, B, C)

    # sage: tcs = [OrderedDict(
        [(A, [7, 1, -3]), (C, [8, 5, 6, 6, 2, 1, 4]), (B, [1, -3, 5, 1, 0, 7, 1])])]
    # sage: xinfo = {'All': ['A', 'B', 'C'], 'Assume': [], 'Const': [], 'Expect': [
        'A[i]=B[C[2i+1]]'], 'ExtFun': [], 'ExtVar': [], 'Global': [], 'Input': [], 'Output': []}
    # sage: na = NestedArray(terms=[],tcs=tcs,xinfo=xinfo)
    dig:Info:*** NestedArray ***
    # sage: na.go()
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
    # sage: var('a b r Alogtable Logtable')
    (a, b, r, Alogtable, Logtable)

    # sage: xinfo = {'All': ['Alogtable', 'Logtable', 'a', 'b', 'r'], 'Assume': [], 'Const': [], 'Expect': [
        'r[i] = Alogtable(mod255(add(Logtable(a[i]),Logtable(b[i]))))'], 'ExtFun': ['add', 'mod255'], 'ExtVar': [], 'Global': [], 'Input': ['a', 'b'], 'Output': []}

    # sage: tcs1 = [OrderedDict([(r, [118]), (a, [29]), (b, [132]), (Alogtable, [1, 3, 5, 15, 17, 51, 85, 255, 26, 46, 114, 150, 161, 248, 19, 53, 95, 225, 56, 72, 216, 115, 149, 164, 247, 2, 6, 10, 30, 34, 102, 170, 229, 52, 92, 228, 55, 89, 235, 38, 106, 190, 217, 112, 144, 171, 230, 49, 83, 245, 4, 12, 20, 60, 68, 204, 79, 209, 104, 184, 211, 110, 178, 205, 76, 212, 103, 169, 224, 59, 77, 215, 98, 166, 241, 8, 24, 40, 120, 136, 131, 158, 185, 208, 107, 189, 220, 127, 129, 152, 179, 206, 73, 219, 118, 154, 181, 196, 87, 249, 16, 48, 80, 240, 11, 29, 39, 105, 187, 214, 97, 163, 254, 25, 43, 125, 135, 146, 173, 236, 47, 113, 147, 174, 233, 32, 96, 160, 251, 22, 58, 78, 210, 109, 183, 194, 93, 231, 50, 86, 250, 21, 63, 65, 195, 94, 226, 61, 71, 201, 64, 192, 91, 237, 44, 116, 156, 191, 218, 117, 159, 186, 213, 100, 172, 239, 42, 126, 130, 157, 188, 223, 122, 142, 137, 128, 155, 182, 193, 88, 232, 35, 101, 175, 234, 37, 111, 177, 200, 67, 197, 84, 252, 31, 33, 99, 165, 244, 7, 9, 27, 45, 119, 153, 176, 203, 70, 202, 69, 207, 74, 222, 121, 139, 134, 145, 168, 227, 62, 66, 198, 81, 243, 14, 18, 54, 90, 238, 41, 123, 141, 140, 143, 138, 133, 148, 167, 242, 13, 23, 57, 75, 221, 124, 132, 151, 162, 253, 28, 36,
                              108, 180, 199, 82, 246, 1]), (Logtable, [0, 0, 25, 1, 50, 2, 26, 198, 75, 199, 27, 104, 51, 238, 223, 3, 100, 4, 224, 14, 52, 141, 129, 239, 76, 113, 8, 200, 248, 105, 28, 193, 125, 194, 29, 181, 249, 185, 39, 106, 77, 228, 166, 114, 154, 201, 9, 120, 101, 47, 138, 5, 33, 15, 225, 36, 18, 240, 130, 69, 53, 147, 218, 142, 150, 143, 219, 189, 54, 208, 206, 148, 19, 92, 210, 241, 64, 70, 131, 56, 102, 221, 253, 48, 191, 6, 139, 98, 179, 37, 226, 152, 34, 136, 145, 16, 126, 110, 72, 195, 163, 182, 30, 66, 58, 107, 40, 84, 250, 133, 61, 186, 43, 121, 10, 21, 155, 159, 94, 202, 78, 212, 172, 229, 243, 115, 167, 87, 175, 88, 168, 80, 244, 234, 214, 116, 79, 174, 233, 213, 231, 230, 173, 232, 44, 215, 117, 122, 235, 22, 11, 245, 89, 203, 95, 176, 156, 169, 81, 160, 127, 12, 246, 111, 23, 196, 73, 236, 216, 67, 31, 45, 164, 118, 123, 183, 204, 187, 62, 90, 251, 96, 177, 134, 59, 82, 161, 108, 170, 85, 41, 157, 151, 178, 135, 144, 97, 190, 220, 252, 188, 149, 207, 205, 55, 63, 91, 209, 83, 57, 132, 60, 65, 162, 109, 71, 20, 42, 158, 93, 86, 242, 211, 171, 68, 17, 146, 217, 35, 32, 46, 137, 180, 124, 184, 38, 119, 153, 227, 165, 103, 74, 237, 222, 197, 49, 254, 24, 13, 99, 140, 128, 192, 247, 112, 7])])]


    # sage: na = NestedArray(terms=[],tcs=tcs1,xinfo=xinfo)
    dig:Info:*** NestedArray ***
    # sage: na.go()
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

    # sage: tcs2 = [OrderedDict([(r, [209]), (a, [12]), (b, [85]), (Alogtable, [1, 3, 5, 15, 17, 51, 85, 255, 26, 46, 114, 150, 161, 248, 19, 53, 95, 225, 56, 72, 216, 115, 149, 164, 247, 2, 6, 10, 30, 34, 102, 170, 229, 52, 92, 228, 55, 89, 235, 38, 106, 190, 217, 112, 144, 171, 230, 49, 83, 245, 4, 12, 20, 60, 68, 204, 79, 209, 104, 184, 211, 110, 178, 205, 76, 212, 103, 169, 224, 59, 77, 215, 98, 166, 241, 8, 24, 40, 120, 136, 131, 158, 185, 208, 107, 189, 220, 127, 129, 152, 179, 206, 73, 219, 118, 154, 181, 196, 87, 249, 16, 48, 80, 240, 11, 29, 39, 105, 187, 214, 97, 163, 254, 25, 43, 125, 135, 146, 173, 236, 47, 113, 147, 174, 233, 32, 96, 160, 251, 22, 58, 78, 210, 109, 183, 194, 93, 231, 50, 86, 250, 21, 63, 65, 195, 94, 226, 61, 71, 201, 64, 192, 91, 237, 44, 116, 156, 191, 218, 117, 159, 186, 213, 100, 172, 239, 42, 126, 130, 157, 188, 223, 122, 142, 137, 128, 155, 182, 193, 88, 232, 35, 101, 175, 234, 37, 111, 177, 200, 67, 197, 84, 252, 31, 33, 99, 165, 244, 7, 9, 27, 45, 119, 153, 176, 203, 70, 202, 69, 207, 74, 222, 121, 139, 134, 145, 168, 227, 62, 66, 198, 81, 243, 14, 18, 54, 90, 238, 41, 123, 141, 140, 143, 138, 133, 148, 167, 242, 13, 23, 57, 75, 221, 124, 132, 151, 162, 253, 28, 36,
                              108, 180, 199, 82, 246, 1]), (Logtable, [0, 0, 25, 1, 50, 2, 26, 198, 75, 199, 27, 104, 51, 238, 223, 3, 100, 4, 224, 14, 52, 141, 129, 239, 76, 113, 8, 200, 248, 105, 28, 193, 125, 194, 29, 181, 249, 185, 39, 106, 77, 228, 166, 114, 154, 201, 9, 120, 101, 47, 138, 5, 33, 15, 225, 36, 18, 240, 130, 69, 53, 147, 218, 142, 150, 143, 219, 189, 54, 208, 206, 148, 19, 92, 210, 241, 64, 70, 131, 56, 102, 221, 253, 48, 191, 6, 139, 98, 179, 37, 226, 152, 34, 136, 145, 16, 126, 110, 72, 195, 163, 182, 30, 66, 58, 107, 40, 84, 250, 133, 61, 186, 43, 121, 10, 21, 155, 159, 94, 202, 78, 212, 172, 229, 243, 115, 167, 87, 175, 88, 168, 80, 244, 234, 214, 116, 79, 174, 233, 213, 231, 230, 173, 232, 44, 215, 117, 122, 235, 22, 11, 245, 89, 203, 95, 176, 156, 169, 81, 160, 127, 12, 246, 111, 23, 196, 73, 236, 216, 67, 31, 45, 164, 118, 123, 183, 204, 187, 62, 90, 251, 96, 177, 134, 59, 82, 161, 108, 170, 85, 41, 157, 151, 178, 135, 144, 97, 190, 220, 252, 188, 149, 207, 205, 55, 63, 91, 209, 83, 57, 132, 60, 65, 162, 109, 71, 20, 42, 158, 93, 86, 242, 211, 171, 68, 17, 146, 217, 35, 32, 46, 137, 180, 124, 184, 38, 119, 153, 227, 165, 103, 74, 237, 222, 197, 49, 254, 24, 13, 99, 140, 128, 192, 247, 112, 7])])]
    # sage: na = NestedArray(terms=[],tcs=tcs2,xinfo=xinfo)
    dig:Info:*** NestedArray ***
    # sage: na.go()
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

    def mk_traces(self):
        # will be modified in preprocess
        tcs_all = Miscs.keys_to_str(self.tcs)
        tcs, _ = get_traces(tcs_all,
                            ntcs=1,  # using only 1 array
                            ntcs_extra=0)

        tcs_extra = tcs_all  # refine on all tcs
        return tcs, tcs_extra

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
            d = HM.merge_dict(efs + [arrs])
            mytcs.append(d)

        self.tcs = mytcs
        self.trees = [Tree(k, [None] * len(list(c.items())[0][1]), ExtFun(k).commute)
                      for k, c in self.tcs[0].items()]

    def solve(self):  # nested arrays

        self.tcs, self.tcs_extra = self.mk_traces()

        mlog.debug('Preprocessing arrays')

        # add ext funs, generate nodes, modify tcs
        self.preprocess()

        mlog.debug("Generate arr exps (nestings)")
        aexps = AEXP.gen_aexps(self.trees, self.xinfo, self.tcs[0])

        def f(tasks):
            rs = [a.peelme(self.tcs[0]) for a in tasks]
            return rs

        wrs = MP.run_mp("Apply reachability", aexps, f, settings.DO_MP)
        sols = list(itertools.chain(*wrs))

        mlog.debug(f"Potential rels: {len(sols)}")
        self.sols = [InvNestedArray(s) for s in sols]
        Inv.print_invs(self.sols)

    def refine(self):
        # No inferrence for array invs
        # Don't do ranking either since array equations is very long
        rf = Refine(ps=self.sols)
        rf.rfilter(tcs=self.tcs_extra)
        self.sols = rf.ps


class Refine:

    def __init__(self, ps):
        assert isinstance(ps, list) and all(isinstance(p, Inv) for p in ps), ps
        self.ps = ps

    def rfilter(self, tcs, do_parallel=True):

        if not self.ps or not tcs:
            print('rfilter skips (|ps|={}, |tcs|={})'
                  .format(len(self.ps), len(tcs)))
            return

        print('rfilter(|ps|={}, |tcs|={})'
              .format(len(self.ps), len(tcs)))

        tcs = Miscs.keys_to_str(tcs)
        # ps_ = [p for p in self.ps if all(p.seval(tc) for tc in tcs)]

        def f(tasks):
            rs = [p for p in tasks if all(p.seval(tc) for tc in tcs)]
            return rs
        wrs = MP.run_mp("rfilter ", self.ps, f, settings.DO_MP)

        self.ps = wrs
        # Refine.print_diff('rfilter', len(tasks), len(self.ps))

# tracefile = Path("../tests/traces/paper_nested.csv")
# ss = {}
# traces = []
# with open(tracefile) as csvfile:
#     myreader = csv.reader(csvfile, delimiter=';')
#     for row in myreader:
#         row = [field.strip() for field in row]

#         if not row or row[0].startswith("#"):
#             continue
#         loc, contents = row[0], row[1:]
#         if loc not in ss:
#             ss[loc] = contents
#         else:
#             contents = list(map(eval, contents))
#             traces.append(contents)


class Tree(namedtuple("Tree", ("root", "children", "commute"))):
    """
    leaf: Tree(None,None,False), Tree(x+7,None,False)
    tree: Tree('a',[Tree],False/True)

    >>> assert set([Tree(), Tree()]) == {Tree(root=None, children=[], commute=False)}

    """

    def __new__(cls, root=None, children=[], commute=False):
        assert(root is None or
               isinstance(root, str) or
               (HM.is_expr(root))
               ), root
        assert isinstance(children, Iterable), children
        assert isinstance(commute, bool), commute

        if (root is None or HM.is_expr(root) or
                (isinstance(root, str) and special_str in root)):  # leaf
            assert not children, children
            assert not commute, commute
        else:
            assert isinstance(children, Iterable) and children, children
            assert all(isinstance(c, Tree) or
                       c is None or
                       (HM.is_expr(c) and not c.is_symbol())
                       for c in children), children
            assert isinstance(commute, bool), commute

            children_ = []
            for c in children:
                if isinstance(c, Tree):
                    children_.append(c)
                elif c is None:
                    children_.append(Tree())  # leaf
                else:
                    assert HM.is_expr(c), c
                    children_.append(Tree(c))
            children = children_
            commute = False if len(children) <= 1 else commute

        return super().__new__(cls, root, tuple(children), commute)

    @property
    def is_leaf(self):
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
                if HM.is_expr(self.root):  # x + 7
                    ret = self.root(leaf_content)  # y+12
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
            if self.root in ExtFun.efdict:
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
            children_vss = Miscs.reach(vss, data[self.root])
            if not children_vss:
                # print('no children_vss')
                return []
        else:
            children_vss = [None] * len(self.children)
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
            rs = [Tree(self.root, [Tree()] * len(self.children), self.commute)]

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
        if HM.is_expr(self.root):
            return self.root == v

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
                return sage.all.var(mycoef) == v
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
        l_idxs = [i+1 for i in range(len(self.lt.children))]
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
            ts = [1] + [sage.all.var(f'i{i+1}')
                        for i in range(len(self.lt.children))]
        else:
            ts = [1] + list(idxs_vals)

        def rpl(t, tid):
            if t.is_leaf:
                prefix = f"_{'_'.join(map(str, tid))}__i"
                if special:
                    c = f"{prefix}{special_str}"
                else:
                    c = HM.mk_template(
                        ts, rv=None, prefix=prefix)[0]
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

        rs = [template.__str__(leaf_content=d, do_lambda=True)
              for d in ds]

        assert all(isinstance(x, str) for x in rs)
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
        __main__:DEBUG:* generate 2 aexps over A,C,B
        0. A[i1] == B[C[(i1)_]]
        1. A[i1] == B[(i1)_]

        >>> aexps = AEXP.gen_aexps(nodes, XInfo(myall=['A', 'B', 'C']), data={})
        __main__:DEBUG:* generate 12 aexps over A,C,B
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
        __main__:DEBUG:* generate 4 aexps over A,C,B
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
                lt = Tree(node.root, [None] * len(node.children), node.commute)
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

        mlog.debug(
            f"* generate {len(aexps)} aexps over {','.join(map(lambda x: str(x.root), nodes))}")
        print('\n'.join(f'{i}. {a}' for i, a in enumerate(aexps)))
        return aexps


class XInfo(namedtuple("XInfo", ("assumes", "consts", "expects", "extfuns", "extvar", "inputs", "outputs", "myall", "myglobals"))):

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

        # sage: AEXP.gen_blacklist({'All':['R','A','B','D','E','xor','g'], \
        'Input':['A','B'],'Output':['R'],'Global':[],'Const':[], \
        'ExtFun':['xor'],'Global':['g']})
        OrderedDict([('A', ['R', 'A', 'B', 'D', 'E', 'xor', 'g']),
                     ('B', ['R', 'A', 'B', 'D', 'E', 'xor', 'g']),
                     ('xor', [None]), ('g', [None]),
                     ('R', ['R', 'A', 'B', 'D', 'E', 'xor', 'g', None])])

        """

        allVars = self.myall
        inputVars = self.inputs
        outputVars = self.outputs
        globalVars = self.myglobals
        constVars = self.consts
        extFuns = [x for x in self.extfuns]

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
        rs = HM.merge_dict(ds)

        return rs


class ExtFun(str):

    efdict = {
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

    @ property
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
        return ExtFun.efdict[self][0]

    @ property
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

    @ property
    def commute(self):
        """
        Returns true if the function is commutative

        # sage: ExtFun('sub').commute
        False
        # sage: ExtFun('add').commute
        True
        # sage: ExtFun('something').commute
        False
        """
        try:
            return ExtFun.efdict[self][1]
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

        >>> assert ExtFun('add').gen_data([1,7,9,-1],doDict=False) == set([2, 8, 10, 0, 14, 16, 6, 18, -2, 1, 7, 9, -1])


        # >>> ExtFun('add').gen_data([[1,7,9,-1]],doDict=True)
        OrderedDict([('add', OrderedDict([(2, [(1, 1)]), (8, [(1, 7), (9, -1)]), (10, [(1, 9)]), (0, [(1, -1)]),
                    (14, [(7, 7)]), (16, [(7, 9)]), (6, [(7, -1)]), (18, [(9, 9)]), (-2, [(-1, -1)])]))])

        # sage: ExtFun('sub').gen_data([[1,2],[5,6]], doDict=False)
        [0, -1, -4, -5, 1, -3, 4, 3, 5, 2, 6]
        # sage: ExtFun('sub').gen_data([[1,2,5,6]], doDict=False)
        [0, -1, -4, -5, 1, -3, 4, 3, 5, 2, 6]
        # sage: ExtFun('sub').gen_data([1,2,5,6], doDict=False)
        [0, -1, -4, -5, 1, -3, 4, 3, 5, 2, 6]

        # sage: ExtFun('sub').gen_data([[1,2],[5,6]],doDict=True)
        OrderedDict([('sub', OrderedDict([(0, [(1, 1), (2, 2), (5, 5), (6, 6)]), (-1, [(1, 2), (5, 6)]), (-4, [(1, 5), (2, 6)]),
                    (-5, [(1, 6)]), (1, [(2, 1), (6, 5)]), (-3, [(2, 5)]), (4, [(5, 1), (6, 2)]), (3, [(5, 2)]), (5, [(6, 1)])]))])

        # sage: ExtFun('add').gen_data([[1,2,3,4],[5,6],[7,8,9]], doDict=False)
        [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 1]

        # sage: ExtFun('add').gen_data([[1,2,3,4],[5,6],[7,8,9]], doDict=True)
        OrderedDict([('add', OrderedDict([(2, [(1, 1)]), (3, [(1, 2)]), (4, [(1, 3), (2, 2)]), (5, [(1, 4), (2, 3)]), (6, [(1, 5), (2, 4), (3, 3)]), (7, [(1, 6), (2, 5), (3, 4)]), (8, [(1, 7), (2, 6), (3, 5), (4, 4)]), (9, [(1, 8), (2, 7), (3, 6), (4, 5)]), (10, [
                    (1, 9), (2, 8), (3, 7), (4, 6), (5, 5)]), (11, [(2, 9), (3, 8), (4, 7), (5, 6)]), (12, [(3, 9), (4, 8), (5, 7), (6, 6)]), (13, [(4, 9), (5, 8), (6, 7)]), (14, [(5, 9), (6, 8), (7, 7)]), (15, [(6, 9), (7, 8)]), (16, [(7, 9), (8, 8)]), (17, [(8, 9)]), (18, [(9, 9)])]))])
        """

        assert isinstance(avals, Iterable) and not any(
            isinstance(v, Iterable) for v in avals), avals

        avals = set(avals)
        alists = [avals] * self.nargs
        idxs = list(itertools.product(*alists))
        fun_vals = [self.fun(*idx) for idx in idxs]

        if doDict:  # create dict
            cs = zip(fun_vals, idxs)
            cs = [(fv, tuple(idx)) for (fv, idx) in cs]

            d = HM.create_dict(cs)

            if self.commute:
                # [(1,2),(2,1),(2,2)] => [(1,2),(2,2)]
                # print(d)
                d = OrderedDict((k, list(set(v))) for k, v in d.items())

            rs = OrderedDict()
            rs[self] = d

            print('fun: {}, fvals {}, idxs {}'
                  .format(self, len(d.keys()), len(idxs)))

        else:  # returns fun_vals as well as the orig avals
            rs = set(fun_vals + list(avals))

        return rs

    @ staticmethod
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

        F_d = [fn.gen_data(f_aval, doDict=True)
               for fn, f_aval in zip(extfuns, F_avals)]

        return F_d

    def get_outvals(extfuns, avals):
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

        assert len(extfuns) >= 1
        assert all(isinstance(f, ExtFun) for f in extfuns)

        if len(extfuns) > 1:
            avals = ExtFun.get_outvals(extfuns[1:], avals)
        else:
            avals = extfuns[0].gen_data(avals, doDict=False)

        return avals

    @ classmethod
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
        assert isinstance(xinfo, dict) and 'ExtFun' in xinfo, xinfo

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

    @ staticmethod
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
        ev = ev.strip()

        assert ev.count(' ') >= 1, ev

        idx = ev.find(' ')

        vname = ev[:idx].strip()
        vname = ReadFile.strToVar(vname)

        vval = ev[idx:].strip()
        vval = ReadFile.formatter(vval)
        vval = ReadFile.strToRatOrList(vval, is_num_val=None)
        return OrderedDict([(vname, vval)])

    @ classmethod
    def gen_extvars(cls, xinfo):
        """
        Returns a list of dicts representing extvars

        [{v1: 3.14},  {v2: [1,2,3]}]

        # sage: ExtFun.gen_extvars({'ExtVar' : ['mpi 3.1415', ' t 20.5 ',  'arr [1,[2,3,4]]']})
        dig_miscs:Debug:gen_extvar: 3 ext funs found in xinfo['ExtVar']
        dig_miscs:Detail:mpi 3.1415,  t 20.5 , arr [1,[2,3,4]]
        [OrderedDict([(mpi, 6283/2000)]), OrderedDict([(t, 41/2)]),
                     OrderedDict([(arr, [1, [2, 3, 4]])])]

        # sage: ExtFun.gen_extvars({'ExtVar' : []})
        []


        """
        assert isinstance(xinfo, dict), xinfo

        try:
            extvars = xinfo.extvars
        except KeyError:
            return []

        mlog.debug(
            f"gen_extvar: {len(extvars)} ext funs from {xinfo.extvars}")
        return list(map(cls.parse_extvar, extvars))


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


class Miscs(object):

    @staticmethod
    def keys_to_str(ls):
        """
        Convert key in dictionary to str, {a:5} => {'a' => 5}

        Input: list of dicts (could be some non-dict elem)
        Output: list of dicts with keys as string

        Examples:

        >>> Miscs.keys_to_str([{var('a'):5},{var('b'):7},5])
        [{'a': 5}, {'b': 7}, 5]          

        """
        return [{str(k): l[k] for k in l} if isinstance(l, dict) else l
                for l in ls]

    @staticmethod
    def travel(A):
        """
        Examples:

        >>> Miscs.travel([1,[0,[5]],8,[8]])
        [([0], 1), ([1, 0], 0), ([1, 1, 0], 5), ([2], 8), ([3, 0], 8)]
        """
        assert isinstance(A, list), A

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

        >>> Miscs.get_idxs([1,[0,[5]],8,[8]])
        {0: [(1, 0)], 1: [(0,)], 5: [(1, 1, 0)], 8: [(2,), (3, 0)]}

        >>> assert Miscs.get_idxs([]) == OrderedDict()
        """

        rs = [(v, tuple(idx)) for idx, v in cls.travel(A)]
        return HM.create_dict(rs)

    @staticmethod
    def reach(vss, rdata):
        """
        Checks if values in vss can be found from rdata and performs
        branching if necessary in the case of multiple occurences.

        The output is a list of size == dim of rdata.

        Examples:

        >>> Miscs.reach([(8,), (15,), (7,)], rdata = {8:[(10,), (4,)], 15:[(8,), (3,)], 7:[(2,)]})
        [[(10, 4), (8, 3), (2,)]]

        10 is found at either (3,) or (8,), written as (3,8)
        The output is a list of size 1 since the dim of rdata is 1
        >>> Miscs.reach([(10,)], rdata = {10:[(3,), (8,)]})
        [[(3, 8)]]

        10 is found at either (3,7) or (8,2), written as [(3,8)],[(7,2)]
        >>> Miscs.reach([(10,)], rdata = {10:[(3,7),(8,2)]})
        [[(3, 8)], [(7, 2)]]

        10 or 4 is found at either (3,7),(8,2) or (0,4), written as [(3,8,0)],[(7,2,4)]
        >>> Miscs.reach([(10,4)], rdata = {4:[(0,4)], 10:[(3,7),(8,2)]})
        [[(3, 8, 0)], [(7, 2, 4)]]

        10 or 4 is found at either (3,7),(8,2) or (0,4), written as [(3,8,0)],[(7,2,4)]
        8 or 3 is found at either (2,6) or (1,2), written as [(2,1)],[(6,2)]
        2 is found at either (2,0) or (1,7),  written as [(2,1)],[(0,7)]
        all together, written as [[(3,8,0),(2,1),(2,1)], [(7,2,4),(6,2),(0,7)]]
        The output is 2 lists. Each list has 3 (# of inputs) tuples.

        >>> Miscs.reach([(10,4),(8,3),(2,)], rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})
        [[(3, 8, 0), (2, 1), (2, 1)], [(7, 2, 4), (6, 2), (0, 7)]]

        >>> sage: Miscs.reach([(10,4),(8,3),(8,3)], rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})
        [[(3, 8, 0), (2, 1), (2, 1)], [(7, 2, 4), (6, 2), (6, 2)]]

        >>> Miscs.reach([(10,5),(8,3),(2,)], rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})
        [[(3, 8), (2, 1), (2, 1)], [(7, 2), (6, 2), (0, 7)]]

        >>> sage: Miscs.reach([(10,4),(8,13),(2,)], rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})
        [[(3, 8, 0), (2,), (2, 1)], [(7, 2, 4), (6,), (0, 7)]]

        >>> Miscs.reach([(100,14),(8,13),(2,)], rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})
        []

        >>> Miscs.reach([(100,4),(8,13),(2,)], rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})
        [[(0,), (2,), (2, 1)], [(4,), (6,), (0, 7)]]

        >>> Miscs.reach([(100,4),(8,13),(100,)], rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})
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


class CM:
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
        rs = [(sage.all.var(str(v())), sage.all.sage_eval(str(m[v])))
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


if __name__ == "__main__":

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
    tcs = [{'A': [7, 1, -3], 'C': [8, 5, 6, 6, 2, 1, 4],
            'B': [1, -3, 5, 1, 0, 7, 1]}]
    xinfo = {'All': ['A', 'B', 'C'], 'Assume': [], 'Const': [], 'Expect': [
        'A[i]=B[C[2i+1]]'], 'ExtFun': [], 'ExtVar': [], 'Global': [], 'Input': [], 'Output': []}
    na = NestedArray(tcs=tcs, xinfo=xinfo)
    # na.solve()
    # na.refine()

    print('TEST 3')
    sage.all.var('a b r AL LT')
    (a, b, r, AL, LT)
    xinfo = {'All': ['AL', 'LT', 'a', 'b', 'r'], 'Assume': [], 'Const': [], 'Expect': [
        'r[i] = Alogtable(mod255(add(Logtable(a[i]),Logtable(b[i]))))'], 'ExtFun': ['add', 'mod255'], 'ExtVar': [], 'Global': [], 'Input': ['a', 'b'], 'Output': []}

    tcs1 = [OrderedDict([(r, [118]), (a, [29]), (b, [132]), (AL, [1, 3, 5, 15, 17, 51, 85, 255, 26, 46, 114, 150, 161, 248, 19, 53, 95, 225, 56, 72, 216, 115, 149, 164, 247, 2, 6, 10, 30, 34, 102, 170, 229, 52, 92, 228, 55, 89, 235, 38, 106, 190, 217, 112, 144, 171, 230, 49, 83, 245, 4, 12, 20, 60, 68, 204, 79, 209, 104, 184, 211, 110, 178, 205, 76, 212, 103, 169, 224, 59, 77, 215, 98, 166, 241, 8, 24, 40, 120, 136, 131, 158, 185, 208, 107, 189, 220, 127, 129, 152, 179, 206, 73, 219, 118, 154, 181, 196, 87, 249, 16, 48, 80, 240, 11, 29, 39, 105, 187, 214, 97, 163, 254, 25, 43, 125, 135, 146, 173, 236, 47, 113, 147, 174, 233, 32, 96, 160, 251, 22, 58, 78, 210, 109, 183, 194, 93, 231, 50, 86, 250, 21, 63, 65, 195, 94, 226, 61, 71, 201, 64, 192, 91, 237, 44, 116, 156, 191, 218, 117, 159, 186, 213, 100, 172, 239, 42, 126, 130, 157, 188, 223, 122, 142, 137, 128, 155, 182, 193, 88, 232, 35, 101, 175, 234, 37, 111, 177, 200, 67, 197, 84, 252, 31, 33, 99, 165, 244, 7, 9, 27, 45, 119, 153, 176, 203, 70, 202, 69, 207, 74, 222, 121, 139, 134, 145, 168, 227, 62, 66, 198, 81, 243, 14, 18, 54, 90, 238, 41, 123, 141, 140, 143, 138, 133, 148, 167, 242, 13, 23, 57, 75, 221, 124, 132, 151, 162, 253, 28, 36,
                        108, 180, 199, 82, 246, 1]), (LT, [0, 0, 25, 1, 50, 2, 26, 198, 75, 199, 27, 104, 51, 238, 223, 3, 100, 4, 224, 14, 52, 141, 129, 239, 76, 113, 8, 200, 248, 105, 28, 193, 125, 194, 29, 181, 249, 185, 39, 106, 77, 228, 166, 114, 154, 201, 9, 120, 101, 47, 138, 5, 33, 15, 225, 36, 18, 240, 130, 69, 53, 147, 218, 142, 150, 143, 219, 189, 54, 208, 206, 148, 19, 92, 210, 241, 64, 70, 131, 56, 102, 221, 253, 48, 191, 6, 139, 98, 179, 37, 226, 152, 34, 136, 145, 16, 126, 110, 72, 195, 163, 182, 30, 66, 58, 107, 40, 84, 250, 133, 61, 186, 43, 121, 10, 21, 155, 159, 94, 202, 78, 212, 172, 229, 243, 115, 167, 87, 175, 88, 168, 80, 244, 234, 214, 116, 79, 174, 233, 213, 231, 230, 173, 232, 44, 215, 117, 122, 235, 22, 11, 245, 89, 203, 95, 176, 156, 169, 81, 160, 127, 12, 246, 111, 23, 196, 73, 236, 216, 67, 31, 45, 164, 118, 123, 183, 204, 187, 62, 90, 251, 96, 177, 134, 59, 82, 161, 108, 170, 85, 41, 157, 151, 178, 135, 144, 97, 190, 220, 252, 188, 149, 207, 205, 55, 63, 91, 209, 83, 57, 132, 60, 65, 162, 109, 71, 20, 42, 158, 93, 86, 242, 211, 171, 68, 17, 146, 217, 35, 32, 46, 137, 180, 124, 184, 38, 119, 153, 227, 165, 103, 74, 237, 222, 197, 49, 254, 24, 13, 99, 140, 128, 192, 247, 112, 7])])]

    na = NestedArray(tcs=tcs1, xinfo=xinfo)
    # na.solve()
    # na.refine()

    # print('TEST 4')
    # C = Tree('C', [None])
    # print(C)

    # vss = [(5,), (0, 3, 6), (1,)]
    # data = OrderedDict([('A', OrderedDict([(7, [(0,)]), (1, [(1,)]), (-3, [(2,)])])), ('C', OrderedDict([(8, [(0,)]), (5, [(1,)]), (6, [(2,), (3,)]),
    #                    (2, [(4,)]), (1, [(5,)]), (4, [(6,)])])), ('B', OrderedDict([(1, [(0,), (3,), (6,)]), (-3, [(1,)]), (5, [(2,)]), (0, [(4,)]), (7, [(5,)])]))])

    # print(list(map(str, C.gen_root_trees([], vss, {}, data))))

    # lt = Tree('R', [None, None, None])
    # rt = Tree('add', [Tree('C', [None]), Tree('D', [None])])
    # rs = AEXP(lt, rt).gen_template()
    # print(rs.lt)
    # print(rs.rt)

    # sage.all.var('_B_0_C_0__i0 _B_0_C_0__i1')
    # # Tree('B', [Tree('C', [Tree(_B_0_C_0__i0 + 2*_B_0_C_0__i1)])]).gen_formula(
    # #     v=81, data={'C': {0: [(0,), (3,)], 1: [(4,)], 7: [(2,), (5,)], 8: [(6,)], 9: [(1,), (8,)], 17: [(7,)]},
    # #                 'B': {81: [(17,)], 74: [(6,), (8,)], 71: [(5,), (7,)]}})

    # rs = Tree('B', [Tree('C', [Tree(_B_0_C_0__i0 + 2*_B_0_C_0__i1)])]).gen_formula(
    #     v=81, data={'C': {0: [(0,), (3,)], 1: [(4,)], 7: [(2,), (5,)], 8: [(6,)], 9: [(1,), (8,)], 17: [(7,)]},
    #                 'B': {81: [(17,), (9,)], 74: [(6,), (8,)], 71: [(5,), (7,)]}})
    # print(rs)

    # sage.all.var('x y')
    # t = Tree('x3', [None, None, x+7])
    # a = AEXP(Tree('v', [None]), Tree('a', [t]))
    # print(a.__str__())
    # print(a.__str__(do_lambda=True))
    # print(a.__str__(leaf_content={x: 5}, do_lambda=True))

    # t1 = Tree('x3', [None, Tree('c', [x-y, None]), x+7])
    # a1 = AEXP(Tree('v', [None]), Tree('a', [t1]))
    # print(a1.__str__(leaf_content={x: 5, y: 7}, do_lambda=True))
    # ### sage: AEXP({'root':'v','children':[None]}, \
    # {'root':'a','children':[{'root':'x3',\
    # 'children':[None,None,x+7]}]}).__str__(leaf_content={x:5},do_lambda=True)
    # 'lambda v,a,x3,i1: v[i1] == a[x3[None][None][12]]'

    # sage.all.var('x')
    # print(Tree(7, [None, None]))
    print('TEST 5')
    na = NestedArray(tcs=[{'R': [128, 127, 126, 125], 'N':[128]}], xinfo={'All': ['R'], 'Const': [], 'Assume': [
    ], 'Global': [], 'Expect': ['R[i]=sub(N,i)'], 'ExtFun': ['sub'], 'Input': [], 'Output': ['R']})
    # na.solve()


nodes = [Tree('A', [None]), Tree('C', [None]), Tree('B', [None])]
xinfo = XInfo(myall=['A', 'B', 'C'], outputs=['C'])
aexps = AEXP.gen_aexps(nodes, xinfo, data={})

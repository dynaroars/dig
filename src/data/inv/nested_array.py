import pdb
import itertools
import functools

import sage.all

from collections import namedtuple, defaultdict, OrderedDict
from collections.abc import Iterable

import z3

import helpers.vcommon as CM
from helpers.miscs import Miscs
from helpers.z3utils import Z3
import data.inv.base
import settings


DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


class NestedArray(data.inv.base.Inv):

    def __init__(self, rel, stat=None):
        assert isinstance(rel, str) and rel, rel

        super().__init__(rel, stat)

    def __str__(self, print_stat=False):
        s = self.inv
        if print_stat:
            s = f"{s} {self.stat}"
        return s

    def eval_lambda(self, idx_info, tc):
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

        f = sage.all.sage_eval(self.inv)
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
        return self.eval_lambda(None, trace.mydict)

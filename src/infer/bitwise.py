"""
Bitwise invariants: x & mask == val for each variable.

For each integer variable, finds the set of bits that are constant across
all traces.  Bits that are 1 in every trace form the "always-set" mask;
bits that are 0 in every trace form the "always-clear" mask.  Together they
give the invariant  x & combined_mask == invariant_val.

Example: if x takes values {4, 6, 12} (binary 100, 110, 1100)
  always-set bits:   AND(4,6,12)  = 4  (0b0100)
  always-clear bits: ~OR(4,6,12)  = ~14 = ...11110001 -> low bits: bit 0
  combined mask = 4 | 1 = 5
  invariant: x & 5 == 4  (bit 2 is always set, bit 0 is always clear)
"""
import pdb
from functools import reduce
from typing import NamedTuple
from beartype import beartype

import sympy
import z3

import settings
import helpers.vcommon as CM
from helpers.miscs import Miscs
from helpers.z3utils import Z3
import infer.inv
import infer.infer
import data.prog
import data.traces


DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.LOGGER_LEVEL)

_NBITS = 16  # number of bit positions to inspect


class BitwiseSpec(NamedTuple):
    """var & mask == val"""
    var: str   # variable name (string)
    mask: int
    val: int

    def __str__(self) -> str:
        return f"{self.var} & {self.mask} == {self.val}"

    def eval(self, trace: data.traces.Trace) -> bool:
        d = {str(k): int(v) for k, v in trace.mydict.items()}
        v = d.get(self.var)
        if v is None:
            return True
        return (v & self.mask) == self.val

    @property
    def expr(self) -> z3.ExprRef:
        """
        Encode  x & mask == val  using integer modular arithmetic.
        bit k is set  iff  (x // 2^k) % 2 == 1  (for non-negative x).
        """
        z3v = Z3.parse(self.var)
        conditions = []
        for k in range(_NBITS):
            bit_in_mask = (self.mask >> k) & 1
            if not bit_in_mask:
                continue
            bit_val = (self.val >> k) & 1
            power = z3.IntVal(2 ** k)
            two = z3.IntVal(2)
            conditions.append((z3v / power) % two == z3.IntVal(bit_val))
        if not conditions:
            return Z3.zTrue
        return z3.And(conditions) if len(conditions) > 1 else conditions[0]


class Bitwise(infer.inv.Inv):
    """Invariant of the form  var & mask == val."""

    @beartype
    def __init__(self, inv, stat: infer.inv.InvStat | None = None) -> None:
        assert isinstance(inv, BitwiseSpec), inv
        super().__init__(inv, stat)

    @property
    def mystr(self) -> str:
        return str(self.inv)

    @property
    def cinvs_category(self) -> str:
        return 'bitwise'

    @beartype
    def test_single_trace(self, trace: data.traces.Trace) -> bool:
        return self.inv.eval(trace)

    @beartype
    @property
    def expr(self) -> z3.ExprRef:
        return self.inv.expr


class Infer(infer.infer._Infer):

    def gen(self) -> infer.inv.DInvs:
        raise NotImplementedError("bitwise uses gen_from_traces only")

    @classmethod
    def gen_from_traces(cls, traces: data.traces.Traces,
                        symbols: data.prog.Symbs) -> list:
        """
        For each integer variable, compute bits that are constant across all
        traces.  Emit Bitwise invariants only when the mask is non-trivial
        (at least one invariant bit) and the combined mask is non-zero.
        """
        results = []
        for symb in symbols:
            if symb.is_array or symb.is_real:
                continue
            var_name = symb.name
            sym = symb.symbolic

            try:
                vals = [int(t.mydict[sym]) for t in traces]
            except (KeyError, TypeError):
                continue

            if not vals:
                continue

            # Bits that are 1 in every value
            always_set = reduce(lambda a, b: a & b, vals)
            # Bits that are 0 in every value (never set across all traces)
            or_all = reduce(lambda a, b: a | b, vals)
            always_clear_mask = (~or_all) & ((1 << _NBITS) - 1)

            combined_mask = always_set | always_clear_mask
            if combined_mask == 0:
                continue

            inv_val = always_set  # always-set bits; always-clear bits are 0
            spec = BitwiseSpec(var=var_name, mask=combined_mask, val=inv_val)

            # Quick sanity check against traces
            if not all(spec.eval(t) for t in traces):
                continue

            results.append(Bitwise(spec))

        return results

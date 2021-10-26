import pdb
import typing

import sympy

import helpers.vcommon as CM
from helpers.miscs import Miscs
from helpers.z3utils import Z3
import settings

import data.traces
import data.inv.base

DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


if __name__ == "__main__":
    import doctest
    doctest.testmod()

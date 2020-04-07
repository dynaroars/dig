"""
Find upperbound of polynomials using binary search-CEGIR approach
"""
import math
import pdb
from time import time

import z3
import sage.all

import helpers.vcommon as CM
from helpers.miscs import Miscs
import helpers.miscs

import settings
import data.traces
import data.poly.base
import data.inv.oct
import cegir.base

DBG = pdb.set_trace

mlog = CM.getLogger(__name__, settings.logger_level)

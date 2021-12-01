from abc import ABCMeta, abstractmethod

import pdb
import operator

import helpers.vcommon as CM
import settings
from helpers.miscs import Miscs


DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.LOGGER_LEVEL)


class Poly(metaclass=ABCMeta):
    def __init__(self, poly):
        self.poly = poly

    def __hash__(self):
        return hash(self.poly)

    def __repr__(self):
        return repr(self.poly)

    def __eq__(self, other):
        return isinstance(other, self.__class__) and self.poly.__eq__(other.poly)

    @abstractmethod
    def eval_traces(self, traces, pred):
        pass

    @abstractmethod
    def mk_le(self, val):
        pass

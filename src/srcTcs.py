import os
from collections import OrderedDict
import sage.all

import vcommon as CM
from miscs import Z3

import settings
mlog = CM.getLogger(__name__, settings.logger_level)


def parse(filename):
    assert os.path.isfile(filename), filename
    contents = CM.iread_strip(filename)


def stripTo(s, to_s): return s[s.find(to_s) + 1:].strip()  # e.g., ...:x  -> x


class Src(object):

    def __init__(self, filename):
        assert os.path.isfile(filename), filename
        self.filename = filename  # /path/to/f.ext

    @property
    def contentsd(self):
        try:
            return self._contentsd
        except AttributeError:
            d = [(i, l.strip()) for i, l in enumerate(CM.iread(self.filename))]
            self._contentsd = OrderedDict((i+1, l) for i, l in d if l)
            return self._contentsd

    def findLocs(self, findf, stopAtFirst):
        assert callable(findf), findf
        assert isinstance(stopAtFirst, bool), stopAtFirst

        locs = []
        for loc, l in self.contentsd.iteritems():
            if findf(l):
                locs.append(loc)
                if stopAtFirst:
                    return locs
        return locs

    def get_inv_decls(self, traceIndicator="//%%%traces:"):
        """
        get Trace variables
        invdecls = {loc : {'x':'int'; 'y':'double'}}
        """
        invdecls = OrderedDict()
        tracesLocs = self.findLocs(lambda l: l.startswith(traceIndicator),
                                   stopAtFirst=False)
        assert tracesLocs, tracesLocs
        for loc in tracesLocs:
            l = self.contentsd[loc]
            varsd = self.mkVarsDict(stripTo(l, ':'))
            invdecls[str(loc)] = varsd
        assert invdecls
        return invdecls

    @staticmethod
    def mkVarsDict(s):
        """
        %%%indicator double x , double y .. ->  {x: int, y: double}
        where x and y are SAGE's symbolic variables
        """
        assert isinstance(s, str), s
        contents = (x.split() for x in s.split(','))
        try:
            return OrderedDict(
                (sage.all.var(k.strip()), t.strip()) for t, k in contents)
        except ValueError:
            return None

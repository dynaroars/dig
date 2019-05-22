import pdb
import os
from collections import OrderedDict
import sage.all

import vcommon as CM
from miscs import Z3
import settings
from ds import Symbs, DSymbs, DTraces

dbg = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


def parse(filename):
    assert os.path.isfile(filename), filename
    loc = 'defaultloc'
    inv_decls = DSymbs([(loc, None)])
    trace_str = []
    for i, line in enumerate(CM.iread_strip(filename)):
        if i == 0:
            # I x, I y
            inv_decls[loc] = Symbs.mk(line)
        else:
            trace_str.append(line.replace(',', ''))

    trace_str = ["{}: {}".format(loc, l) for l in trace_str]
    dtraces = DTraces.parse(trace_str, inv_decls)

    return inv_decls, dtraces

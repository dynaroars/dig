"""
Analyze and print Dig's results
"""
import random
import pdb
from collections import Counter
from pathlib import Path

import sage.all

import settings
import helpers.vcommon as CM

DBG = pdb.set_trace

mlog = CM.getLogger(__name__, settings.logger_level)


class Results:
    def __init__(self, dinvs, dtraces, inps, solver_calls, depth_changes, t_time):
        self.dinvs = dinvs
        self.dtraces = dtraces
        self.inps = inps
        self.solver_calls = solver_calls
        self.depth_changes = depth_changes
        self.t_time = t_time

    @classmethod
    def rfiles(cls, dir_):
        return [dir_ / f for f in
                ['dinvs',
                 'dtraces',
                 'inps',
                 'solver_calls',
                 'depth_changes',
                 't_time']]

    def save(self, todir):
        assert todir.is_dir(), todir

        rdata = [self.dinvs,
                 self.dtraces,
                 self.inps,
                 self.solver_calls,
                 self.depth_changes,
                 self.t_time]

        _ = [CM.vsave(f, d) for f, d in zip(self.rfiles(todir), rdata)]

    @classmethod
    def load(cls, fromdir):
        assert isinstance(fromdir, Path) and fromdir.is_dir(), fromdir

        rdata = [CM.vload(f) for f in cls.rfiles(fromdir)]
        return cls(*rdata)

    def analyze_symstates(self):

        def get_str(d):
            return "{} ({})".format(
                sum(d[k] for k in d),
                ', '.join('{} {}'.format(k, d[k]) for k in sorted(d.keys())))

        solver_calls = Counter(str(stat)
                               for stat, is_succ in self.solver_calls)

        def get_inv_typ(inv):
            # assert inv is None or isinstance(inv, Inv), inv
            try:
                return inv.__class__.__name__
            except AttributeError:
                assert inv is None
                print('W: unknown inv type: {}'.format(inv))
                return "Unknown"

        def get_change(x, y):
            return "{}->{}".format(x, y)

        change_stats = Counter(get_inv_typ(inv)
                               for inv, stat0, depth0, stat1, depth1 in self.depth_changes)
        # unsat->sat
        change_typs = Counter(get_change(stat0, stat1)
                              for inv, stat0, depth0, stat1, depth1 in self.depth_changes)
        # 9->10, 10->11
        change_depths = Counter(get_change(depth0, depth1)
                                for inv, stat0, depth0, stat1, depth1 in self.depth_changes)

        solver_calls_s = "solver calls {}".format(get_str(solver_calls))
        change_stats_s = "stats {}".format(get_str(change_stats))
        change_typs_s = "change typs {}".format(get_str(change_typs))
        change_depths_s = "change depths {}".format(get_str(change_depths))

        ss = [solver_calls_s, change_stats_s, change_typs_s, change_depths_s]
        return ', '.join(ss)

    def analyze(self):
        inv_typs = ', '.join('{} {}'.format(self.dinvs.typ_ctr[t], t)
                             for t in sorted(self.dinvs.typ_ctr))

        symstates_s = self.analyze_symstates()

        ss = [  # "file {}".format(dig.filename),
            "locs {}".format(len(self.dinvs)),
            "invs {} ({})".format(self.dinvs.siz, inv_typs),
            "traces {}".format(self.dtraces.siz),
            "inps {}".format(len(self.inps) if self.inps else 0),
            "time {:.2f}s".format(self.t_time),
            symstates_s,
            # "rand seed {}, test ({}, {})".format(
            # dig.seed, random.randint(0, 100), sage.all.randint(0, 100))
        ]
        print("***",  ', '.join(s for s in ss if s))
        print(self.dinvs.__str__(print_stat=False))

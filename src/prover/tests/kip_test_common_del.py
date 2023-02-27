import time
from vu_common import pause, is_empty, vset
from z3util import model_str, get_vars
from z3 import And, Implies, unknown, Solver, unsat, Not
import logging
import kip
Prog = kip.Prog

kip.logger.setLevel(logging.INFO)


if __name__ == "__main__":
    import doctest
    doctest.testmod()


"""
To run doctest
$ ~/miniconda3/bin/python3 -m doctest -v helpers/vcommon.py
"""

import logging
import pickle
from pathlib import Path
from typing import Any


def pause(s: str | None = None):
    """ do something """
    input("Press any key to continue ..." if s is None else s)


def vwrite(filename: str, contents: str, mode: str = 'w'):
    with open(filename, mode) as fh:
        fh.write(contents)


def getLogger(name: str, level: int) -> logging.Logger:
    logger = logging.getLogger(name)
    logger.setLevel(logging.DEBUG)
    if logger.handlers:
        # Already configured (e.g. the same module re-requesting its logger).
        # Don't stack another handler, which would duplicate every line; just
        # update the level on the existing one.
        for h in logger.handlers:
            h.setLevel(level)
        return logger
    ch = logging.StreamHandler()
    ch.setLevel(level)
    formatter = logging.Formatter("%(name)s:%(levelname)s:%(message)s")
    ch.setFormatter(formatter)
    logger.addHandler(ch)
    return logger


def getLogLevel(level: int) -> int:
    assert 0 <= level < 5
    levels = [logging.CRITICAL, logging.ERROR, logging.WARNING, logging.INFO, logging.DEBUG]
    return levels[level]


def vsave(filename: str, sobj: Any, mode: str = 'wb'):
    with open(filename, mode) as fh:
        pickle.dump(sobj, fh)


def vload(filename: str, mode: str = 'rb') -> Any:
    with open(filename, mode) as fh:
        return pickle.load(fh)


def vread(filename: str) -> str:
    return Path(filename).read_text()


if __name__ == "__main__":
    import doctest
    doctest.testmod()

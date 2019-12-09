import subprocess as sp
import logging
"""
To run doctest
$ python -m doctest -v common.py
"""


def is_python3():
    import sys
    return sys.version_info > (3, 0)


def pause(s=None):
    input("Press any key to continue ..." if s is None else s)


def iread(filename):
    """ return a generator """
    with open(filename, 'r') as fh:
        for line in fh:
            yield line


def strip_contents(lines, strip_c='#'):
    lines = (l.strip() for l in lines)
    lines = (l for l in lines if l)
    if strip_c:
        lines = (l for l in lines if not l.startswith(strip_c))
    return lines


def iread_strip(filename, strip_c='#'):
    """
    like iread but also strip out comments and empty line
    """
    return strip_contents(iread(filename), strip_c)


def vwrite(filename, contents, mode='w'):
    with open(filename, mode) as fh:
        fh.write(contents)


def vcmd(cmd, inp=None, shell=True):
    proc = sp.Popen(cmd, shell=shell, stdin=sp.PIPE,
                    stdout=sp.PIPE, stderr=sp.PIPE)
    out, err = proc.communicate(input=inp)
    if is_python3():
        return out.decode('utf-8'), err.decode('utf-8')
    else:
        return out, err


def getLogger(name, level):
    logger = logging.getLogger(name)
    logger.setLevel(logging.DEBUG)
    ch = logging.StreamHandler()
    ch.setLevel(level)
    formatter = logging.Formatter("%(name)s:%(levelname)s:%(message)s")
    ch.setFormatter(formatter)
    logger.addHandler(ch)
    return logger


def getLogLevel(level):
    assert level in set(range(5))

    if level == 0:
        return logging.CRITICAL
    elif level == 1:
        return logging.ERROR
    elif level == 2:
        return logging.WARNING
    elif level == 3:
        return logging.INFO
    else:
        return logging.DEBUG


if __name__ == "__main__":
    import doctest
    doctest.testmod()

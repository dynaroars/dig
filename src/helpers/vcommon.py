from collections import defaultdict
import multiprocessing
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


def getLogger(name, level):
    logger = logging.getLogger(name)
    logger.setLevel(logging.DEBUG)
    ch = logging.StreamHandler()
    ch.setLevel(level)
    # formatter = logging.Formatter("%(asctime)s %(process)d ] %(name)s:%(levelname)s:%(message)s")
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


def vsave(filename, sobj, mode='wb'):
    with open(filename, mode) as fh:
        import pickle
        pickle.dump(sobj, fh)


def vload(filename, mode='rb'):
    with open(filename, mode) as fh:
        import pickle
        sobj = pickle.load(fh)
    return sobj


def vread(filename):
    with open(filename, 'r') as fh:
        return fh.read()


def get_workload(tasks, n_cpus):
    """
    sage: from helpers.miscs import Miscs

    >>> wls = Miscs.get_workload(range(12),7); [len(wl) for wl in wls]
    [1, 1, 2, 2, 2, 2, 2]

    >>> wls = Miscs.get_workload(range(12),5); [len(wl) for wl in wls]
    [2, 2, 2, 3, 3]

    >>> wls = Miscs.get_workload(range(20),7); [len(wl) for wl in wls]
    [2, 3, 3, 3, 3, 3, 3]

    >>> wls = Miscs.get_workload(range(20),20); [len(wl) for wl in wls]
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

    >>> wls = Miscs.get_workload(range(12),7); [len(wl) for wl in wls]
    [1, 1, 2, 2, 2, 2, 2]

    >>> wls = Miscs.get_workload(range(146), 20); [len(wl) for wl in wls]
        [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8]
    """
    assert len(tasks) >= 1, tasks
    assert n_cpus >= 1, n_cpus

    wloads = defaultdict(list)
    for i, task in enumerate(tasks):
        cpu_id = i % n_cpus
        wloads[cpu_id].append(task)

    wloads = [wl for wl in sorted(wloads.values(), key=lambda wl: len(wl))]

    return wloads


def run_mp(taskname, tasks, f, DO_MP):
    """
    Run wprocess on tasks in parallel
    """

    def wprocess(mytasks, myQ):
        rs = None
        try:
            rs = f(mytasks)
        except BaseException as ex:
            print(f"Got exception in worker: {ex}")
            if myQ is None:
                raise
            else:
                rs = ex

        if myQ is None:
            return rs
        else:
            myQ.put(rs)

    n_cpus = multiprocessing.cpu_count()
    if len(tasks) >= 2 and n_cpus >= 2:
        Q = multiprocessing.Queue()
        wloads = get_workload(tasks, n_cpus=n_cpus)
        print(
            f"{taskname}:running {len(tasks)} jobs "
            f"using {len(wloads)} threads: {list(map(len, wloads))}"
        )

        workers = [
            multiprocessing.Process(target=wprocess, args=(wl, Q)) for wl in wloads
        ]

        for w in workers:
            w.start()

        wrs = []
        for _ in workers:
            rs = Q.get()
            if isinstance(rs, list):
                wrs.extend(rs)
            else:
                print(f"Got exception from worker: {rs}")
                raise rs

    else:
        wrs = wprocess(tasks, myQ=None)

    return wrs


if __name__ == "__main__":
    import doctest
    doctest.testmod()

import os
import os.path as path
import shutil
import operator
import subprocess as sp
from time import time
from datetime import datetime
from collections import OrderedDict
from functools import total_ordering
import itertools
"""
To run doctest
$ python -m doctest -v vu_common.py
$ sage -t common0.py
"""

__vdebug__ = True

#Data Structures

@total_ordering
class HDict(OrderedDict):
    """
    Hashable dictionary
    
    __eq__ and __lt__ + total_ordering is needed for __cmp__
    which is needed to compare or sort things

       
    >>> c = HDict([('f', frozenset(['0'])), ('g', frozenset(['0']))]) 
    >>> d = HDict([('f', frozenset(['0'])), ('g', frozenset(['1']))])
    >>> _ = {'c':c,'d':d}
    >>> _ = set([c,d])
    >>> sorted([c,d])
    [HDict([('f', frozenset(['0'])), ('g', frozenset(['0']))]), HDict([('f', frozenset(['0'])), ('g', frozenset(['1']))])]

    """
    @property
    def hcontent(self):
        try:
            return self._hcontent
        except AttributeError:
            self._hcontent = frozenset(self.iteritems())
            return self._hcontent
    
    def __hash__(self):
        try:
            return self._hash
        except AttributeError:
            self._hash = hash(self.hcontent)
            return self._hash

    def __eq__(self,other):
        return (other is self or
                (isinstance(other,HDict) and
                 self.hcontent.__eq__(other.hcontent)))

    def __lt__(self,other):
        return isinstance(other,HDict) and self.hcontent.__lt__(other.hcontent)

        
vmul = lambda l: reduce(operator.mul, l, 1)

merge_dict = lambda l: reduce(lambda x,y: OrderedDict(x.items() + y.items()),l,{})

def pause(s=None):
    try: #python2
        raw_input("Press any key to continue ..." if s is None else s)
    except NameError:
        input("Press any key to continue ..." if s is None else s)

def iset(seq,idfun=None):
    """
    returns generator
    """
    return vset(seq,idfun,as_list=False)

def vset(seq,idfun=None,as_list=True):
    """
    order preserving

    >>> vset([[11,2],1, [10,['9',1]],2, 1, [11,2],[3,3],[10,99],1,[10,['9',1]]],idfun=repr)
    [[11, 2], 1, [10, ['9', 1]], 2, [3, 3], [10, 99]]
    """
    def _uniq_normal(seq):
        d_ = {}
        for s in seq:
            if s not in d_:
                d_[s] = None
                yield s

    def _uniq_idfun(seq,idfun):
        d_ = {}
        for s in seq:
            h_ = idfun(s)
            if h_ not in d_:
                d_[h_] = None
                yield s

    if idfun is None:
        res = _uniq_normal(seq)
    else:
        res = _uniq_idfun(seq,idfun)

    return list(res) if as_list else res


def vsetdiff(seq1,seq2):
    """
    Set diff operation that preserves order, return seq1 - seq2

    EXAMPLES:

    sage: var('y')
    y
    sage: vsetdiff([x^2>=1,x-y==3,x+y==9,x-y==3],[2])
    [x^2 >= 1, x - y == 3, x + y == 9, x - y == 3]
    sage: vsetdiff([x^2>=1,x-y==3,x+y==9,x-y==3],[x-y==3])
    [x^2 >= 1, x + y == 9]
    sage: vsetdiff([x^2>=1],[x-y==3])
    [x^2 >= 1]
    sage: vsetdiff([],[x-y==3])
    []
    sage: vsetdiff([1,2,3],[2])
    [1, 3]

    """
    assert is_list(seq1)
    assert is_list(seq2)

    seq2 = set(seq2) #since  membership testing in set is quick

    return [s for s in seq1 if s not in seq2]

def vsetsymdiff(seq1,seq2):
    """
    Set symm diff operation that preserves order

    EXAMPLES:

    >>> vsetsymdiff([1,2,3,4],[1,2])
    [3, 4]
    >>> vsetsymdiff([1,2,3,4],[1,2,5,7])
    [3, 4, 5, 7]

    """
    assert is_list(seq1)
    assert is_list(seq2)


    set_u = vsetunion(seq1,seq2)
    set_i = vsetintersect(seq1,seq2)
    set_d = vsetdiff(set_u,set_i)

    return set_d

def vsetunion(seq1,seq2):
    """
    Set union operation that preserves order

    EXAMPLES
    >>> vsetunion([1,2,3,4],[1,2,5,7])
    [1, 2, 3, 4, 5, 7]
    >>> vsetunion([7,1,2,3,4],[1,2,5,7])
    [7, 1, 2, 3, 4, 5]

    """
    assert is_list(seq1)
    assert is_list(seq2)

    seq1_ = set(seq1) #since  membership testing in set is quick

    seq2 = [s for s in seq2 if s not in seq1_]

    return seq1 + seq2

def vsetintersect(seq1,seq2):
    """
    Set intersection operation that preserves order

    >>> vsetintersect([1,2,3],[])
    []
    >>> vsetintersect([1,2,3],[3])
    [3]
    >>> vsetintersect([],[3])
    []
    >>> vsetintersect([2],[3])
    []
    >>> vsetintersect([1,2,3,7],[3,5,7])
    [3, 7]
    """
    assert is_list(seq1)
    assert is_list(seq2)

    seq2 = set(seq2)
    return [s for s in seq1 if s in seq2]



def vflatten(l, ltypes=(list, tuple)):
    ltype = type(l)
    l = list(l)
    i = 0
    while i < len(l):
        while isinstance(l[i], ltypes):
            if not l[i]:
                l.pop(i)
                i -= 1
                break
            else:
                l[i:i + 1] = l[i]
        i += 1
    return ltype(l)


simple_flatten = lambda l: [item for sublist in l for item in sublist] #return a list
iflatten = lambda l: itertools.chain.from_iterable(l) #return a generator

def dict2str(d, count=0, ignores=[], print_size_only=[],join_str=', '):
    """
    Returns a string from the input dict.

    >>> print dict2str(d={1:'ba','kw1':True,'kw2':(1,2),'kw3':[4,7],'kw4':100, 'kw5':'hello','kw6':8,'kw7':range(10),'kw8':{'kw1a':3}},ignores=['kw4'])
    0. 1: ba
    1. kw1: True
    2. kw2: 1, 2
    3. kw3: 4, 7
    4. kw5: hello
    5. kw6: 8
    6. kw7: 0, 1, 2, 3, 4, 5, 6, 7, 8, 9
    7. kw8: 
     0. kw1a: 3

    >>> print dict2str(d={1:'ba','kw1':True,'kw2':(1,2),'kw3':[4,7],'kw4':100, 'kw5':'hello','kw6':8,'kw7':range(10),'kw8':{'kw1a':3},'kw9':{'kw9a':[10]},'kw10':range(5)},ignores=['kw4'],print_size_only=['kw10','kw9a'])
    0. 1: ba
    1. kw1: True
    2. |kw10|: 5
    3. kw2: 1, 2
    4. kw3: 4, 7
    5. kw5: hello
    6. kw6: 8
    7. kw7: 0, 1, 2, 3, 4, 5, 6, 7, 8, 9
    8. kw8: 
     0. kw1a: 3
    9. kw9: 
     0. |kw9a|: 1

    >>> print dict2str(d={1:'ba','kw1':True,'kw2':(1,2),'kw3':[4,7],'kw4':100, 'kw5':'hello','kw6':8,'kw7':range(10),'kw8':{'kw1a':3},'kw9':{'kw9a':[10]},'kw10':range(5)},ignores=['kw4'],print_size_only=['kw10','kw9a', 'kw8'])
    0. 1: ba
    1. kw1: True
    2. |kw10|: 5
    3. kw2: 1, 2
    4. kw3: 4, 7
    5. kw5: hello
    6. kw6: 8
    7. kw7: 0, 1, 2, 3, 4, 5, 6, 7, 8, 9
    8. |kw8|: 1
    9. kw9: 
     0. |kw9a|: 1

      print dict2str(d={1:'ba','kw1':True,'kw2':(1,2),'kw3':[4,7],'kw4':100, 'kw5':'hello','kw6':8,'kw7':range(10),'kw8':{'kw1a':3},'kw9':{'kw9a':[10]},'kw10':range(5)},ignores=['kw4',1],print_size_only=['kw10','kw9a'])
      0. kw1: True
      1. |kw10|: 5
      2. kw2: (1, 2)
      3. kw3: [4, 7]
      4. kw5: hello
      5. kw6: 8
      6. kw7: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
      7. kw8:
        0. kw1a: 3
      8. kw9:
        0. |kw9a|: 1

    """
    rs = []
    items = sorted(d.iteritems(), key=lambda xy: str(xy[0]))

    i=0
    for (k, v) in items:
        if k in ignores: continue
            
        if k in print_size_only:
            k = '|%s|'%k
            try:
                v = str(len(v))
            except TypeError:  #v could be None
                pass
            
        elif is_dict(v):
            v = '\n' + dict2str(v, count+1, ignores, print_size_only)
        elif is_iterable(v):
            v = str_of_list(v, join_str)
            
        rs.append('%d. %s: %s'%(i,k,v))
        i = i + 1


    rs = [(' ' * count) + r_ for r_ in rs]
    rs = '\n'.join(rs)

    return rs


def isnum(s):
    """
    >>> assert isnum([1,2]) == False
    >>> assert isnum(7)
    >>> assert isnum('7')
    >>> assert isnum('s') == False
    >>> assert isnum(7/3)
    >>> assert isnum(7.2)
    >>> assert isnum(0.1)
    >>> assert isnum(True)
    >>> assert isnum(False)
    >>> assert isnum('False') == False
    """
    try: float(s);     return True
    except ValueError: return False
    except TypeError : return False


def vall_uniq(ls,idfun=None):
    """
    >>> vall_uniq([])
    True
    >>> vall_uniq([1,1])
    False
    >>> vall_uniq([1,2,1])
    False
    >>> vall_uniq([[1],[2],[1]],idfun=repr)
    False
    >>> vall_uniq([[1],[2],[3]],idfun=repr)
    True
    >>> vall_uniq([[1],[2],[3]],idfun=len)
    False
    """
    return len(vset(ls,idfun=idfun)) == len(ls)

def vall_same(ls, idfun=lambda x:x):
    """
    return true iff forall(x,y) in ls,  f(x) = f(y)

    >>> vall_same([],idfun=len)
    False
    >>> vall_same([[1],[2]],idfun=len)
    True
    >>> vall_same([[1],[2,3]],idfun=len)
    False
    >>> vall_same([[]],idfun=len)
    True
    >>> vall_same([],idfun=len)
    False
    >>> vall_same([[]],idfun=len)
    True
    """
    return len(vset(ls,idfun=idfun)) == 1


def tsplit(s, d):
    """
    >>> tsplit("hello,my|name+is-bob", (",", "|", "+", "-"))
    ['hello', 'my', 'name', 'is', 'bob']
    """
    import re
    return re.split('|'.join(map(re.escape, d)),s)


def get_fun_args():
    """Returns tuple containing dictionary of calling function's
    named arguments and a list of calling function's unnamed
    positional arguments.
    """
    from inspect import getargvalues, stack
    posname, kwname, args = getargvalues(stack()[1][0])[-3:]
    posargs = args.pop(posname, [])
    args.update(args.pop(kwname, []))
    return args, posargs

def is_iterable(l):
    """
    >>> is_iterable(7)
    False
    >>> is_iterable([7])
    True
    >>> is_iterable(tuple([7]))
    True
    >>> is_iterable(set([7]))
    True
    >>> is_iterable('abc')
    False
    >>> d = {7:None}
    >>> is_iterable(d)
    True
    """
    return hasattr(l,"__iter__")

is_tuple = lambda v: isinstance(v,tuple)
is_list = lambda v: isinstance(v,list)
is_dict = lambda v: isinstance(v,dict)
is_str  = lambda v: isinstance(v,str)
is_bool  = lambda v: isinstance(v,bool)
is_empty = lambda v: len(v) == 0
is_none = lambda v: v is None
is_none_or_empty = lambda v: is_none(v) or is_empty(v)


def get_md5(s):
    import hashlib
    return hashlib.md5(s).hexdigest()

def imply(pred1,pred2):
    """
    Returns True if pred1 implies pred2 , i.e. not pred1 or pred2.
    pred1, pred2 are bool vars
    """
    return (not pred1) or pred2


def create_dict(l):
    """
    given a list of set of type [(k1,v1),..,(kn,vn)]
    generates a dict where keys are k's and values are [v's]
    e.g.,

    >>> d = create_dict([('a',1),['b',2],('a',3),('c',4),('b',10)]); d
    OrderedDict([('a', [1, 3]), ('b', [2, 10]), ('c', [4])])
    >>> d['x']
    Traceback (most recent call last):
    ...
    KeyError: 'x'
    """
    return reduce(lambda d,kv:d.setdefault(kv[0],[]).append(kv[1]) or d,l,OrderedDict())

def create_dict2(l):
    """
    Group a seq of key-value pairs into dictionary of list.
    Using defaultdict is more efficient than setdefault --
    But, it's not equiv to create_dict because it does not
    generate Error when key not in dict

    EXAMPLES:
    >>> create_dict2([('a',1),['b',2],('a',3),('c',4),('b',10)])
    defaultdict(<type 'list'>, {'a': [1, 3], 'c': [4], 'b': [2, 10]})

    >>> d = create_dict2([('yellow', 1), ('blue', 2), ('yellow', 3), ('blue', 4), ('red', 1)]); d.items()
    [('blue', [2, 4]), ('red', [1]), ('yellow', [1, 3])]
    >>> d['x']
    []
    """
    from collections import defaultdict

    d = defaultdict(list)
    for k, v in l:
        d[k].append(v)

    return d


def create_hash(ls):
    """
    Examples:

    >>> create_hash([1,2,3])
    {1: None, 2: None, 3: None}
    """
    return dict.fromkeys(ls)

def issorted(ls):
    """
    using lazy iterators

    slower 1 line version:
    issorted = lambda ls: all(b >= a for a, b in zip(ls, ls[1:]))

    """
    it = iter(ls)
    it.next()
    return all(b >= a for a, b in itertools.izip(ls, it))


def vread(filename):
    with open(filename, 'r') as fh:
        return fh.read()

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

def vsave(filename,sobj,mode='wb'):
    try:
        import cPickle as pickle
    except ImportError:  #Python3
        import pickle
        
    with open(filename,mode) as fh:
        pickler = pickle.Pickler(fh,-1)
        pickler.dump(sobj)

def vload(filename,mode='rb'):
    try:
        import cPickle as pickle
    except ImportError:  #Python3
        import pickle

    with open(filename,mode) as fh:
        pickler = pickle.Unpickler(fh)
        sobj = pickler.load()
    return sobj

def vmkdir(dir_):
    """
      creates directory 'dir_' if it's not existed
    """
    try:
        os.makedirs(dir_)
    except OSError as why:
        print(why)


def vmv(src, dst):
    """
    moves file/dir 'src' to 'dst'
    """
    shutil.move(src, dst)


def vrm(filename, mkdir=False):
    """
    deletes file/dir
    """
    if path.isdir(filename):
        shutil.rmtree(filename)
    elif path.isfile(filename) or path.islink(filename):
        os.remove(filename)
    elif path.exists(filename):
        vcmd("rm -rf " + filename)

    if mkdir:
        vmkdir(filename)


def vtime(f,args,s=None):
    stime = time()
    res = f(**args) if is_dict(args) else f(*args)
    time_elapsed = time() - stime

    #print 'Time elapsed: %.4f s (%s)' \
    #    %(time_elapsed,('function ' + f.func_name) if s is None else s)

    return res,time_elapsed


def check_range(x,min_x,max_x):
    """
    >>> print check_range(0,3,7)
    3
    >>> print check_range(10,3,7)
    7
    >>> print check_range(10,7,3)
    3
    """
    x = max(x,min_x)
    x = min(x,max_x)
    return x

def is_file_empty(filename):
    "returns True if file size is 0 or contents are just space and '\n' "

    if path.getsize(filename) == 0:
        return True
    else:
        lines = vread(filename)
        return lines.strip().strip('\n') == ''


def rm_empty_files(dir_):
    """remove all empty files in dir dir_"""

    import glob

    efs1 = [f for f in glob.glob(os.path.join(dir_,'*.err*'))
            if is_file_empty(f)]
    efs2 = [f for f in glob.glob(os.path.join(dir_,'*.dk_err*'))
            if is_file_empty(f)]
    efs = efs1 + efs2
    if efs:
        for f in efs:
            vrm(f)
        #print ("rm %d empty *err* files" %len(efs))

def vcmd(cmd, inp=None, shell=True):
    proc = sp.Popen(cmd,shell=shell,stdin=sp.PIPE,stdout=sp.PIPE,stderr=sp.PIPE)
    return proc.communicate(input=inp)

def vcmd1(cmd):
    import shlex
    proc = sp.Popen(shlex.split(cmd),stdout=sp.PIPE)
    return proc.communicate()[0]


def vpartition(seq, pred, parts=2):
    """
    >>> vpartition(xrange(10), lambda x: x%5, parts=5)
    [[0, 5], [1, 6], [2, 7], [3, 8], [4, 9]]

    >>> vpartition(xrange(10),lambda x: x%2==0)
    [[1, 3, 5, 7, 9], [0, 2, 4, 6, 8]]

    >>> vpartition([],lambda x: x%2 == 0)
    [[], []]
    """

    res = [[] for _ in xrange(parts)]
    for e in seq:
        res[int(pred(e))].append(e)
    return res

def ipartition(seq,pred,parts=2):
    """
    >>> map(list,list(ipartition(xrange(10), lambda x: x%5, parts = 5)))
    [[0, 5], [1, 6], [2, 7], [3, 8], [4, 9]]
    >>> map(list,list(ipartition(xrange(10), lambda x: x%5)))
    [[0, 5], [1, 6]]
    >>> map(list,list(ipartition(xrange(10), lambda x: x%5)))
    [[0, 5], [1, 6]]
    >>> map(list,list(ipartition(xrange(10), lambda x: x%2)))
    [[0, 2, 4, 6, 8], [1, 3, 5, 7, 9]]
    >>> map(list,list(ipartition(xrange(0), lambda x: x%2)))
    [[], []]
    """
    mfilter = lambda k,it: itertools.ifilter(lambda x: pred(x)==k, it)
    return (mfilter(i,r) for i,r in enumerate(itertools.tee(seq, parts)))
                    
getpath = lambda f: os.path.realpath(os.path.expanduser(f))

vsublist = lambda l1,l2: all(v in l2 for v in l1)
#vall(l1,lambda x: x in l2)


find_first = lambda xs,f: next((x for x in xs if f(x)), None)

def mtime(f):
    def wrapper(self,*args,**kws):
        from time import time
        stime = time()
        rs = f(self,*args,**kws)
        time_elapsed = time() - stime

        # print 'Time elapsed: %.4f s (%s)' \
        #     %(time_elapsed,('function ' + f.func_name))

        return rs,time_elapsed

    return wrapper


def list_str(L, join_str=', '):
    return '{}'.format(join_str.join(map(str, L)))

str_of_list = list_str

def get_logger(logger_name,very_detail=True):
    assert is_str(logger_name) and logger_name, logger_name
    assert is_bool(very_detail), very_detail

    import logging

    logger = logging.getLogger(logger_name)
    ch = logging.StreamHandler()
    if very_detail:
        f = "%(asctime)s:%(filename)s:%(funcName)s:%(levelname)s: %(message)s"
        formatter = logging.Formatter(f,datefmt='%H:%M:%S')
    else:
        f = "%(levelname)s: %(message)s"
        formatter = logging.Formatter(f)

    ch.setFormatter(formatter)
    logger.addHandler(ch)
    return logger


class VLog(object):
    """
    >>> logger = VLog('vu_logger')
    >>> assert logger.level  == VLog.INFO
    >>> logger.detail('detail msg')
    >>> logger.debug('debug msg')
    >>> logger.info('info msg')
    vu_logger:Info:info msg
    >>> logger.warn('warn msg')
    vu_logger:Warn:warn msg
    >>> logger.error('error msg')
    vu_logger:Error:error msg

    >>> logger.set_level(VLog.DETAIL)
    >>> logger.detail('detail msg')
    vu_logger:Detail:detail msg
    >>> f = lambda: 'detail msg'
    >>> logger.detail(f)
    vu_logger:Detail:detail msg
    >>> logger.debug('debug msg')
    vu_logger:Debug:debug msg
    >>> logger.info('info msg')
    vu_logger:Info:info msg
    >>> logger.warn('warn msg')
    vu_logger:Warn:warn msg
    >>> logger.error('error msg')
    vu_logger:Error:error msg
    """
    ERROR = 0
    WARN = 1
    INFO = 2
    DEBUG = 3
    DETAIL = 4
    
    level_d = {ERROR: 'Error',
               WARN: 'Warn',
               INFO: 'Info',
               DEBUG: 'Debug',
               DETAIL: 'Detail'}

    try:  #python2
        level_d_rev = dict((v,k) for (k,v) in level_d.iteritems())
    except AttributeError: #python 3
        level_d_rev = dict((v,k) for (k,v) in level_d.items())

    def __init__(self, name):
        self.name = name
        self.level = VLog.INFO
        self.printtime = False
        
    def get_level(self): 
        return self._level

    def set_level(self, level):
        assert level in self.level_d, level
        self._level = level
    level = property(get_level,set_level)


    def get_printtime(self): 
        return self._printtime

    def set_printtime(self, printtime):
        assert isinstance(printtime, bool), printtime
        self._printtime = printtime
    printtime = property(get_printtime,set_printtime)
    
    def print_s(self, s, level):
        if self.level < level:
            return
        else:
            if not isinstance(s,str):
                s = s()
                
            level_name =  self.level_d[level]
            if self.printtime:
                print("{}:{}:{}:{}"
                      .format(get_cur_time(),self.name,level_name, s))
            else:
                print("{}:{}:{}"
                      .format(self.name,level_name, s)) 

    def detail(self, s): self.print_s(s, VLog.DETAIL)
    def debug(self, s): self.print_s(s, VLog.DEBUG)
    def info(self, s): self.print_s(s, VLog.INFO)
    def warn(self, s): self.print_s(s, VLog.WARN)
    def error(self, s): self.print_s(s, VLog.ERROR)

file_basename = lambda filename: path.splitext(filename)[0]
file_extension = lambda filename: path.splitext(filename)[1]

def get_cur_time(time_only=True):
    now = datetime.now()
    if time_only:
        return "{}:{}:{}".format(now.hour,now.minute,now.second)
    else:
        return str(now)

#Multiprocessing stuff
def get_workloads(tasks,max_nprocesses,chunksiz):
    """
    >>> wls = get_workloads(range(12),7,1); wls
    [[0, 1], [2, 3], [4, 5], [6, 7], [8, 9], [10, 11]]


    >>> wls = get_workloads(range(12),5,2); wls
    [[0, 1], [2, 3], [4, 5], [6, 7], [8, 9, 10, 11]]

    >>> wls = get_workloads(range(20),7,2); wls
    [[0, 1, 2], [3, 4, 5], [6, 7, 8], [9, 10, 11], [12, 13, 14], [15, 16, 17], [18, 19]]


    >>> wls = get_workloads(range(20),20,2); wls
    [[0, 1], [2, 3], [4, 5], [6, 7], [8, 9], [10, 11], [12, 13], [14, 15], [16, 17], [18, 19]]

    """

    assert len(tasks) >= 1, tasks
    assert max_nprocesses >= 1, max_nprocesses
    assert chunksiz >= 1, chunksiz

    #determine # of processes
    ntasks = len(tasks)
    nprocesses = int(round(ntasks/float(chunksiz)))
    if nprocesses > max_nprocesses:
        nprocesses = max_nprocesses

    #determine workloads 
    cs = int(round(ntasks/float(nprocesses)))
    workloads = []
    for i in range(nprocesses):
        s = i*cs
        e = s+cs if i < nprocesses-1 else ntasks
        wl = tasks[s:e]
        if wl:  #could be 0, e.g., get_workloads(range(12),7,1)
            workloads.append(wl)

    return workloads

def callMultiF(f,n,cache):
    """
    Try to get n unique results by calling f() multiple times
    >>> import random
    >>> random.seed(0)
    >>> callMultiF(lambda : random.randint(0,10), 9, set())
    [9, 8, 4, 2, 5, 3, 6, 10]
    >>> random.seed(0)
    >>> callMultiF(lambda : random.randint(0,10), 9, set([8,9,10]))
    [4, 2, 5, 3, 6, 7]
    """
    rs = []
    rs_s = set()
    if cache:
        for c in cache: rs_s.add(c)
        
    for _ in range(n):
        c = f()

        c_iter = 0
        while c in rs_s and c_iter < 3:
            c_iter += 1
            c = f()

        if c not in rs_s:
            rs_s.add(c)
            rs.append(c)

    assert len(rs) <= n
    return rs

if __name__ == "__main__":
    import doctest
    doctest.testmod()



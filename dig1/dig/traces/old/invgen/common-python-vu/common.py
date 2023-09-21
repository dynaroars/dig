import os
import os.path as path
import shutil
import subprocess as sp
import shlex

"""
To run doctest
$ python -m doctest -v common0.py
$ sage -t common0.py
"""

is_none_or_empty = lambda l: l is None or len(l) == 0
merge_dict = lambda l: reduce(lambda x,y: dict(x.items() + y.items()),l,{})




def pause(s=None):
    raw_input("Press any key to continue ..." if s is None else s)


def vset(seq,idfun=None):
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
    
    return list(res)



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
    if __debug__:
        assert isinstance(seq1,list)
        assert isinstance(seq2,list)
    
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
    if __debug__:
        assert isinstance(seq1,list)
        assert isinstance(seq2,list)


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
    if __debug__:
        assert isinstance(seq1,list)
        assert isinstance(seq2,list)
    
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
    if __debug__:
        assert isinstance(seq1,list)
        assert isinstance(seq2,list)

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



def dict2str(d, count=0, ignores=[], print_size_only=[]):
    """
    Returns a string from the input dict.

    print dict2str(d={1:'ba','kw1':True,'kw2':(1,2),'kw3':[4,7],'kw4':100, 'kw5':'hello','kw6':8,'kw7':range(10),'kw8':{'kw1a':3}},ignores=['kw4'])
    0. 1: ba
    1. kw1: True
    2. kw2: (1, 2)
    3. kw3: [4, 7]
    4. kw5: hello
    5. kw6: 8
    6. kw7: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
    7. kw8: 
      0. kw1a: 3

    print dict2str(d={1:'ba','kw1':True,'kw2':(1,2),'kw3':[4,7],'kw4':100, 'kw5':'hello','kw6':8,'kw7':range(10),'kw8':{'kw1a':3},'kw9':{'kw9a':[10]},'kw10':range(5)},ignores=['kw4'],print_size_only=['kw10','kw9a'])
     0. 1: ba
      1. kw1: True
      2. |kw10|: 5
      3. kw2: (1, 2)
      4. kw3: [4, 7]
      5. kw5: hello
      6. kw6: 8
      7. kw7: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
      8. kw8: 
        0. kw1a: 3
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

    items = sorted(d.items(), key=lambda (x,_): str(x))

    i=0
    for (k, v) in items:

        if k in ignores:
            continue
        
        if isinstance(v,dict):
            v = '\n' + dict2str(v, count+1, ignores, print_size_only)
        else:
            if k in print_size_only and hasattr(v,"__iter__"):
                k = '|%s|'%k
                v = str(len(v))

        rs.append('%d. %s: %s'%(i,k,v))
        i = i+1


    rs = [(' ' * count) + r_ for r_ in rs]
    rs = '\n'.join(rs)

    return rs


def isnum(s):
    """
    >>> isnum([1,2])
    False
    >>> isnum(7)
    True
    >>> isnum('7')
    True
    >>> isnum('s')
    False
    >>> isnum(7/3)
    True
    >>> isnum(7.2)
    True
    >>> isnum(0.1)
    True
    >>> isnum(True)
    True
    >>> isnum(False)
    True
    >>> isnum('False')
    False
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

def vall_same(ls,idfun=lambda x:x,verbose=1):
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




def get_arguments():
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




def get_md5(s):
    import hashlib
    return hashlib.md5(s).hexdigest()


def imply(pred1,pred2):
    """
    Returns True if pred1 implies pred2 , i.e. not pred1 or pred2.
    pred1, pred2 are bool vars
    """
    return (not pred1) or pred2




def tsplit(s, d):
    """
    >>> tsplit("hello,my|name+is-bob", (",", "|", "+", "-"))
    ['hello', 'my', 'name', 'is', 'bob']
    """
    import re
    return re.split('|'.join(map(re.escape, d)),s)


def get_arguments():
    """Returns tuple containing dictionary of calling function's
    named arguments and a list of calling function's unnamed
    positional arguments.
    """
    from inspect import getargvalues, stack
    posname, kwname, args = getargvalues(stack()[1][0])[-3:]
    posargs = args.pop(posname, [])
    args.update(args.pop(kwname, []))
    return args, posargs

def create_dict(l):
    """
    given a list of set of type [(k1,v1),..,(kn,vn)]
    generates a dict where keys are k's and values are [v's]
    e.g.,
    
    >>> create_dict([('a',1),['b',2],('a',3),('c',4),('b',10)])
    {'a': [1, 3], 'c': [4], 'b': [2, 10]}
    
    """
    return reduce(lambda d,(k,v):d.setdefault(k,[]).append(v) or d,l,{})

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
    import itertools

    it = iter(ls)
    it.next()
    return all(b >= a for a, b in itertools.izip(ls, it))



        
def vread(filename, verbose=1):
    if verbose >= 1:
        print("read '{f}'".format(f=filename))

    with open(filename, 'r') as fh: 
        return fh.read()

def vwrite(filename, contents, mode='w',verbose=1):
    if verbose >= 1:
        print("writing file '{f}'".format(f=filename))

    with open(filename, mode) as fh: 
        fh.write(contents)


def vmkdir(dir_, verbose=1):
  """
  creates directory 'dir_' if it's not existed
  """
  if verbose>=1: 
      print("# mkdir " + dir_)
  
  try:
      os.makedirs(dir_)
  except OSError as why: 
      print why


def vmv(src, dst, verbose=1):
  """
  moves file/dir 'src' to 'dst'
  """
  if verbose >= 1: 
    print("# mv %s -> %s" %(src,dst))

  try:
    shutil.move(src, dst)
  except (OSError, IOError) as why: 
    print why


def vrm(filename, mkdir=False, verbose=1): 
  """
  deletes file/dir 
  """
  if verbose >= 0: 
    print("# rm " + filename)

  try:
      if path.isdir(filename):
          shutil.rmtree(filename)
      elif path.isfile(filename) or path.islink(filename):
          os.remove(filename)
      elif path.exists(filename):
          if verbose: 
              print("W: '%s' not regular file" %filename)
        
          vcmd("rm -rf " + filename, verbose=verbose)
  except OSError as why: 
      print(why)

  if mkdir: 
      vmkdir(filename, verbose)


def vtime(f,args,s=None,verbose=1):
    import time
    stime = time.time()
    res = f(**args) if isinstance(args,dict) else f(*args)
    time_elapsed = time.time() - stime
    if verbose >= 1:
        print 'Time elapsed: %.4f s (%s)' \
            %(time_elapsed,('function ' + f.func_name) if s is None else s)

    return res,time_elapsed



def is_empty(filename):
    "returns True if file size is 0 or contents are just space and '\n' "

    if path.getsize(filename) == 0: 
        return True
    else:
        lines = vread(filename)
        return lines.strip().strip('\n') == ''


def rm_empty_files(dir_,verbose=1):
    """remove all empty files in dir dir_"""

    import glob

    efs1 = [f for f in glob.glob(os.path.join(dir_,'*.err*'))
            if is_empty(f)]
    efs2 = [f for f in glob.glob(os.path.join(dir_,'*.dk_err*'))
            if is_empty(f)]
    efs = efs1 + efs2
    if efs:
        for f in efs:
            vrm(f, verbose=verbose)
        print ("rm %d empty *err* files" %len(efs))

def vcmd_to(cmd, inp, timeout, verbose=1):
    try:
        alarm(timeout)
        proc = sp.Popen(cmd,stdin=sp.PIPE,stdout=sp.PIPE,stderr=sp.PIPE)
        return proc.communicate(input=inp)

    except KeyboardInterrupt:
        print "Timeout (%d secs): Terminate process %s" \
              %(timeout,' '.join(cmd))
        return None,'timeout'

def vcmd(cmd, inp=None, shell=True, verbose=1):
    
    proc = sp.Popen(cmd,shell=shell,stdin=sp.PIPE,stdout=sp.PIPE,stderr=sp.PIPE)
    return proc.communicate(input=inp)

def vcmd1(cmd, verbose=1):

    if verbose >= 1: 
        print('$ ' + cmd)

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

    res = [[] for i in xrange(parts)] 
    for e in seq: 
        res[int(pred(e))].append(e) 
    return res 



def vall(S,P):
    """
    >>> vall([1,2,5], lambda x : x > 3)
    False
    >>> vall([1,2,5], lambda x : x > 0)
    True

    """
    for x in S:
        if not P(x): return False
    return True

def vany(S,P):
    """
    >>> vany([1,2,5], lambda x : x > 7)
    False
    >>> vany([1,2,5], lambda x : x > 3)
    True
    >>> cubes = [t**3 for t in range(-10,11)]
    >>> vany([(x,y) for x in cubes for y in cubes], lambda v : v[0]+v[1] == 218)
    True
    >>> vany([(x,y) for x in cubes for y in cubes], lambda v : v[0]+v[1] == 219)
    False

    """
    for x in S:
        if P(x): return True
    return False
    

vsublist = lambda l1,l2: vall(l1,lambda x: x in l2)

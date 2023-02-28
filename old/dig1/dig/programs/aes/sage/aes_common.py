from sage.all import *

def xor(x,y, verbose=1):
    """
    sage: xor(2,3)
    1
    sage: xor(8,5)
    13
    sage: xor(5,8)
    13
    """
    x = convertInt(x)
    y = convertInt(y)

    res = x.__xor__(y)

    return res

def myxor(xs):
    """
    sage: myxor([3,7,15,9])
    2
    sage: myxor([3,-7,5,99])
    -100
    """

    assert len(xs)>1

    res = reduce(lambda r_,x: xor(r_,x),xs)
    return res

def myand(xs):
    assert len(xs)>1
    return reduce(lambda r_,x: r_.__and__(x),xs)


def convertInt(x):
    if not isinstance(x,sage.rings.integer.Integer):
        x  = Integer(x)
    return x




MAXKC = 8
MAXNR = 14

byte = 2**8  #256

is_byte = lambda b: 0 <= b <= (byte - 1)

byte_index = 16 #0..15
is_block = lambda b: len(b)==byte_index and all(is_byte(b_) for b_ in b)

key_index = 4*MAXKC  #32
is_key = lambda k: len(k)==key_index and all(is_byte(k_) for k_ in k)

roundkey_index = 4*(MAXNR+1) #60



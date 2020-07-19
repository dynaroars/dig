from copy import deepcopy
from vu_common import pause
from aes_common import xor, xor_xor, myxor
from aes_common import (byte, is_byte, byte_index, is_block, key_index, is_key, roundkey_index,
                       S, Si, rcon, Alogtable, Logtable, is_word, is_state, is_key_schedule,
                       state_index, word_index) 

"""
based on the ADA _annotated/refactored_ implementation
"""

nk_vals = [4, 6, 8]
nr_vals = [10, 12, 14]
keybit_vals = [128, 192, 256]


### Functions

def mul(a,b ,verbose=1):
    """
    >>> mul(5,3,verbose=0)
    15
    >>> mul(5,0,verbose=0)
    0
    >>> mul(255,7,verbose=0)
    203
    >>> mul(7,255,verbose=0)
    203
    >>> mul(87,215,verbose=0)
    157
    >>> mul(187,153,verbose=0)
    79

    """
    if __debug__:
        assert is_byte(a) and is_byte(b), (a,b)

    if verbose >=1:
        print 'l1: a b'
        print 'l1: ', [a], [b]

    if a != 0 and b != 0:
        r =  Alogtable[(Logtable[a] + Logtable[b]) % 255]
    else:
        r =  0

    if verbose >= 1: #tvn traces
        print 'l0: r a b'
        print 'l0: ', [r], [a], [b]

    assert is_byte(r)
    return r

def word_xor(a,b,verbose=1):
    """
    >>> word_xor([1,2,3,4],[1,2,3,4])
    [0, 0, 0, 0]

    >>> word_xor([1,2,3,4],[2,3,4,5])
    [3, 1, 7, 1]

    >>> word_xor([8,91,24,18],[73,143,43,11],verbose=0)
    [65, 212, 51, 25]

    >>> word_xor([18,91,234,88],[93,114,57,10],verbose=0)
    [79, 41, 211, 82]

    >>> word_xor([93,114,57,10],[18,91,234,88],verbose=0)
    [79, 41, 211, 82]

    """

    assert is_word(a) and is_word(b)

    r =  [xor(a[0],b[0]), xor(a[1],b[1]),
          xor(a[2],b[2]), xor(a[3],b[3])]

    if verbose >= 1: #tvn traces
        print 'l0: r a b'
        print 'l0: ', r, a, b

    assert is_word(r)
    return r


def word_xor_xor(a,b,c,verbose=1):
    r = [xor_xor(a[0],b[0],c[0]),
         xor_xor(a[1],b[1],c[1]),
         xor_xor(a[2],b[2],c[2]),
         xor_xor(a[3],b[3],c[3])]

    assert (is_word(a) and is_word(b) and is_word(c))

    if verbose >= 1: #tvn traces

        print 'l0: r a b c'
        print 'l0: ', r, a, b, c

    assert is_word(r)
    return r

def SubWord(w, verbose=1):
    """
    tvn: *nested* array
    r[i] = S[w[i]]
    """

    assert is_word(w)

    r =  [S[w[0]], S[w[1]], S[w[2]], S[w[3]]];

    if verbose >= 1:    #tvn traces
        print 'l0: r w'
        print 'l0: ', r, w

    assert is_word(r)
    return r


def RotWord(w, verbose=1):
    """
    #tvn: miscs array type
    r0 = w1 , r1 = w2,  r2 = w3, r3 = w0

    """
    assert is_word(w)

    r = [w[1], w[2], w[3], w[0]];

    #tvn traces
    if verbose >= 1:
        print 'l0: r w'
        print 'l0: ', r,w

    assert is_word(r)
    return r

def Block2State(t, verbose=1):
    """
    tvn: multidim array inv
    r[i][j] = t[4i+j]
    """
    assert is_block(t)
    
    #inv : should get this:  r00 = t0 , r01 = t1  ....
    r =  [[t[0], t[1], t[2], t[3]],
          [t[4], t[5], t[6], t[7]],
          [t[8], t[9], t[10], t[11]],
          [t[12], t[13], t[14], t[15]]]

    #tvn traces
    if verbose >= 1:
        print 'l0: r t'
        print 'l0: ', r, t

    assert is_state(r)
    return r

def State2Block(st, verbose = 1):
    """
    tvn: multidim array inv
    r[4*i+j] = st[i][j]
    """
    assert is_state(st)

    #inv: should get this:r0 = st00 ...
    r =  [st[0][0], st[0][1], st[0][2], st[0][3],
          st[1][0], st[1][1], st[1][2], st[1][3],
          st[2][0], st[2][1], st[2][2], st[2][3],
          st[3][0], st[3][1], st[3][2], st[3][3]]

    #tvn traces
    if verbose >= 1:
        print 'l0: r st'
        print 'l0: ', r, st

    assert is_block(r)
    return r

def SubBytes(st, verbose=1):
    """
    tvn: *nested* array
    r[i,j] = S[st[i,j]]
    """

    assert is_state(st)

    r =  [[S[st[0][0]], S[st[0][1]], S[st[0][2]], S[st[0][3]]],
          [S[st[1][0]], S[st[1][1]], S[st[1][2]], S[st[1][3]]],
          [S[st[2][0]], S[st[2][1]], S[st[2][2]], S[st[2][3]]],
          [S[st[3][0]], S[st[3][1]], S[st[3][2]], S[st[3][3]]]]

    if verbose >= 1: #tvn traces
        print 'l0: r st'
        print 'l0: ', r, st

    assert is_state(r)

    return r

def InvSubBytes(st, verbose=1):
    """
    tvn: *nested* array
    r[i,j] = Si[st[i,j]]
    """

    assert is_state(st)

    r= [[Si[st[0][0]], Si[st[0][1]], Si[st[0][2]], Si[st[0][3]]],
        [Si[st[1][0]], Si[st[1][1]], Si[st[1][2]], Si[st[1][3]]],
        [Si[st[2][0]], Si[st[2][1]], Si[st[2][2]], Si[st[2][3]]],
        [Si[st[3][0]], Si[st[3][1]], Si[st[3][2]], Si[st[3][3]]]]

    if verbose >= 1: #tvn traces
        print 'l0: r st'
        print 'l0: ', r, st

    assert is_state(r)
    return r

def ShiftRows(st, verbose=1):
    """
    tvn: miscs array inv
    [-r_3_3 + st_2_3 == 0, r_2_0 - st_2_0 == 0, r_3_1 - st_0_1 == 0, -r_1_3 + st_0_3 == 0, -r_2_2 + st_0_2 == 0, r_1_0 - st_1_0 == 0, r_0_1 - st_1_1 == 0, -r_0_3 + st_3_3 == 0, r_3_0 - st_3_0 == 0, r_0_0 - st_0_0 == 0, -r_3_2 + st_1_2 == 0, r_1_1 - st_2_1 == 0, -r_0_2 + st_2_2 == 0, r_2_1 - st_3_1 == 0, -r_2_3 + st_1_3 == 0, r_1_2 - st_3_2 == 0]

    >>> ShiftRows([[1,3,4,255],[1,2,3,4],[7,8,10,52],[0,1,2,15]],verbose=0)
    [[1, 2, 10, 15], [1, 8, 2, 255], [7, 1, 4, 4], [0, 3, 3, 52]]

    >>> ShiftRows([[1,13,4,55],[1,22,3,4],[7,18,10,52],[0,1,2,15]],verbose=0)
    [[1, 22, 10, 15], [1, 18, 2, 55], [7, 1, 4, 4], [0, 13, 3, 52]]
    """

    assert is_state(st)

    r = [[st[0][0], st[1][1], st[2][2], st[3][3]],
         [st[1][0], st[2][1], st[3][2], st[0][3]],
         [st[2][0], st[3][1], st[0][2], st[1][3]],
         [st[3][0], st[0][1], st[1][2], st[2][3]]]

    if verbose>=1: #tvn traces
        print 'l0: r st'
        print 'l0: ', r, st

    assert is_state(r)

    return r

def InvShiftRows(st, verbose=1):
    """
    tvn: miscs array inv
    [-r_1_3 + st_2_3 == 0, -r_0_2 + st_2_2 == 0, r_3_1 - st_2_1 == 0, -r_3_3 + st_0_3 == 0, -r_2_2 + st_0_2 == 0, -r_2_1 + st_1_1 == 0, r_0_1 - st_3_1 == 0, r_2_0 - st_2_0 == 0, r_3_0 - st_3_0 == 0, r_0_0 - st_0_0 == 0, -r_3_2 + st_1_2 == 0, r_1_1 - st_0_1 == 0, r_1_0 - st_1_0 == 0, r_2_3 - st_3_3 == 0, -r_0_3 + st_1_3 == 0, r_1_2 - st_3_2 == 0]

    """

    assert is_state(st)

    if verbose>=1: #tvn traces
        print 'l1: st'
        print 'l1: ', st

    r =  [[st[0][0], st[3][1], st[2][2], st[1][3]],
          [st[1][0], st[0][1], st[3][2], st[2][3]],
          [st[2][0], st[1][1], st[0][2], st[3][3]],
          [st[3][0], st[2][1], st[1][2], st[0][3]]]


    if verbose >= 1: #tvn traces
        print 'l0: r st'
        print 'l0: ', r, st

    assert is_state(r)
    return r


def MixColumns(st, verbose=1):
    assert is_state(st)

    r = [[myxor([mul(2,st[0][0],verbose=0), mul(3,st[0][1],verbose=0), st[0][2],                  st[0][3]                ]),
          myxor([st[0][0],                  mul(2,st[0][1],verbose=0), mul(3,st[0][2],verbose=0), st[0][3]                ]),
          myxor([st[0][0],                  st[0][1],                  mul(2,st[0][2],verbose=0), mul(3,st[0][3],verbose=0) ]),
          myxor([mul(3,st[0][0],verbose=0), st[0][1],st[0][2],         mul(2,st[0][3],verbose=0)                          ])],

         [myxor([mul(2,st[1][0],verbose=0), mul(3,st[1][1],verbose=0), st[1][2],                st[1][3]                ]),
          myxor([st[1][0],                mul(2,st[1][1],verbose=0), mul(3,st[1][2],verbose=0), st[1][3]                ]),
          myxor([st[1][0],                st[1][1],                mul(2,st[1][2],verbose=0), mul(3,st[1][3],verbose=0) ]),
          myxor([mul(3,st[1][0],verbose=0), st[1][1],                st[1][2],                mul(2,st[1][3],verbose=0) ])],

         [myxor([mul(2,st[2][0],verbose=0), mul(3,st[2][1],verbose=0), st[2][2],                st[2][3]                ]),
          myxor([st[2][0],                mul(2,st[2][1],verbose=0), mul(3,st[2][2],verbose=0), st[2][3]                ]),
          myxor([st[2][0],                st[2][1],                mul(2,st[2][2],verbose=0), mul(3,st[2][3],verbose=0) ]),
          myxor([mul(3,st[2][0],verbose=0), st[2][1],                st[2][2],                mul(2,st[2][3],verbose=0) ])],

         [myxor([mul(2,st[3][0],verbose=0), mul(3,st[3][1],verbose=0), st[3][2],                st[3][3]                ]),
          myxor([st[3][0],                mul(2,st[3][1],verbose=0), mul(3,st[3][2],verbose=0), st[3][3]                ]),
          myxor([st[3][0],                st[3][1],                mul(2,st[3][2],verbose=0), mul(3,st[3][3],verbose=0) ]),
          myxor([mul(3,st[3][0],verbose=0), st[3][1],                st[3][2],                mul(2,st[3][3],verbose=0) ])]
         ]
 
    assert is_state(r)
    
    if verbose >= 1: #tvn traces
        print 'l0: r st'
        print 'l0: ', r, st
   
    return r



def InvMixColumns(st, verbose=1):

    assert is_state(st)

    r = [
        [myxor([mul(14,st[0][0],verbose=0), mul(11,st[0][1],verbose=0), mul(13,st[0][2],verbose=0), mul( 9,st[0][3],verbose=0)]),
         myxor([mul( 9,st[0][0],verbose=0), mul(14,st[0][1],verbose=0), mul(11,st[0][2],verbose=0), mul(13,st[0][3],verbose=0)]),
         myxor([mul(13,st[0][0],verbose=0), mul( 9,st[0][1],verbose=0), mul(14,st[0][2],verbose=0), mul(11,st[0][3],verbose=0)]),
         myxor([mul(11,st[0][0],verbose=0), mul(13,st[0][1],verbose=0), mul( 9,st[0][2],verbose=0), mul(14,st[0][3],verbose=0)])],

        [myxor([mul(14,st[1][0],verbose=0), mul(11,st[1][1],verbose=0), mul(13,st[1][2],verbose=0), mul( 9,st[1][3],verbose=0)]),
         myxor([mul( 9,st[1][0],verbose=0), mul(14,st[1][1],verbose=0), mul(11,st[1][2],verbose=0), mul(13,st[1][3],verbose=0)]),
         myxor([mul(13,st[1][0],verbose=0), mul( 9,st[1][1],verbose=0), mul(14,st[1][2],verbose=0), mul(11,st[1][3],verbose=0)]),
         myxor([mul(11,st[1][0],verbose=0), mul(13,st[1][1],verbose=0), mul( 9,st[1][2],verbose=0), mul(14,st[1][3],verbose=0)])],

        [myxor([mul(14,st[2][0],verbose=0), mul(11,st[2][1],verbose=0), mul(13,st[2][2],verbose=0), mul( 9,st[2][3],verbose=0)]),
         myxor([mul( 9,st[2][0],verbose=0), mul(14,st[2][1],verbose=0), mul(11,st[2][2],verbose=0), mul(13,st[2][3],verbose=0)]),
         myxor([mul(13,st[2][0],verbose=0), mul( 9,st[2][1],verbose=0), mul(14,st[2][2],verbose=0), mul(11,st[2][3],verbose=0)]),
         myxor([mul(11,st[2][0],verbose=0), mul(13,st[2][1],verbose=0), mul( 9,st[2][2],verbose=0), mul(14,st[2][3],verbose=0)])],

        [myxor([mul(14,st[3][0],verbose=0), mul(11,st[3][1],verbose=0), mul(13,st[3][2],verbose=0), mul( 9,st[3][3],verbose=0)]),
         myxor([mul( 9,st[3][0],verbose=0), mul(14,st[3][1],verbose=0), mul(11,st[3][2],verbose=0), mul(13,st[3][3],verbose=0)]),
         myxor([mul(13,st[3][0],verbose=0), mul( 9,st[3][1],verbose=0), mul(14,st[3][2],verbose=0), mul(11,st[3][3],verbose=0)]),
         myxor([mul(11,st[3][0],verbose=0), mul(13,st[3][1],verbose=0), mul( 9,st[3][2],verbose=0), mul(14,st[3][3],verbose=0)])]
        ]

    assert is_state(r)
 
    if verbose >= 1: #tvn traces
        print 'l0: r st'
        print 'l0: ', r, st    
        
    return r

def AddRoundKey(st, rk0, rk1, rk2, rk3, verbose=1):
    """
    *nested* array
    r[i][j] = xor(st[i][j], rk[i][j])
    """

    assert is_state(st), st
    assert (is_word(rk0) and is_word(rk1) and 
            is_word(rk2) and is_word(rk3)), (rk0,rk1,rk2,rk3)
    

    if verbose >= 1:
        print 'l1: st rk0 rk1 rk2 rk3'
        print 'l1: ', st, rk0, rk1, rk2, rk3

    r = [
        [xor(st[0][0], rk0[0]), xor(st[0][1], rk0[1]), xor(st[0][2], rk0[2]), xor(st[0][3], rk0[3])],
        [xor(st[1][0], rk1[0]), xor(st[1][1], rk1[1]), xor(st[1][2], rk1[2]), xor(st[1][3], rk1[3])],
        [xor(st[2][0], rk2[0]), xor(st[2][1], rk2[1]), xor(st[2][2], rk2[2]), xor(st[2][3], rk2[3])],
        [xor(st[3][0], rk3[0]), xor(st[3][1], rk3[1]), xor(st[3][2], rk3[2]), xor(st[3][3], rk3[3])]
        ]


    if verbose >= 1:
        print 'l0: st rk0 rk1 rk2 rk3 r'
        print 'l0: ', st, rk0, rk1, rk2, rk3, r


    assert is_state(r)

    return r

def AddRoundKey_vn(st, rk, verbose=1):
    """
    Similar to AddRoundKey except using 
    rk=[rk0,..,rk3]instead of 4 individual inputs rk0,..,rk3
    
    """
    assert is_state(st)

    
    if verbose >= 1:
        print 'l1: st rk'
        print 'l1: ', st, rk

    r = [
        [xor(st[0][0], rk[0][0]), xor(st[0][1], rk[0][1]), xor(st[0][2], rk[0][2]), xor(st[0][3], rk[0][3])],
        [xor(st[1][0], rk[1][0]), xor(st[1][1], rk[1][1]), xor(st[1][2], rk[1][2]), xor(st[1][3], rk[1][3])],
        [xor(st[2][0], rk[2][0]), xor(st[2][1], rk[2][1]), xor(st[2][2], rk[2][2]), xor(st[2][3], rk[2][3])],
        [xor(st[3][0], rk[3][0]), xor(st[3][1], rk[3][1]), xor(st[3][2], rk[3][2]), xor(st[3][3], rk[3][3])]
        ]


    if verbose >= 1:
        print 'l0: st rk r'
        print 'l0: ', st, rk, r

    assert is_state(r)
    return r



def AddRoundKey_vn_simple(st,rk, verbose=1):
    """
    for debugging purpose
    """

    st = [st_[:3] for st_ in st[:3]]
    rk = [rk_[:3] for rk_ in rk[:3]]

    if verbose >= 1:
        print 'l1: st rk'
        print 'l1: ', st, rk

    r = [
        [xor(st[0][0], rk[0][0]), xor(st[0][1], rk[0][1]), xor(st[0][2], rk[0][2])],
        [xor(st[1][0], rk[1][0]), xor(st[1][1], rk[1][1]), xor(st[1][2], rk[1][2])],
        [xor(st[2][0], rk[2][0]), xor(st[2][1], rk[2][1]), xor(st[2][2], rk[2][2])]
        ]

    if verbose >= 1:
        print 'l0: st rk r'
        print 'l0: ', st, rk, r


    return r

def KeySetupEnc4(cipherKey, verbose=1):# return key_schedule
    """
    tvn: *multidim* array
    rk[i][j] = cipherKey[4*i+j]
    """

    if __debug__:
        assert is_key(cipherKey), cipherKey

    #rk = key_schedule'(others => [0, 0, 0, 0])
    rk = [[0,0,0,0]]*roundkey_index  #create an array of roundkey_index empty words
    for i in range(4):
        rk[i] = [cipherKey[4*i], cipherKey[4*i+1], cipherKey[4*i+2], cipherKey[4*i+3]]

    
    if verbose >= 1:
        print 'l1: rk cipherKey'
        print 'l1: ', rk[:6], cipherKey


    #--# assert 0 <= i and i <= 3 and
    #--#        (for all p in Integer range 0 .. i =>
    #--#          (rk(p) = [cipherKey(4*p), cipherKey(4*p+1), cipherKey(4*p+2), cipherKey(4*p+3))))


    for i in range(4,44):
        if i % 4 == 0:
            rk[i] = word_xor_xor(rk[i-4], SubWord(RotWord(rk[i-1],verbose=0),verbose=0),
                                 rcon[i/4-1],verbose=0)
        else:
            rk[i] = word_xor(rk[i-4], rk[i-1],verbose=0)


    
    # if verbose >= 1:
    #     print 'rk_else cipherKey'
    #     print [rk[i] for i in range(4,44)], cipherKey

    # assert 4 <= i and i <= 43 and
    # (for all p in Integer range 0 .. 3 =>
    #          (rk(p) = [cipherKey(4*p), cipherKey(4*p+1), cipherKey(4*p+2), cipherKey(4*p+3)))) and
    #        (for all p in Integer range 4 .. i =>
    #          ((p mod 4 = 0 and rk(p) = word_xor_xor(rk(p-4), SubWord(RotWord(rk(p-1))), rcon(p/4-1))) or
    #          (p mod 4 /= 0 and rk(p) = word_xor(rk(p-4), rk(p-1)))))


    #disj
    if verbose >= 1:
        print 'l0: rk cipherKey'
        print 'l0: ', rk, cipherKey


    assert is_key_schedule(rk)

    return rk


def KeySetupEnc6(cipherKey, verbose=1):# return key_schedule
    """
    tvn: *multidim* array
    rk[i][j] = cipherKey[4*i+j]
    """

    assert is_key(cipherKey)

    rk = [[0,0,0,0]]*roundkey_index  #create an array of roundkey_index empty words

    for i in range(6):
        rk[i]= [cipherKey[4*i], cipherKey[4*i+1], cipherKey[4*i+2], cipherKey[4*i+3]]
        # assert 0 <= i and i <= 5 and
        #        (for all p in Integer range 0 .. i =>
        #          (rk(p) = [cipherKey(4*p), cipherKey(4*p+1), cipherKey(4*p+2), cipherKey(4*p+3))))


    if verbose >= 1:
        print 'l1: rk cipherKey'
        print 'l1: ', rk, cipherKey


    for i in range(6,52):
        if (i % 6 == 0):
            rk[i] = word_xor_xor(rk[i-6], SubWord(RotWord(rk[i-1],verbose=0),verbose=0),
                                 rcon[i/6-1],verbose=0)
        else:
            rk[i] = word_xor(rk[i-6], rk[i-1],verbose=0)
        # assert 6 <= i and i <= 51 and
        #        (for all p in Integer range 0 .. 5 =>
        #          (rk(p) = [cipherKey(4*p), cipherKey(4*p+1), cipherKey(4*p+2), cipherKey(4*p+3)))) and
        #        (for all p in Integer range 6 .. i =>
        #          ((p mod 6 = 0 and rk(p) = word_xor_xor(rk(p-6), SubWord(RotWord(rk(p-1))), rcon(p/6-1))) or
        #          (p mod 6 /= 0 and rk(p) = word_xor(rk(p-6), rk(p-1)))))


    if verbose >= 1:
        print 'l0: rk cipherKey'
        print 'l0: ', rk, cipherKey

    assert is_key_schedule(rk)
    return rk


def KeySetupEnc8(cipherKey, verbose=1):# return key_schedule
    """
    tvn: *multidim* array
    rk[i][j] = cipherKey[4*i+j]
    """
    assert is_key(cipherKey)

    rk = [[0,0,0,0]]*roundkey_index  #create an array of roundkey_index empty words


    for i in range(8):
        rk[i] = [cipherKey[4*i], cipherKey[4*i+1], cipherKey[4*i+2], cipherKey[4*i+3]]

    
    if verbose >= 1:
        print 'l1: rk cipherKey'
        print 'l1: ', rk, cipherKey

        # assert 0 <= i and i <= 7 and
        #        (for all p in Integer range 0 .. i =>
        #          (rk(p) = [cipherKey(4*p), cipherKey(4*p+1), cipherKey(4*p+2), cipherKey(4*p+3))))


    for i in range(8,60):
        if (i % 8 == 0):
            rk[i] = word_xor_xor(rk[i-8], SubWord(RotWord(rk[i-1],verbose=0),verbose=0),
                                 rcon[i/8-1],verbose=0)
        elif (i % 4 == 0):
            rk[i] = word_xor(rk[i-8], SubWord(rk[i-1],verbose=0),verbose=0)
        else:
            rk[i] = word_xor(rk[i-8], rk[i-1],verbose=0)

        # assert 8 <= i and i <= 59 and
        #        (for all p in Integer range 0 .. 7 =>
        #          (rk(p) = [cipherKey(4*p), cipherKey(4*p+1), cipherKey(4*p+2), cipherKey(4*p+3)))) and
        #        (for all p in Integer range 8 .. i =>
        #          ((p % 8 = 0 and                  rk(p) = word_xor_xor(rk(p-8), SubWord(RotWord(rk(p-1))), rcon(p/8-1))) or
        #          (p % 8 /= 0 and p % 4 = 0 and  rk(p) = word_xor(rk(p-8), SubWord(rk(p-1)))) or
        #          (p % 8 /= 0 and p % 4 /= 0 and rk(p) = word_xor(rk(p-8), rk(p-1)))))

    if verbose >= 1:
        print 'l0: rk cipherKey'
        print 'l0: ', rk, cipherKey

    assert is_key_schedule(rk)
    return rk


def KeySetupEnc(cipherKey, Nk, verbose=1):
    assert is_key(cipherKey)
    assert Nk in nk_vals

    rk = [[0,0,0,0]]*roundkey_index  #create an array of roundkey_index empty words
    if (Nk == 4):
        rk = KeySetupEnc4(cipherKey,verbose=0)
    if (Nk == 6):
        rk = KeySetupEnc6(cipherKey,verbose=0)
    if (Nk == 8):
        rk = KeySetupEnc8(cipherKey,verbose=0)
        
    assert is_key_schedule(rk)

    if verbose >= 1:
        print 'l0: rk cipherKey'
        print 'l0: ', rk, cipherKey
        
    return rk



def KeyScheduleMod1__(W, Nr,verbose=1):
    assert is_key_schedule(W)
    rk = deepcopy(W)
    for i in range(4*(Nr+1)):
        #print i, 4*(Nr-i//4)+i%4
        #print i, (4*Nr- 4*(i//4))+i%4
        rk[i] = W[4*(Nr-i//4)+i%4]

        #rk[i] = W[add(mul4(sub(Nr,div4(i))),mod4(i))]

        # assert 0 <= i and i <= Nr and Nr = Nr% and
        #        (for all p in Integer range 0 .. i =>
        #          (rk(4*p  ) = W(4*(Nr-p)  ) and
        #           rk(4*p+1) = W(4*(Nr-p)+1) and
        #           rk(4*p+2) = W(4*(Nr-p)+2) and
        #           rk(4*p+3) = W(4*(Nr-p)+3))) and
        #        (for all j in Integer range 4*(Nr+1) .. 4*(MAXNR+1)-1 =>
        #          (rk(j) = W(j)))

    if verbose >= 1:
        # vs1 = ['RK_%d_%d'%(i,j) for i in range(len(rk)) for j in range(len(rk[0]))]
        # ns1 = [rk[i][j]  for i in range(len(rk)) for j in range(len(rk[0]))]

        # vs2 = ['W_%d_%d'%(i,j) for i in range(len(W)) for j in range(len(W[0]))]
        # ns2 = [W[i][j]  for i in range(len(W)) for j in range(len(W[0]))]


        # print ' '.join(vs1+vs2)
        # print ' '.join(map(str,ns1+ns2))
        
        print 'l0: rk, W Nr'
        print 'l0: ', rk, W, [Nr]

    assert is_key_schedule(rk)
    return rk


def KeyScheduleMod1_(W, Nr,verbose=1):
    assert is_key_schedule(W)
    rk = deepcopy(W)
    for i in range(Nr+1):
        for j in range(len(rk[0])):
            rk[4*i+j] =W[4*(Nr-i)+j]
        # assert 0 <= i and i <= Nr and Nr = Nr% and
        #        (for all p in Integer range 0 .. i =>
        #          (rk(4*p  ) = W(4*(Nr-p)  ) and
        #           rk(4*p+1) = W(4*(Nr-p)+1) and
        #           rk(4*p+2) = W(4*(Nr-p)+2) and
        #           rk(4*p+3) = W(4*(Nr-p)+3))) and
        #        (for all j in Integer range 4*(Nr+1) .. 4*(MAXNR+1)-1 =>
        #          (rk(j) = W(j)))
# 
#     if verbose >= 1:
#         vs1 = ['RK_%d_%d'%(i,j) for i in range(len(rk)) for j in range(len(rk[0]))]
#         ns1 = [rk[i][j]  for i in range(len(rk)) for j in range(len(rk[0]))]
# 
#         vs2 = ['W_%d_%d'%(i,j) for i in range(len(W)) for j in range(len(W[0]))]
#         ns2 = [W[i][j]  for i in range(len(W)) for j in range(len(W[0]))]
# 
# 
#         print 'l0: ', ' '.join(vs1+vs2)
#         print 'l0: ', ' '.join(map(str,ns1+ns2))

    assert is_key_schedule(rk)
    return rk

def KeyScheduleMod1(W, Nr, verbose=1):
    assert is_key_schedule(W)
    assert Nr in nr_vals
    
    rk = deepcopy(W)
    for i in range(Nr+1):
        rk[4*i] =W[4*(Nr-i)]
        rk[4*i+1] =W[4*(Nr-i)+1]
        rk[4*i+2] =W[4*(Nr-i)+2]
        rk[4*i+3] =W[4*(Nr-i)+3]
        # assert 0 <= i and i <= Nr and Nr = Nr% and
        #        (for all p in Integer range 0 .. i =>
        #          (rk(4*p  ) = W(4*(Nr-p)  ) and
        #           rk(4*p+1) = W(4*(Nr-p)+1) and
        #           rk(4*p+2) = W(4*(Nr-p)+2) and
        #           rk(4*p+3) = W(4*(Nr-p)+3))) and
        #        (for all j in Integer range 4*(Nr+1) .. 4*(MAXNR+1)-1 =>
        #          (rk(j) = W(j)))

#     if verbose >= 1:
#         vs1 = ['RK_%d_%d'%(i,j) for i in range(len(rk)) for j in range(len(rk[0]))]
#         ns1 = [rk[i][j]  for i in range(len(rk)) for j in range(len(rk[0]))]
# 
#         vs2 = ['W_%d_%d'%(i,j) for i in range(len(W)) for j in range(len(W[0]))]
#         ns2 = [W[i][j]  for i in range(len(W)) for j in range(len(W[0]))]
# 
# 
#         print 'l0: ', ' '.join(vs1+vs2)
#         print 'l0: ', ' '.join(map(str,ns1+ns2))


    if verbose >= 1:
        print 'l0: W rk'
        print 'l0: ', W, rk

    assert is_key_schedule(rk)
    return rk


def KeyScheduleMod2(W, Nr, verbose=1):# return key_schedule
    assert is_key_schedule(W)
    assert Nr in nr_vals
    
    rk = deepcopy(W)
    for i in range(1,Nr):
        st = [W[4*i], W[4*i+1], W[4*i+2], W[4*i+3]]
        assert is_state(st)
        st = InvMixColumns(st,verbose=0)
        rk[4*i]   = st[0]
        rk[4*i+1] = st[1]
        rk[4*i+2] = st[2]
        rk[4*i+3] = st[3]
        # assert 1 <= i and i <= Nr-1 and Nr = Nr% and
        #        (for all p in Integer range 1 .. i =>
        #          (rk(4*p  ) = InvMixColumns([W(4*p), W(4*p+1), W(4*p+2), W(4*p+3)))(0) and
        #           rk(4*p+1) = InvMixColumns([W(4*p), W(4*p+1), W(4*p+2), W(4*p+3)))(1) and
        #           rk(4*p+2) = InvMixColumns([W(4*p), W(4*p+1), W(4*p+2), W(4*p+3)))(2) and
        #           rk(4*p+3) = InvMixColumns([W(4*p), W(4*p+1), W(4*p+2), W(4*p+3)))(3))) and
        #        (for all j in Integer range 0 .. 3 =>
        #          (rk(j) = W(j))) and
        #        (for all j in Integer range 4*Nr .. 4*(MAXNR+1)-1 =>
        #          (rk(j) = W(j)))

    assert is_key_schedule(rk)

    if verbose >= 1:
        print 'l0: W rk'
        print 'l0: ', W, rk
        
    return rk


def KeySetupDec(cipherKey, Nk, verbose=1): # return key_schedule
    assert is_key(cipherKey)
    assert Nk in nk_vals

    rk =  KeyScheduleMod2(KeyScheduleMod1(KeySetupEnc(cipherKey, Nk,verbose=0), Nk + 6,verbose=0), Nk + 6,verbose=0)
    assert is_key_schedule(rk)
    
    if verbose >= 1:
        print 'l0: rk cipherKey'
        print 'l0: ', rk, cipherKey
        
    return rk


def AesKeySetupEnc(cipherKey, keyBits, verbose=1):

    assert is_key(cipherKey)
    assert keyBits in keybit_vals

    Nr = keyBits/32 + 6
    rk = KeySetupEnc(cipherKey, keyBits/32,verbose=0)

    if verbose >= 1:
        print 'l0: cipherKey rk'
        print 'l0: ', cipherKey, rk

    assert is_key_schedule(rk)
    assert Nr in nr_vals
    
    return Nr,rk

def AesKeySetupDec(cipherKey, keyBits, verbose=1):

    assert is_key(cipherKey)
    assert keyBits in keybit_vals

    Nr = keyBits/32 + 6
    rk = KeySetupDec(cipherKey, keyBits/32,verbose=0)

    if verbose >= 1: #tvntraces
        print 'l0: cipherKey rk'
        print 'l0: ', cipherKey, rk

    assert is_key_schedule(rk)
    assert Nr in nr_vals

    return Nr,rk


def AesEncrypt(rk,Nr,pt,verbose=1):
    assert is_key_schedule(rk)
    assert is_block(pt)
    assert Nr in nr_vals

    st = AddRoundKey(Block2State(pt,verbose=0), 
                     rk[0], rk[1], rk[2], rk[3], verbose=0)
    # assert st = encrypt_round(Block2State(pt), rk, Nr, 0)

    for r in range(1,Nr):

        sb = SubBytes(st,verbose=0)
        sr = ShiftRows(sb,verbose=0)

        st = AddRoundKey(MixColumns(sr,verbose=0), 
                         rk[4*r], rk[4*r+1], rk[4*r+2], rk[4*r+3],
                         verbose=0)


    st = AddRoundKey(ShiftRows(SubBytes(st,verbose=0),verbose=0), rk[4*Nr], rk[4*Nr+1], rk[4*Nr+2], rk[4*Nr+3],verbose=0)
    # assert st = encrypt_round(Block2State(pt), rk, Nr, Nr)
    # assert 1 <= r and r <= Nr-1 and Nr = Nr% and
    #        st = encrypt_round(Block2State(pt), rk, Nr, r)

    

    ct = State2Block(st,verbose=0)

    if verbose >= 1:
        print 'l0: rk ct st pt'
        print 'l0: ', rk, ct, st, pt

    assert is_block(ct)
    return ct

def AesDecrypt(rk, Nr, ct,verbose=1):
    assert is_key_schedule(rk)
    assert is_block(ct)
    assert Nr in nr_vals

    st = AddRoundKey(Block2State(ct,verbose=0), 
                     rk[0], rk[1], rk[2], rk[3],verbose=0)
    # assert st = decrypt_round(Block2State(ct), rk, Nr, 0)


    for r in range(1,Nr):
        st =AddRoundKey(InvMixColumns(InvShiftRows(InvSubBytes(st,verbose=0),verbose=0),verbose=0), rk[4*r], rk[4*r+1], rk[4*r+2], rk[4*r+3],verbose=0)

    st = AddRoundKey(InvShiftRows(InvSubBytes(st,verbose=0),verbose=0), 
                     rk[4*Nr], rk[4*Nr+1], rk[4*Nr+2], rk[4*Nr+3],verbose=0)
    # assert st = decrypt_round(Block2State(ct), rk, Nr, Nr)
    
    # assert 1 <= r and r <= Nr-1 and Nr = Nr% and
    #        st = decrypt_round(Block2State(ct), rk, Nr, r)    

    pt = State2Block(st,verbose=0)
    
    if verbose >= 1:
        print 'l0: rk ct st pt'
        print 'l0: ', rk, ct, st, pt

    assert is_block(pt)
    return pt



def Driver(verbose=1):
    """
    Examples for using the AES functions
    """
    
    print("AES mul")
    print mul(8,3,verbose)
    print mul(50,50,verbose)
    print mul(8,0,verbose)

    print("AES word_xor")
    print word_xor([0,1,9,1],[0,0,2,245],verbose)
    print word_xor([0,0,99,1],[100,0,2,145],verbose)

    print("AES word_xor_xor")
    print word_xor_xor([0,1,0,0],[1,0,1,1],[1,1,1,1],verbose)
    print word_xor_xor([0,1,0,89],[124,0,1,1],[0,1,241,1],verbose)

    print 'Subword'
    print SubWord([1,1,1,255],verbose)
    print SubWord([231,189,0,255],verbose)
    print SubWord([0,0,7,75],verbose)

    print 'RodWord'
    print RotWord([1,3,4,255],verbose);
    print RotWord([89,0,43,24],verbose);
    print RotWord([41,38,67,8],verbose);

    print 'Block2State'
    print Block2State([1,3,4,255,
                       1,2,3,4,
                       7,8,10,52,
                       0,1,2,15],verbose)

    print("AES State2Block");
    print State2Block([
            [1,3,4,255],
            [1,2,3,4],
            [7,8,10,52],
            [0,1,2,15]],verbose)



    print("AES SubBytes")
    print SubBytes([
            [1,3,4,255],
            [1,2,3,4],
            [7,8,10,52],
            [0,1,2,15]],verbose)



    print("AES InvSubBytes")
    print InvSubBytes([
            [1,3,4,255],
            [1,2,3,4],
            [7,8,10,52],
            [0,1,2,15]],verbose)


    print InvSubBytes([
            [0,13,89,132],
            [12,82,10,97],
            [40,88,42,80],
            [0,111,102,105]],verbose)


    print("AES ShiftRows")
    print ShiftRows([[1,3,4,255],[1,2,3,4],[7,8,10,52],[0,1,2,15]],verbose)


    print("AES InvShiftRows")
    print InvShiftRows([
            [1,3,4,255],
            [1,2,3,4],
            [7,8,10,52],
            [0,1,2,15]],verbose)



    print("AES MixColumns")
    print MixColumns([[1,3,4,255],[1,2,3,4],[7,8,10,52],[0,1,2,15]],verbose)
    #result = [[252, 244, 16, 225], [3, 4, 9, 10], [40, 61, 71, 99], [14, 11, 20, 29]]



    print("AES AddRoundKey")
    print AddRoundKey([[1,3,4,255],[1,2,3,4],[7,8,10,52],[0,1,2,15]],
                      [1,3,4,255],
                      [1,3,4,255],
                      [1,3,4,255],
                      [1,3,4,255],verbose)


    Key1 = [1,3,4,255,1,2,3,4,7,8,10,52,0,1,2,15,  
            1,3,4,255,1,2,3,4,7,8,10,52,0,1,2,15]


    Key2 = [89,32,4,90,1,213,16,4,34,8,80,13,0,1,0,132,
            82,28,76,21,132,48,89,123,90,80,12,12,10,8,40,65]


    Key3= [221, 35, 247, 82, 247, 246, 49, 41, 172, 47, 146, 208, 70, 99, 
           153, 38, 249, 200, 103, 242, 175, 74, 234, 164, 202, 222, 2, 178, 89, 64, 139, 160]

    print("AES KeySetup4")

    print(KeySetupEnc4(Key1,verbose))
    print(KeySetupEnc4(Key2,verbose))

    print("AES KeySetup6")

    print(KeySetupEnc6(Key1,verbose))
    print(KeySetupEnc6(Key2,verbose))


    print("AES KeySetup8")

    print(KeySetupEnc8(Key1,verbose))
    print(KeySetupEnc8(Key2,verbose))


    print("AES KeySetupEnc")

    print(KeySetupEnc(Key1,8,verbose)) #4,6, or 8
    print(KeySetupEnc(Key2,4,verbose)) #4,6, or 8

    # ----------
    print("AES KeyScheduleMod1")
 
    print KeyScheduleMod1(KeySetupEnc(Key1,4,verbose),10,verbose) # 10, 12, 14
    print KeyScheduleMod1(KeySetupEnc(Key2,6,verbose),14,verbose) # 10, 12, 14
 
 
 
    print("AES KeyScheduleMod2")
 
    print(KeyScheduleMod1(KeySetupEnc(Key1,6,verbose),14,verbose)) # 10, 12, 14
    print(KeyScheduleMod1(KeySetupEnc(Key2,8,verbose),12,verbose)) # 10, 12, 14


    print("AES KeySetupDec")
 
    print(KeySetupDec(Key1,8,verbose)) #4,6,8
    print(KeySetupDec(Key2,4,verbose)) #4,6,8



    print("AES aesKeySetupEnc")
 
    Nr,Rk = AesKeySetupEnc(Key1,#--cipherKey
                           192, #--keyBits 128,192, 256
                           verbose)
 
    print(Rk)
    print(Nr)
 
 
    Nr,Rk = AesKeySetupEnc(Key2,#--cipherKey
                           128, #--keyBits 128,192, 256
                           verbose)
 
    print(Rk)
    print(Nr)
 
 
 
    #-------
    print("AES aesKeySetupDec")
 
    Nr, Rk = AesKeySetupDec(Key1,#--cipherKey
                            192, #--keyBits 128,192, 256
                            verbose)
 
    print(Rk)
    print(Nr)
 
    Nr, Rk = AesKeySetupDec(Key2,#--cipherKey
                            256, #--keyBits 128,192, 256
                            verbose)
 
    print(Rk)
    print(Nr)
 
 
    #-------
    print("AES AesEncrypt 1")
 
    Rk = [[0,0,0,0]]*roundkey_index
    Nr = 14
    Block1 = [255,0,0,0, 1,0,0,0, 0,0,0,0, 0,0,0,1]
    Block2 = AesEncrypt(Rk,Nr,Block1,verbose)
    print(Block2)
 
    print("AES AesDecrypt 1")
    Block1_ = AesDecrypt(Rk,Nr,Block2,verbose)
    print(Block1_)
    assert Block1 == Block1_
 
 
    print("AES AesEncrypt 1 - Cust")
    Rk = [[78,15,93,2]]*roundkey_index
    Nr = 14
    Block1 = [255,0,0,0, 1,0,0,0, 0,0,0,0, 0,0,0,1]
    Block2 = AesEncrypt(Rk,Nr,Block1,verbose)
    print(Block2)
 
 
    print("AES AesDecrypt 1 - Cust")
    Block1_ = AesDecrypt(Rk,Nr,Block2,verbose)
    print(Block1_)
    #assert Block1 == Block1_ #TODO, should these 2 be the same ?
 
 
    ##############
 
    print("AES AesEncrypt 2")
 
    Rk = [[0,0,0,0]]*roundkey_index
    Nr = 10
    Block1 = [255,0,28,0, 1,0,0,0, 0,0,0,92, 5,0,11,7]
    Block2 = AesEncrypt(Rk,Nr,Block1,verbose)
    print(Block2)
 
 
    print("AES AesDecrypt 2")
    Block1_ = AesDecrypt(Rk,Nr,Block2,verbose)
    print(Block1_)
    assert Block1 == Block1_
 
 
    print("AES AesEncrypt 2 - Cust")
 
    Rk = [[78,15,93,2]]*roundkey_index
    Nr = 10
    Block1 = [255,0,28,0, 1,0,0,0, 0,0,0,92, 5,0,11,7]
    Block2 = AesEncrypt(Rk,Nr,Block1,verbose)
    print(Block2)
 
 
 
    print("AES AesDecrypt 2 - Cust")
    Block1 = AesDecrypt(Rk,Nr,Block2,verbose)
    print(Block1)
 
 
    #################
 
 
    print("AES AesEncrypt 3")
 
    Rk = [[0,0,0,0]]*roundkey_index
    Nr = 10
    Block1 = [55,0,28,15, 199,0,254,45, 0,89,98,92, 52,130,171,78]
    Block2 = AesEncrypt(Rk,Nr,Block1,verbose)
    print(Block2)
 
 
 
    print("AES AesDecrypt 3")
    Block1_ = AesDecrypt(Rk,Nr,Block2,verbose)
    print(Block1_)
    assert Block1 == Block1_

 
 
 
    print("AES AesEncrypt 3 - Cust")
 
    Rk = [[78,15,93,2]]*roundkey_index
    Nr = 10
    Block1 = [255,0,28,15, 199,0,254,45, 0,89,0,92, 52,130,171,78]
    Block2 = AesEncrypt(Rk,Nr,Block1,verbose)
    print(Block2)
 
 
 
    print("AES AesDecrypt 3 - Cust")
    Block1 = AesDecrypt(Rk,Nr,Block2,verbose)
    print(Block1)

    """
    AES AesEncrypt
    [137, 68, 165, 70, 4, 134, 2, 246, 190, 149, 62, 139, 151, 51, 162, 29]
    AES AesDecrypt
    [255, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    AES AesEncrypt
    [74, 214, 59, 245, 196, 180, 42, 157, 33, 179, 23, 176, 232, 101, 117, 87]
    AES AesDecrypt
    [255, 0, 28, 0, 1, 0, 0, 0, 0, 0, 0, 92, 5, 0, 11, 7]
    """

def aes_gen_tcs(fn, reps=300, mseed=0):
    """
    Generate random test cases to obtain traces
    """
    
    from random import seed, randint, choice

    seed(mseed)
    print '# Setting seed to', mseed
    
    #0 .. 255
    gen_v     = lambda siz: [randint(0, byte-1) for _ in range(siz)] 

    gen_key   = lambda: gen_v(key_index)
    gen_block = lambda: gen_v(byte_index)
    gen_word  = lambda: gen_v(word_index)
    gen_state = lambda: [gen_v(word_index) for _ in range(state_index)]
    gen_key_schedule = lambda : [gen_v(word_index) for _ in range(roundkey_index)]

    gen_nk = lambda: choice(nk_vals)
    gen_nr = lambda: choice(nr_vals)
    gen_keybit = lambda: choice(keybit_vals)

    run = lambda f: [f() for _ in range(reps)]
    

    if fn == 'mul':
        _ =  run(lambda: mul(randint(1,255),randint(1,255)))

    elif fn == 'word_xor':
        _ =  run(lambda: word_xor(gen_word(), gen_word()))

    elif fn == 'word_xor_xor':
        _ =  run(lambda: word_xor_xor(gen_word(), gen_word(), gen_word()))

    elif fn == 'SubWord':
        _ =  run(lambda: SubWord(gen_word()))
        
    elif fn == 'RotWord':
        _ =  run(lambda: RotWord(gen_word()))
        
    elif fn == 'Block2State':
        _ =  run(lambda: Block2State(gen_block()))

    elif fn == 'State2Block':
        _ =  run(lambda: State2Block(gen_state()))

    elif fn == 'SubBytes':
        _ =  run(lambda: SubBytes(gen_state()))

    elif fn == 'InvSubBytes':
        _ =  run(lambda: InvSubBytes(gen_state()))
        
    elif fn == 'ShiftRows':
        _ =  run(lambda: ShiftRows(gen_state()))

    elif fn == 'InvShiftRows':
        _ =  run(lambda: InvShiftRows(gen_state()))
             
    elif fn == 'MixColumns':
        _ = run(lambda: MixColumns(gen_state()))
 
    elif fn == 'InvMixColumns':
        _ = run(lambda: InvMixColumns(gen_state()))

    elif fn == 'addroundkey':
        _ = run(lambda: AddRoundKey(gen_state(),
                                    gen_word(),gen_word(),gen_word(),gen_word()))

    elif fn == 'addroundkey_vn':
        _ = run(lambda: AddRoundKey_vn(gen_state(),
                               [gen_word(),gen_word(),gen_word(),gen_word()]))

#     elif fn == 'addroundkey_vn_simple':
#         myargs = [(gen_state(),[gen_word(),gen_word(),gen_word(),gen_word()])
#                   for _ in range(reps)]
#         _ =  [AddRoundKey_vn_simple(*myarg) for myarg in myargs]

    elif fn == 'KeySetupEnc4':
        _ =  run(lambda: KeySetupEnc4(gen_key()))

    elif fn == 'KeySetupEnc6':
        _ =  run(lambda: KeySetupEnc6(gen_key()))

    elif fn == 'KeySetupEnc8':
        _ = run(lambda: KeySetupEnc8(gen_key()))

    elif fn == 'KeySetupEnc':
        _ =  run(lambda: KeySetupEnc(gen_key(), gen_nk()))
        
    elif fn == 'KeyScheduleMod1':
        _ = run(lambda: KeyScheduleMod1(gen_key_schedule(), gen_nr()))

    elif fn == 'KeyScheduleMod2':
        _ = run(lambda: KeyScheduleMod2(gen_key_schedule(), gen_nr()))

    elif fn == 'KeySetupDec':
        _ = run(lambda: KeySetupDec(gen_key(),gen_nk()))
                    

    elif fn == 'AesKeySetupEnc':
        _ = run(lambda: AesKeySetupEnc(gen_key(), gen_keybit()))

    elif fn == 'AesKeySetupDec':
        _ = run(lambda: AesKeySetupDec(gen_key(),gen_keybit()))


    elif fn == 'AesEncrypt':
        _ = run(lambda: AesEncrypt(gen_key_schedule(),gen_nr(),gen_block()))
                   
    
    elif fn == 'AesDecrypt':
        _ = run(lambda: AesDecrypt(gen_key_schedule(),gen_nr(),gen_block()))

    else:
        print 'cannot recognize fn: ', fn
        
def gen_tcs(reps=300, mseed=0):
    funnames = ['mul', 'word_xor', 'word_xor_xor', 'SubWord', 'RotWord', 'Block2State', 'State2Block',
                'SubBytes', 'InvSubBytes', 'ShiftRows', 'InvShiftRows', 'MixColumns', 'InvMixColumns',
                'addroundkey', 'addroundkey_vn', 'KeySetupEnc4', 'KeySetupEnc6', 'KeySetupEnc8', 'KeySetupEnc',
                'KeyScheduleMod1', 'KeyScheduleMod2', 'KeySetupDec', 'AesKeySetupEnc', 'AesKeySetupDec',
                'AesEncrypt', 'AesDecrypt']
    
    for f in funnames:
        print '#traces for {}'.format(f)
        aes_gen_tcs(f,reps=reps,mseed=mseed)
        print '\n'*3
        


# if __name__ == "__main__":
#     import argparse
#     aparser = argparse.ArgumentParser()
#  
#     aparser.add_argument("funname", help="funname")
#  
#     aparser.add_argument("-r", "--reps",
#                          type=int,default=100,
#                          help="number of repetitions")
#     aparser.add_argument("-vr", "--v_range",
#                          type=int,default=255,
#                          help="number range")
#     aparser.add_argument("-s", "--mseed",
#                          help="seed",default=0)
#  
#     args = aparser.parse_args()
#     aes_gen_tcs(args.funname,
#                 reps = args.reps,
#                 v_range = args.v_range,
#                 mseed = args.mseed)




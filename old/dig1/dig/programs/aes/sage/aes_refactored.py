from sage.all import *

from aes_common import xor, myxor, myand
from aes_common import MAXKC, MAXNR, byte, is_byte, byte_index, is_block, key_index, is_key, roundkey_index
"""
based on the ADA _annotated/refactored_ implementation
"""



def xor_xor(x,y,z, verbose=1):
    return xor(xor(x,y),z)



word_index = 4  #0..3,   
is_word = lambda w: len(w) == word_index and all(is_byte(b) for b in w)
is_byte_table = lambda t: len(t) == byte and all(is_byte(b) for b in t)
is_word_table = lambda t: len(t) == byte and all(is_word(w) for w in t)

state_index = 4 #0..3
is_state = lambda s: len(s) == state_index and all(is_word(w) for w in s)


rcon_index = 10
is_rcon_array = lambda arr: (len(arr) == rcon_index and
                             all(is_word(w) for w in arr))

is_key_schedule = lambda ks: (len(ks)== roundkey_index and
                              all(is_word(w) for w in ks))

####

Logtable = map(Integer,[  #256 
        0,   0,  25,   1,  50,   2,  26, 198,  75, 199,  27, 104,  51, 238, 223,   3,
        100,   4, 224,  14,  52, 141, 129, 239,  76, 113,   8, 200, 248, 105,  28, 193,
        125, 194,  29, 181, 249, 185,  39, 106,  77, 228, 166, 114, 154, 201,   9, 120,
        101,  47, 138,   5,  33,  15, 225,  36,  18, 240, 130,  69,  53, 147, 218, 142,
        150, 143, 219, 189,  54, 208, 206, 148,  19,  92, 210, 241,  64,  70, 131,  56,
        102, 221, 253,  48, 191,   6, 139,  98, 179,  37, 226, 152,  34, 136, 145,  16,
        126, 110,  72, 195, 163, 182,  30,  66,  58, 107,  40,  84, 250, 133,  61, 186,
        43, 121,  10,  21, 155, 159,  94, 202,  78, 212, 172, 229, 243, 115, 167,  87,
        175,  88, 168,  80, 244, 234, 214, 116,  79, 174, 233, 213, 231, 230, 173, 232,
        44, 215, 117, 122, 235,  22,  11, 245,  89, 203,  95, 176, 156, 169,  81, 160,
        127,  12, 246, 111,  23, 196,  73, 236, 216,  67,  31,  45, 164, 118, 123, 183,
        204, 187,  62,  90, 251,  96, 177, 134,  59,  82, 161, 108, 170,  85,  41, 157,
        151, 178, 135, 144,  97, 190, 220, 252, 188, 149, 207, 205,  55,  63,  91, 209,
        83,  57, 132,  60,  65, 162, 109,  71,  20,  42, 158,  93,  86, 242, 211, 171,
        68,  17, 146, 217,  35,  32,  46, 137, 180, 124, 184,  38, 119, 153, 227, 165,
        103,  74, 237, 222, 197,  49, 254,  24,  13,  99, 140, 128, 192, 247, 112,   7
        ])
assert is_byte_table(Logtable)

Alogtable = map(Integer,[ 
        1,   3,   5,  15,  17,  51,  85, 255,  26,  46, 114, 150, 161, 248,  19,  53,
        95, 225,  56,  72, 216, 115, 149, 164, 247,   2,   6,  10,  30,  34, 102, 170,
        229,  52,  92, 228,  55,  89, 235,  38, 106, 190, 217, 112, 144, 171, 230,  49,
        83, 245,   4,  12,  20,  60,  68, 204,  79, 209, 104, 184, 211, 110, 178, 205,
        76, 212, 103, 169, 224,  59,  77, 215,  98, 166, 241,   8,  24,  40, 120, 136,
        131, 158, 185, 208, 107, 189, 220, 127, 129, 152, 179, 206,  73, 219, 118, 154,
        181, 196,  87, 249,  16,  48,  80, 240,  11,  29,  39, 105, 187, 214,  97, 163,
        254,  25,  43, 125, 135, 146, 173, 236,  47, 113, 147, 174, 233,  32,  96, 160,
        251,  22,  58,  78, 210, 109, 183, 194,  93, 231,  50,  86, 250,  21,  63,  65,
        195,  94, 226,  61,  71, 201,  64, 192,  91, 237,  44, 116, 156, 191, 218, 117,
        159, 186, 213, 100, 172, 239,  42, 126, 130, 157, 188, 223, 122, 142, 137, 128,
        155, 182, 193,  88, 232,  35, 101, 175, 234,  37, 111, 177, 200,  67, 197,  84,
        252,  31,  33,  99, 165, 244,   7,   9,  27,  45, 119, 153, 176, 203,  70, 202,
        69, 207,  74, 222, 121, 139, 134, 145, 168, 227,  62,  66, 198,  81, 243,  14,
        18,  54,  90, 238,  41, 123, 141, 140, 143, 138, 133, 148, 167, 242,  13,  23,
        57,  75, 221, 124, 132, 151, 162, 253,  28,  36, 108, 180, 199,  82, 246,   1
        ])

assert is_byte_table(Alogtable)

S = map(Integer,[
        99, 124, 119, 123, 242, 107, 111, 197,  48,   1, 103,  43, 254, 215, 171, 118,
        202, 130, 201, 125, 250,  89,  71, 240, 173, 212, 162, 175, 156, 164, 114, 192,
        183, 253, 147,  38,  54,  63, 247, 204,  52, 165, 229, 241, 113, 216,  49,  21,
        4, 199,  35, 195,  24, 150,   5, 154,   7,  18, 128, 226, 235,  39, 178, 117,
        9, 131,  44,  26,  27, 110,  90, 160,  82,  59, 214, 179,  41, 227,  47, 132,
        83, 209,   0, 237,  32, 252, 177,  91, 106, 203, 190,  57,  74,  76,  88, 207,
        208, 239, 170, 251,  67,  77,  51, 133,  69, 249,   2, 127,  80,  60, 159, 168,
        81, 163,  64, 143, 146, 157,  56, 245, 188, 182, 218,  33,  16, 255, 243, 210,
        205,  12,  19, 236,  95, 151,  68,  23, 196, 167, 126,  61, 100,  93,  25, 115,
        96, 129,  79, 220,  34,  42, 144, 136,  70, 238, 184,  20, 222,  94,  11, 219,
        224,  50,  58,  10,  73,   6,  36,  92, 194, 211, 172,  98, 145, 149, 228, 121,
        231, 200,  55, 109, 141, 213,  78, 169, 108,  86, 244, 234, 101, 122, 174,   8,
        186, 120,  37,  46,  28, 166, 180, 198, 232, 221, 116,  31,  75, 189, 139, 138,
        112,  62, 181, 102,  72,   3, 246,  14,  97,  53,  87, 185, 134, 193,  29, 158,
        225, 248, 152,  17, 105, 217, 142, 148, 155,  30, 135, 233, 206,  85,  40, 223,
        140, 161, 137,  13, 191, 230,  66, 104,  65, 153,  45,  15, 176,  84, 187,  22
        ])

assert is_byte_table(S)

Si = map(Integer,[
        82,   9, 106, 213,  48,  54, 165,  56, 191,  64, 163, 158, 129, 243, 215, 251,
        124, 227,  57, 130, 155,  47, 255, 135,  52, 142,  67,  68, 196, 222, 233, 203,
        84, 123, 148,  50, 166, 194,  35,  61, 238,  76, 149,  11,  66, 250, 195,  78,
        8,  46, 161, 102,  40, 217,  36, 178, 118,  91, 162,  73, 109, 139, 209,  37,
        114, 248, 246, 100, 134, 104, 152,  22, 212, 164,  92, 204,  93, 101, 182, 146,
        108, 112,  72,  80, 253, 237, 185, 218,  94,  21,  70,  87, 167, 141, 157, 132,
        144, 216, 171,   0, 140, 188, 211,  10, 247, 228,  88,   5, 184, 179,  69,   6,
        208,  44,  30, 143, 202,  63,  15,   2, 193, 175, 189,   3,   1,  19, 138, 107,
        58, 145,  17,  65,  79, 103, 220, 234, 151, 242, 207, 206, 240, 180, 230, 115,
        150, 172, 116,  34, 231, 173,  53, 133, 226, 249,  55, 232,  28, 117, 223, 110,
        71, 241,  26, 113,  29,  41, 197, 137, 111, 183,  98,  14, 170,  24, 190,  27,
        252,  86,  62,  75, 198, 210, 121,  32, 154, 219, 192, 254, 120, 205,  90, 244,
        31, 221, 168,  51, 136,   7, 199,  49, 177,  18,  16,  89,  39, 128, 236,  95,
        96,  81, 127, 169,  25, 181,  74,  13,  45, 229, 122, 159, 147, 201, 156, 239,
        160, 224,  59,  77, 174,  42, 245, 176, 200, 235, 187,  60, 131,  83, 153,  97,
        23,  43,   4, 126, 186, 119, 214,  38, 225, 105,  20,  99,  85,  33,  12, 125
        ])

assert is_byte_table(Si)



rcon = map(lambda a: map(Integer,a),[
        [1,0,0,0],   # [16#01#,16#00#,16#00#,16#00#],        
        [2,0,0,0],   # [16#02#,16#00#,16#00#,16#00#],       
        [4,0,0,0],   # [16#04#,16#00#,16#00#,16#00#],      
        [8,0,0,0],   # [16#08#,16#00#,16#00#,16#00#],     
        [16,0,0,0],  # [16#10#,16#00#,16#00#,16#00#],    
        [32,0,0,0],  # [16#20#,16#00#,16#00#,16#00#],   
        [64,0,0,0],  # [16#40#,16#00#,16#00#,16#00#],  
        [128,0,0,0], # [16#80#,16#00#,16#00#,16#00#], 
        [27,0,0,0],  # [16#1B#,16#00#,16#00#,16#00#],
        [54,0,0,0]   # [16#36#,16#00#,16#00#,16#00#]
        ])

assert is_rcon_array(rcon)


### Functions

def mul(a,b ,verbose=1):
    """
    sage: mul(5,3,verbose=0)
    15
    sage: mul(5,0,verbose=0)
    0
    sage: mul(255,7,verbose=0)
    203
    sage: mul(7,255,verbose=0)
    203
    sage: mul(87,215,verbose=0)
    157
    sage: mul(187,153,verbose=0)
    79

    """


    assert is_byte(a) and is_byte(b)

    if a != 0 and b != 0:
        r =  Alogtable[(Logtable[a] + Logtable[b]) % 255]
    else:
        r =  Integer(0)


    if verbose >= 1: #tvn traces
        print 'Input: a'
        print 'Input: b'
        print 'Output: r'
        print 'Global: Alogtable'
        print 'Global: Logtable'
        print 'ExtFun: add'
        print 'ExtFun: mod255'
        
        print 'r a b Alogtable Logtable'
        print [r], [a], [b], Alogtable, Logtable
    
    assert is_byte(r)

    return r

def word_xor(a,b, verbose=1):
    """
    sage: word_xor([1,2,3,4],[1,2,3,4])
    [0, 0, 0, 0]

    sage: word_xor([1,2,3,4],[2,3,4,5])
    [3, 1, 7, 1]

    sage: word_xor([8,91,24,18],[73,143,43,11],verbose=0)
    [65, 212, 51, 25]
    
    sage: word_xor([18,91,234,88],[93,114,57,10],verbose=0)
    [79, 41, 211, 82]

    sage: word_xor([93,114,57,10],[18,91,234,88],verbose=0)
    [79, 41, 211, 82]

    """
    
    assert is_word(a) and is_word(b)
    r =  [xor(a[0],b[0]), xor(a[1],b[1]), 
          xor(a[2],b[2]), xor(a[3],b[3])]

    if verbose >= 1: #tvn traces
        print 'Input: a'
        print 'Input: b'
        print 'Output: r'
        print 'ExtFun: xor'
        
        print 'r a b'
        print r, a, b
        
    assert is_word(r)
    return r



def word_xor_xor_orig(a, b, c ,verbose=1):
    #inv :  r[i] = xor(xor(a[i],b[i]),c[i])
    r =  [xor(xor(a[0],b[0]),c[0]),
          xor(xor(a[1],b[1]),c[1]),
          xor(xor(a[2],b[2]),c[2]),
          xor(xor(a[3],b[3]),c[3])]

    assert is_word(r)
    return r

def word_xor_xor(a,b,c,verbose=1):
    r = [xor_xor(a[0],b[0],c[0],verbose),
         xor_xor(a[1],b[1],c[1],verbose),
         xor_xor(a[2],b[2],c[2],verbose),
         xor_xor(a[3],b[3],c[3],verbose)]

    if verbose >= 1: #tvn traces
        print 'Input: a'
        print 'Input: b'
        print 'Input: c'
        print 'Output: r'
        print 'ExtFun: xor_xor'
        
        print 'r a b c'
        print r, a, b, c
    
    assert is_word(r)
    return r

def SubWord(w,verbose=1):
    """
    tvn: *nested* array
    r[i] = S[w[i]]
    """
    r =  [S[w[0]], S[w[1]], S[w[2]], S[w[3]]];

    if verbose>= 1:    #tvn traces
        print 'Input: w'
        print 'Output: r'
        print 'Global: Si'
        print 'Global: S'
        print 'Global: Alogtable'
        print 'Global: Logtable'
        print 'r w Si S Alogtable Logtable'
        print r, w, Si, S, Alogtable, Logtable

    assert is_word(r)
    return r


def RotWord(w, verbose=1):
    """
    #tvn: miscs array type
    r0 = w1 , r1 = w2,  r2 = w3, r3 = w0
    
    """
    r = [w[1], w[2], w[3], w[0]];

    #tvn traces
    if verbose >= 1:
        print 'r w'
        print r,w

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
        print 'r t'
        print r, t

    assert is_state(r)
    return r

def State2Block(st, verbose = 1):
    """
    tvn: multidim array inv
    r[4*i+j] = st[i][j]
    """

    #inv: should get this:r0 = st00 ...
    r =  [st[0][0], st[0][1], st[0][2], st[0][3],
          st[1][0], st[1][1], st[1][2], st[1][3],
          st[2][0], st[2][1], st[2][2], st[2][3],
          st[3][0], st[3][1], st[3][2], st[3][3]]

    
    #tvn traces
    if verbose >= 1:
        print 'r st'
        print r, st

    assert is_block(r)
    return r

def SubBytes(st, verbose=1):
    """
    tvn: *nested* array
    r[i,j] = S[st[i,j]]
    """
    r =  [[S[st[0][0]], S[st[0][1]], S[st[0][2]], S[st[0][3]]],
          [S[st[1][0]], S[st[1][1]], S[st[1][2]], S[st[1][3]]],
          [S[st[2][0]], S[st[2][1]], S[st[2][2]], S[st[2][3]]],
          [S[st[3][0]], S[st[3][1]], S[st[3][2]], S[st[3][3]]]]

    if verbose >= 1: #tvn traces
        print 'r st S Si'
        print r, st, S, Si
        
    assert is_state(r)

    return r

def InvSubBytes(st, verbose=1):
    """
    tvn: *nested* array
    r[i,j] = Si[st[i,j]]
    """
    
    r= [[Si[st[0][0]], Si[st[0][1]], Si[st[0][2]], Si[st[0][3]]],
        [Si[st[1][0]], Si[st[1][1]], Si[st[1][2]], Si[st[1][3]]],
        [Si[st[2][0]], Si[st[2][1]], Si[st[2][2]], Si[st[2][3]]],
        [Si[st[3][0]], Si[st[3][1]], Si[st[3][2]], Si[st[3][3]]]]

    if verbose >= 1: #tvn traces
        print 'r st S Si'
        print r, st, S, Si

    assert is_state(r)
    return r

def ShiftRows(st, verbose=1):
    """
    tvn: miscs array inv
    [-r_3_3 + st_2_3 == 0, r_2_0 - st_2_0 == 0, r_3_1 - st_0_1 == 0, -r_1_3 + st_0_3 == 0, -r_2_2 + st_0_2 == 0, r_1_0 - st_1_0 == 0, r_0_1 - st_1_1 == 0, -r_0_3 + st_3_3 == 0, r_3_0 - st_3_0 == 0, r_0_0 - st_0_0 == 0, -r_3_2 + st_1_2 == 0, r_1_1 - st_2_1 == 0, -r_0_2 + st_2_2 == 0, r_2_1 - st_3_1 == 0, -r_2_3 + st_1_3 == 0, r_1_2 - st_3_2 == 0]

    sage: ShiftRows([[1,3,4,255],[1,2,3,4],[7,8,10,52],[0,1,2,15]],verbose=0)
    [[1, 2, 10, 15], [1, 8, 2, 255], [7, 1, 4, 4], [0, 3, 3, 52]]

    sage: ShiftRows([[1,13,4,55],[1,22,3,4],[7,18,10,52],[0,1,2,15]],verbose=0)
    [[1, 22, 10, 15], [1, 18, 2, 55], [7, 1, 4, 4], [0, 13, 3, 52]]    
    """


    r = [[st[0][0], st[1][1], st[2][2], st[3][3]],
         [st[1][0], st[2][1], st[3][2], st[0][3]],
         [st[2][0], st[3][1], st[0][2], st[1][3]],
         [st[3][0], st[0][1], st[1][2], st[2][3]]]

    if verbose>=1: #tvn traces
        print 'r st'
        print r, st
    
    assert is_state(r)

    return r

def InvShiftRows(st, verbose=1):
    """
    tvn: miscs array inv
    [-r_1_3 + st_2_3 == 0, -r_0_2 + st_2_2 == 0, r_3_1 - st_2_1 == 0, -r_3_3 + st_0_3 == 0, -r_2_2 + st_0_2 == 0, -r_2_1 + st_1_1 == 0, r_0_1 - st_3_1 == 0, r_2_0 - st_2_0 == 0, r_3_0 - st_3_0 == 0, r_0_0 - st_0_0 == 0, -r_3_2 + st_1_2 == 0, r_1_1 - st_0_1 == 0, r_1_0 - st_1_0 == 0, r_2_3 - st_3_3 == 0, -r_0_3 + st_1_3 == 0, r_1_2 - st_3_2 == 0]

    """
    r =  [[st[0][0], st[3][1], st[2][2], st[1][3]],
          [st[1][0], st[0][1], st[3][2], st[2][3]],
          [st[2][0], st[1][1], st[0][2], st[3][3]],
          [st[3][0], st[2][1], st[1][2], st[0][3]]]


    if verbose>=1: #tvn traces
        print 'r st'
        print r, st

    assert is_state(r)
    return r


def MixColumns(st, verbose=1):

    r = [[myxor([mul(2,st[0][0],verbose), mul(3,st[0][1],verbose), st[0][2],                st[0][3]                ]),
          myxor([st[0][0],                mul(2,st[0][1],verbose), mul(3,st[0][2],verbose), st[0][3]                ]),
          myxor([st[0][0],                st[0][1],                mul(2,st[0][2],verbose), mul(3,st[0][3],verbose) ]),
          myxor([mul(3,st[0][0],verbose), st[0][1],st[0][2],       mul(2,st[0][3],verbose)                          ])],
         
         [myxor([mul(2,st[1][0],verbose), mul(3,st[1][1],verbose), st[1][2],                st[1][3]                ]),
          myxor([st[1][0],                mul(2,st[1][1],verbose), mul(3,st[1][2],verbose), st[1][3]                ]),
          myxor([st[1][0],                st[1][1],                mul(2,st[1][2],verbose), mul(3,st[1][3],verbose) ]),
          myxor([mul(3,st[1][0],verbose), st[1][1],                st[1][2],                mul(2,st[1][3],verbose) ])],

         [myxor([mul(2,st[2][0],verbose), mul(3,st[2][1],verbose), st[2][2],                st[2][3]                ]),
          myxor([st[2][0],                mul(2,st[2][1],verbose), mul(3,st[2][2],verbose), st[2][3]                ]),
          myxor([st[2][0],                st[2][1],                mul(2,st[2][2],verbose), mul(3,st[2][3],verbose) ]),
          myxor([mul(3,st[2][0],verbose), st[2][1],                st[2][2],                mul(2,st[2][3],verbose) ])],

         [myxor([mul(2,st[3][0],verbose), mul(3,st[3][1],verbose), st[3][2],                st[3][3]                ]),
          myxor([st[3][0],                mul(2,st[3][1],verbose), mul(3,st[3][2],verbose), st[3][3]                ]),
          myxor([st[3][0],                st[3][1],                mul(2,st[3][2],verbose), mul(3,st[3][3],verbose) ]),
          myxor([mul(3,st[3][0],verbose), st[3][1],                st[3][2],                mul(2,st[3][3],verbose) ])]
         ]
    assert is_state(r)

    return r



def InvMixColumns(st, verbose=1):
    r = [
        [myxor([mul(14,st[0][0],verbose), mul(11,st[0][1],verbose), mul(13,st[0][2],verbose), mul( 9,st[0][3],verbose)]),
         myxor([mul( 9,st[0][0],verbose), mul(14,st[0][1],verbose), mul(11,st[0][2],verbose), mul(13,st[0][3],verbose)]),
         myxor([mul(13,st[0][0],verbose), mul( 9,st[0][1],verbose), mul(14,st[0][2],verbose), mul(11,st[0][3],verbose)]),
         myxor([mul(11,st[0][0],verbose), mul(13,st[0][1],verbose), mul( 9,st[0][2],verbose), mul(14,st[0][3],verbose)])],
                                            
        [myxor([mul(14,st[1][0],verbose), mul(11,st[1][1],verbose), mul(13,st[1][2],verbose), mul( 9,st[1][3],verbose)]),
         myxor([mul( 9,st[1][0],verbose), mul(14,st[1][1],verbose), mul(11,st[1][2],verbose), mul(13,st[1][3],verbose)]),
         myxor([mul(13,st[1][0],verbose), mul( 9,st[1][1],verbose), mul(14,st[1][2],verbose), mul(11,st[1][3],verbose)]),
         myxor([mul(11,st[1][0],verbose), mul(13,st[1][1],verbose), mul( 9,st[1][2],verbose), mul(14,st[1][3],verbose)])],
                                            
        [myxor([mul(14,st[2][0],verbose), mul(11,st[2][1],verbose), mul(13,st[2][2],verbose), mul( 9,st[2][3],verbose)]),
         myxor([mul( 9,st[2][0],verbose), mul(14,st[2][1],verbose), mul(11,st[2][2],verbose), mul(13,st[2][3],verbose)]),
         myxor([mul(13,st[2][0],verbose), mul( 9,st[2][1],verbose), mul(14,st[2][2],verbose), mul(11,st[2][3],verbose)]),
         myxor([mul(11,st[2][0],verbose), mul(13,st[2][1],verbose), mul( 9,st[2][2],verbose), mul(14,st[2][3],verbose)])],
                                            
        [myxor([mul(14,st[3][0],verbose), mul(11,st[3][1],verbose), mul(13,st[3][2],verbose), mul( 9,st[3][3],verbose)]),
         myxor([mul( 9,st[3][0],verbose), mul(14,st[3][1],verbose), mul(11,st[3][2],verbose), mul(13,st[3][3],verbose)]),
         myxor([mul(13,st[3][0],verbose), mul( 9,st[3][1],verbose), mul(14,st[3][2],verbose), mul(11,st[3][3],verbose)]),
         myxor([mul(11,st[3][0],verbose), mul(13,st[3][1],verbose), mul( 9,st[3][2],verbose), mul(14,st[3][3],verbose)])]
        ]

    assert is_state(r)
    return r
    
def AddRoundKey(st, rk0, rk1, rk2, rk3, verbose=1):
    """
    *nested* array
    r[i][j] = xor(st[i][j], rk[i][j])
    """
    assert is_state(st)
    assert is_word(rk0) and is_word(rk1) and is_word(rk2) and is_word(rk3)

    r = [
        [xor(st[0][0], rk0[0]), xor(st[0][1], rk0[1]), xor(st[0][2], rk0[2]), xor(st[0][3], rk0[3])],
        [xor(st[1][0], rk1[0]), xor(st[1][1], rk1[1]), xor(st[1][2], rk1[2]), xor(st[1][3], rk1[3])],
        [xor(st[2][0], rk2[0]), xor(st[2][1], rk2[1]), xor(st[2][2], rk2[2]), xor(st[2][3], rk2[3])],
        [xor(st[3][0], rk3[0]), xor(st[3][1], rk3[1]), xor(st[3][2], rk3[2]), xor(st[3][3], rk3[3])]
        ]

    if verbose >= 1:
        print 'Input: st'
        print 'Input: rk0'
        print 'Input: rk1'
        print 'Input: rk2'
        print 'Input: rk3'
        print 'Output: r_'
        print 'ExtFun: xor'

        print 'st rk0 rk1 rk2 rk3 r_'
        print st, rk0, rk1, rk2, rk3, r

    assert is_state(r)

    return r

def AddRoundKey_vn(st,rk):
    assert is_state(st)
    assert is_word(rk[0]) and is_word(rk[1]) and is_word(rk[2]) and is_word(rk[3])
    r = [
        [xor(st[0][0], rk[0][0]), xor(st[0][1], rk[0][1]), xor(st[0][2], rk[0][2]), xor(st[0][3], rk[0][3])],
        [xor(st[1][0], rk[1][0]), xor(st[1][1], rk[1][1]), xor(st[1][2], rk[1][2]), xor(st[1][3], rk[1][3])],
        [xor(st[2][0], rk[2][0]), xor(st[2][1], rk[2][1]), xor(st[2][2], rk[2][2]), xor(st[2][3], rk[2][3])],
        [xor(st[3][0], rk[3][0]), xor(st[3][1], rk[3][1]), xor(st[3][2], rk[3][2]), xor(st[3][3], rk[3][3])]
        ]

    if verbose >= 1:
        print 'Input: st'
        print 'Input: rk'
        print 'Output: r_'
        print 'ExtFun: xor'

        print 'st rk r_'
        print st, rk, r

    assert is_state(r)
    return r    



def AddRoundKey_vn_simple(st,rk):
    """
    for debugging purpose
    """

    st = [st_[:3] for st_ in st[:3]]
    rk = [rk_[:3] for rk_ in rk[:3]]
    
    r = [
        [xor(st[0][0], rk[0][0]), xor(st[0][1], rk[0][1]), xor(st[0][2], rk[0][2])],
        [xor(st[1][0], rk[1][0]), xor(st[1][1], rk[1][1]), xor(st[1][2], rk[1][2])],
        [xor(st[2][0], rk[2][0]), xor(st[2][1], rk[2][1]), xor(st[2][2], rk[2][2])]
        ]

    if verbose >= 1:
        print 'Input: st'
        print 'Input: rk'
        print 'Output: r_'
        print 'ExtFun: xor'

        print 'st rk r_'
        print st, rk, r

    
    return r 

def KeySetupEnc4(cipherKey, verbose=1):# return key_schedule
    """
    tvn: *multidim* array
    rk[i][j] = cipherKey[4*i+j]
    """
    print len(cipherKey)
    
    assert is_key(cipherKey)

    #rk = key_schedule'(others => [0, 0, 0, 0])
    rk = [[0,0,0,0]]*roundkey_index  #create an array of roundkey_index empty words
    for i in range(4):
        rk[i] = [cipherKey[4*i], cipherKey[4*i+1], cipherKey[4*i+2], cipherKey[4*i+3]]

    # #tvn: traces
    # if verbose >= 1:
    #     print 'rk cipherKey'
    #     print rk[:4], cipherKey



    #--# assert 0 <= i and i <= 3 and
    #--#        (for all p in Integer range 0 .. i =>
    #--#          (rk(p) = [cipherKey(4*p), cipherKey(4*p+1), cipherKey(4*p+2), cipherKey(4*p+3))))


    for i in range(4,44):
         if i % 4 == 0:
             rk[i] = word_xor_xor(rk[i-4], SubWord(RotWord(rk[i-1],verbose=0),verbose=0), 
                                  rcon[i/4-1],verbose=0)
         else:
             rk[i] = word_xor(rk[i-4], rk[i-1],verbose=0)


    #tvn: traces
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
        print 'rk cipherKey'
        print rk, cipherKey


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



    #tvn: traces
    # if verbose >= 1:
    #     print 'rk cipherKey'
    #     print rk[:6], cipherKey


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


    #tvn: traces
    if verbose >= 1:
        print 'rk cipherKey'
        print rk, cipherKey

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

    #tvn: traces
    if verbose >= 1:
        print 'rk cipherKey'
        print rk[:8], cipherKey

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


    assert is_key_schedule(rk)
    return rk


def KeySetupEnc(cipherKey, Nk, verbose=1): #return key_schedule
    assert is_key(cipherKey)
    rk = [[0,0,0,0]]*roundkey_index  #create an array of roundkey_index empty words
    if (Nk == 4):
         rk = KeySetupEnc4(cipherKey,verbose)
    if (Nk == 6):
        rk = KeySetupEnc6(cipherKey,verbose)
    if (Nk == 8):
        rk = KeySetupEnc8(cipherKey,verbose)

    assert is_key_schedule(rk)
    return rk



def KeyScheduleMod1__(W, Nr,verbose=1): #return key_schedule
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
        print 'rk, W, Nr'
        print rk, W, [Nr]

    assert is_key_schedule(rk)
    return rk


def KeyScheduleMod1_(W, Nr,verbose=1): #return key_schedule
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

    if verbose >= 1:
        vs1 = ['RK_%d_%d'%(i,j) for i in range(len(rk)) for j in range(len(rk[0]))]
        ns1 = [rk[i][j]  for i in range(len(rk)) for j in range(len(rk[0]))]

        vs2 = ['W_%d_%d'%(i,j) for i in range(len(W)) for j in range(len(W[0]))]
        ns2 = [W[i][j]  for i in range(len(W)) for j in range(len(W[0]))]


        print ' '.join(vs1+vs2)
        print ' '.join(map(str,ns1+ns2))

    assert is_key_schedule(rk)
    return rk

def KeyScheduleMod1(W, Nr,verbose=1): #return key_schedule
    assert is_key_schedule(W)
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

    if verbose >= 1:
        vs1 = ['RK_%d_%d'%(i,j) for i in range(len(rk)) for j in range(len(rk[0]))]
        ns1 = [rk[i][j]  for i in range(len(rk)) for j in range(len(rk[0]))]

        vs2 = ['W_%d_%d'%(i,j) for i in range(len(W)) for j in range(len(W[0]))]
        ns2 = [W[i][j]  for i in range(len(W)) for j in range(len(W[0]))]


        print ' '.join(vs1+vs2)
        print ' '.join(map(str,ns1+ns2))

    assert is_key_schedule(rk)
    return rk


def KeyScheduleMod2(W, Nr, verbose=1):# return key_schedule
    assert is_key_schedule(W)

    st = None
    rk = deepcopy(W)
    for i in range(1,Nr):
         st = [W[4*i], W[4*i+1], W[4*i+2], W[4*i+3]]
         assert is_state(st)
         st = InvMixColumns(st,verbose)
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
    return rk


def KeySetupDec(cipherKey, Nk, verbose=1): # return key_schedule
    assert is_key(cipherKey)
    r =  KeyScheduleMod2(KeyScheduleMod1(KeySetupEnc(cipherKey, Nk,verbose), Nk + 6,verbose), Nk + 6,verbose)
    assert is_key_schedule(r)
    return r


def AesKeySetupEnc(cipherKey, keyBits, verbose=1):
    assert is_key(cipherKey)
    Nr = keyBits/32 + 6
    rk = KeySetupEnc(cipherKey, keyBits/32,verbose=0)

    assert is_key_schedule(rk)

    if verbose >= 1: #tvntraces
        print 'Nr keyBits'
        print Nr, keyBits

    return Nr,rk

def AesKeySetupDec(cipherKey, keyBits, verbose=1):
    
    assert is_key(cipherKey)

    Nr =keyBits/32 + 6
    rk =KeySetupDec(cipherKey, keyBits/32,verbose=0)

    assert is_key_schedule(rk)

    if verbose >= 1: #tvntraces
        print 'Nr keyBits'
        print Nr, keyBits
        
    return Nr,rk


def AesEncrypt(rk,Nr,pt,verbose=1):
    assert is_key_schedule(rk)
    assert is_block(pt)
    st =AddRoundKey(Block2State(pt,verbose), rk[0], rk[1], rk[2], rk[3],verbose)
    # assert st = encrypt_round(Block2State(pt), rk, Nr, 0)
    
    for r in range(1,Nr):

        sb = SubBytes(st,verbose)
        sr = ShiftRows(sb,verbose)
        
        st = AddRoundKey(MixColumns(sr,verbose), rk[4*r], rk[4*r+1], rk[4*r+2], rk[4*r+3],verbose)

        
        # assert 1 <= r and r <= Nr-1 and Nr = Nr% and
        #        st = encrypt_round(Block2State(pt), rk, Nr, r)


    st =AddRoundKey(ShiftRows(SubBytes(st,verbose),verbose), rk[4*Nr], rk[4*Nr+1], rk[4*Nr+2], rk[4*Nr+3],verbose)
    # assert st = encrypt_round(Block2State(pt), rk, Nr, Nr)

    ct =State2Block(st,verbose)
    assert is_block(ct)
    return ct

def AesDecrypt(rk, Nr, ct,verbose=1):
    assert is_key_schedule(rk)
    assert is_block(ct)
    st = AddRoundKey(Block2State(ct,verbose), rk[0], rk[1], rk[2], rk[3],verbose)
    # assert st = decrypt_round(Block2State(ct), rk, Nr, 0)


    for r in range(1,Nr):
        st =AddRoundKey(InvMixColumns(InvShiftRows(InvSubBytes(st,verbose),verbose),verbose), rk[4*r], rk[4*r+1], rk[4*r+2], rk[4*r+3],verbose)
        # assert 1 <= r and r <= Nr-1 and Nr = Nr% and
        #        st = decrypt_round(Block2State(ct), rk, Nr, r)


    st =AddRoundKey(InvShiftRows(InvSubBytes(st,verbose),verbose), rk[4*Nr], rk[4*Nr+1], rk[4*Nr+2], rk[4*Nr+3],verbose)
    # assert st = decrypt_round(Block2State(ct), rk, Nr, Nr)

    pt =State2Block(st,verbose)
    assert is_block(pt)
    return pt





def Driver(verbose=1):
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

    print 'subword'
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
                      
   
   

    Key1 = [1,3,4,255,1,2,3,4,7,8,10,52,0,1,2,15,  1,3,4,255,1,2,3,4,7,8,10,52,0,1,2,15]
            


    Key2 = [89,32,4,90,1,213,16,4,34,8,80,13,0,1,0,132,
            82,28,76,21,132,48,89,123,90,80,12,12,10,8,40,65]


    Key3= [221, 35, 247, 82, 247, 246, 49, 41, 172, 47, 146, 208, 70, 99, 153, 38, 249, 200, 103, 242, 175, 74, 234, 164, 202, 222, 2, 178, 89, 64, 139, 160]
   
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
    print(KeySetupEnc(Key2,4),verbose) #4,6, or 8
   
    # ----------
    print("AES KeyScheduleMod1")

    print KeyScheduleMod1(KeySetupEnc(Key1,4,verbose),10,verbose) # 10, 12, 14
    print KeyScheduleMod1(KeySetupEnc(Key2,6,verbose),14,verbose) # 10, 12, 14

    
    
    print("AES KeyScheduleMod2")

    print(KeyScheduleMod1(KeySetupEnc(Key1,6),14,verbose)) # 10, 12, 14
    print(KeyScheduleMod1(KeySetupEnc(Key2,8),12,verbose)) # 10, 12, 14
    
   
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

    Rk = [[0,0,0,0]]*roundkey_index#Init_Key_Schedule(Rk)
    Nr = 14
    Block1 = [255,0,0,0, 1,0,0,0, 0,0,0,0, 0,0,0,1]
    Block2 = AesEncrypt(Rk,Nr,Block1,verbose)
    print(Block2)
   
   
   
    print("AES AesDecrypt 1")
    Block1 = AesDecrypt(Rk,Nr,Block2,verbose)
    print(Block1)


    print("AES AesEncrypt 1 - Cust")

    Rk = [[78,15,93,2]]*roundkey_index#Init_Key_Schedule(Rk)
    Nr = 14
    Block1 = [255,0,0,0, 1,0,0,0, 0,0,0,0, 0,0,0,1]
    Block2 = AesEncrypt(Rk,Nr,Block1,verbose)
    print(Block2)
   
   
   
    print("AES AesDecrypt 1 - Cust")
    Block1 = AesDecrypt(Rk,Nr,Block2,verbose)
    print(Block1)


    ##############

    print("AES AesEncrypt 2")

    Rk = [[0,0,0,0]]*roundkey_index#Init_Key_Schedule(Rk)
    Nr = 10
    Block1 = [255,0,28,0, 1,0,0,0, 0,0,0,92, 5,0,11,7]
    Block2 = AesEncrypt(Rk,Nr,Block1,verbose)
    print(Block2)
   
   
   
    print("AES AesDecrypt 2")
    Block1 = AesDecrypt(Rk,Nr,Block2,verbose)
    print(Block1)


    print("AES AesEncrypt 2 - Cust")

    Rk = [[78,15,93,2]]*roundkey_index#Init_Key_Schedule(Rk)
    Nr = 10
    Block1 = [255,0,28,0, 1,0,0,0, 0,0,0,92, 5,0,11,7]
    Block2 = AesEncrypt(Rk,Nr,Block1,verbose)
    print(Block2)
   
   
   
    print("AES AesDecrypt 2 - Cust")
    Block1 = AesDecrypt(Rk,Nr,Block2,verbose)
    print(Block1)


    #################


    print("AES AesEncrypt 3")

    Rk = [[0,0,0,0]]*roundkey_index#Init_Key_Schedule(Rk)
    Nr = 10
    Block1 = [255,0,28,15, 199,0,254,45, 0,89,0,92, 52,130,171,78]
    Block2 = AesEncrypt(Rk,Nr,Block1,verbose)
    print(Block2)
   
   
   
    print("AES AesDecrypt 3")
    Block1 = AesDecrypt(Rk,Nr,Block2,verbose)
    print(Block1)    



    print("AES AesEncrypt 3 - Cust")

    Rk = [[78,15,93,2]]*roundkey_index#Init_Key_Schedule(Rk)
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

def aes_gen_tc(fn,reps=100,v_range=255,seed=0):
    print '# Setting seed to', seed
    set_random_seed(seed)
    
    gen_v     = lambda siz: [randint(0,v_range) for _ in range(siz)]
    gen_key   = lambda : gen_v(key_index)
    gen_byte  = lambda : gen_v(byte_index)
    gen_rcon  = lambda  : gen_v(rcon_index)
    gen_word  = lambda : gen_v(word_index)
    gen_state = lambda : [gen_v(word_index) for _ in range(state_index)] 
    gen_roundkey = lambda : gen_v(roundkey_index)

    #MultiDim invs
    if fn =='KeySetupEnc4':
        rs = [KeySetupEnc4(gen_v(key_index)) for _ in range(reps)]
        
    elif fn =='KeySetupEnc6':
        rs = [KeySetupEnc6(gen_v(key_index)) for _ in range(reps)]

    elif fn =='KeySetupEnc8':
        rs = [KeySetupEnc8(gen_v(key_index)) for _ in range(reps)]
        
    elif fn == 'Block2State':
        rs = [Block2State(gen_v(byte_index)) for _ in range(reps)]
        
    elif fn == 'State2Block':
        rs = [State2Block([gen_v(byte_index) for _ in range(4)]) for _ in range(reps)]
        
    elif fn == 'RotWord':
        rs = [RotWord(gen_v(word_index)) for _ in range(reps)]
        
    elif fn == 'ShiftRows':
        rs = [ShiftRows([gen_v(byte_index) for _ in range(4)]) for _ in range(reps)]
        
    elif fn == 'InvShiftRows':
        rs= [InvShiftRows([gen_v(byte_index) for _ in range(4)]) for _ in range(reps)]    

    
    #nested
    elif fn == 'SubWord':
        rs = [SubWord(gen_v(word_index)) for _ in range(reps)]
        
    elif fn == 'SubBytes':
        rs = [SubBytes([gen_v(byte_index) for _ in range(4)]) for _ in range(reps)]    

    elif fn == 'InvSubBytes':
        rs = [InvSubBytes([gen_v(byte_index) for _ in range(4)]) for _ in range(reps)]    

    
    #ext_fun
    elif fn == 'word_xor':
        rs = [word_xor(gen_v(word_index),gen_v(word_index)) for _ in range(reps)]


    elif fn == 'word_xor_xor':
        rs = [word_xor_xor(gen_v(word_index),gen_v(word_index),gen_v(word_index))
              for _ in range(reps)]

    elif fn == 'mul':
        rs = [mul(randint(1,255),randint(1,255)) for _ in range(reps)]

    elif fn == 'addroundkey':
        myargs = [(gen_state(),gen_word(),gen_word(),gen_word(),gen_word())
                  for _ in range(reps)]
        rs = [AddRoundKey(*myarg) for myarg in myargs]

    elif fn == 'addroundkey_vn':
        myargs = [(gen_state(),[gen_word(),gen_word(),gen_word(),gen_word()]) for _ in range(reps)]
        rs = [AddRoundKey_vn(*myarg) for myarg in myargs]

    elif fn == 'addroundkey_vn_simple':
        myargs = [(gen_state(),[gen_word(),gen_word(),gen_word(),gen_word()])
                  for _ in range(reps)]
        rs = [AddRoundKey_vn_simple(*myarg) for myarg in myargs]

    elif fn == 'AesKeySetupDec':
        rs = [AesKeySetupDec(gen_v(key_index),choice([128,192, 256])) for _ in range(reps)]

    elif fn == 'AesKeySetupEnc':
        rs = [AesKeySetupEnc(gen_v(key_index),choice([128,192,256])) for _ in range(reps)]
    
    else:
        print 'cannot recognize fn: ', fn



#
# W: [[1, 3, 4, 255], [1, 2, 3, 4], [7, 8, 10, 52], [0, 1, 2, 15], [124, 116, 114, 156], [125, 118, 113, 152], [122, 126, 123, 172], [122, 127, 121, 163], [172, 194, 120, 70], [209, 180, 9, 222], [171, 202, 114, 114], [209, 181, 11, 209], [125, 233, 70, 120], [172, 93, 79, 166], [7, 151, 61, 212], [214, 34, 54, 5], [230, 236, 45, 142], [74, 177, 98, 40], [77, 38, 95, 252], [155, 4, 105, 249], [4, 21, 180, 154], [78, 164, 214, 178], [3, 130, 137, 78], [152, 134, 224, 183], [96, 244, 29, 220], [46, 80, 203, 110], [45, 210, 66, 32], [181, 84, 162, 151], [0, 206, 149, 9], [46, 158, 94, 103], [3, 76, 28, 71], [182, 24, 190, 208], [45, 96, 229, 71], [3, 254, 187, 32], [0, 178, 167, 103], [182, 170, 25, 183], [154, 180, 76, 9], [153, 74, 247, 41], [153, 248, 80, 78], [47, 82, 73, 249], [172, 143, 213, 28], [53, 197, 34, 53], [172, 61, 114, 123], [131, 111, 59, 130], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]


# Nr: 10

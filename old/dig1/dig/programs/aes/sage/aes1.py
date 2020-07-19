import common as C
from sage.all import *
"""
based on ADA implementation
also see the file /home/tnguyen/Dropbox/aes/c/pyAES.py for a Python implementation

"""


def xor(x,y):
    """
    sage: xor(2,3)
    1
    sage: xor(8,5)
    13
    sage: xor(5,8)
    13
    """
    return x.__xor__(y)

MAXKC = 8
MAXNR = 14

byte = 2**8  #256
is_byte = lambda b: 0 <= b <= (byte - 1)  #0 to 255

word_index = 4  #0..3,   
#word: 4 byte,  32 bit
is_word = lambda w: len(w)==word_index and C.vall(w,is_byte) 

is_byte_table = lambda t : len(t)==byte and C.vall(t,is_byte)
#is_word_table = lambda t : len(t)==byte and C.vall(t,is_word)

rcon_index = 10 #0..9
is_rcon_array = lambda t : len(t)==rcon_index and C.vall(t,is_word)

byte_index = 16 #0..15
#block : 16 byte, 128 bit
is_block = lambda b: len(b)==byte_index and C.vall(b,is_byte)

key_index = 4*MAXKC  #0..4*MAXKC-1
#key :  32 byte,  256 bit
is_key = lambda k: len(k)==key_index and C.vall(k,is_byte)

roundkey_index = 4*(MAXNR+1)  #0..4*(MAXNR+1)-1
#key_schedule: 60 word, 240 byte,  1920 bit
is_key_schedule = lambda ks: len(ks)==roundkey_index and C.vall(ks,is_word)

state_index = 4 #0..3
#state: 4 word, 16 byte,  128 bit
is_state = lambda s: len(s)==state_index and C.vall(s,is_word)

####

Logtable = [  #256 
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
]

assert is_byte_table(Logtable)

Alogtable = [ 
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
]

assert is_byte_table(Alogtable)

S = [
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
]

assert is_byte_table(S)

Si = [
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
]

assert is_byte_table(Si)


rcon = [
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
    ]            

assert is_rcon_array(rcon)


### Functions

def mul(a,b):
    """
    sage: mul(5,3)
    15
    sage: mul(5,0)
    0
    """
    assert is_byte(a) and is_byte(b)
    if a != 0 and b != 0:
        r =  Alogtable[(Logtable[a] + Logtable[b]) % 255]
    else:
        r =  0
    
    assert is_byte(r)
    return r

def word_xor(a,b):
    """
    sage: word_xor([1,2,3,4],[1,2,3,4])
    [0, 0, 0, 0]

    sage: word_xor([1,2,3,4],[2,3,4,5])
    [3, 1, 7, 1]

    """
    assert is_word(a) and is_word(b)
    r =  [xor(a[0],b[0]), xor(a[1],b[1]), 
          xor(a[2],b[2]), xor(a[3],b[3])]
    assert is_word(r)
    return r



def word_xor_xor(a, b, c):
    r =  [xor(xor(a[0],b[0]),c[0]),
          xor(xor(a[1],b[1]),c[1]),
          xor(xor(a[2],b[2]),c[2]),
          xor(xor(a[3],b[3]),c[3])]

    assert is_word(r)
    return r




def SubWord(w):
    print w
    r =  [S[w[0]], S[w[1]], S[w[2]], S[w[3]]];

    assert is_word(r)
    print r
    return r


def RotWord(w):
    r = [w[1], w[2], w[3], w[0]];
    assert is_word(r)
    return r

def Block2State(t):
    r =  [[t[0], t[1], t[2], t[3]],
          [t[4], t[5], t[6], t[7]],
          [t[8], t[9], t[10], t[11]],
          [t[12], t[13], t[14], t[15]]]
    assert is_state(r)
    return r

def State2Block(st):
    r =  [st[0][0], st[0][1], st[0][2], st[0][3],
          st[1][0], st[1][1], st[1][2], st[1][3],
          st[2][0], st[2][1], st[2][2], st[2][3],
          st[3][0], st[3][1], st[3][2], st[3][3]]
    assert is_block(r)
    return r

def SubBytes(st):
    r =  [[S[st[0][0]], S[st[0][1]], S[st[0][2]], S[st[0][3]]],
          [S[st[1][0]], S[st[1][1]], S[st[1][2]], S[st[1][3]]],
          [S[st[2][0]], S[st[2][1]], S[st[2][2]], S[st[2][3]]],
          [S[st[3][0]], S[st[3][1]], S[st[3][2]], S[st[3][3]]]]
    assert is_state(r)
    return r

def InvSubBytes(st):
    r= [[Si[st[0][0]], Si[st[0][1]], Si[st[0][2]], Si[st[0][3]]],
        [Si[st[1][0]], Si[st[1][1]], Si[st[1][2]], Si[st[1][3]]],
        [Si[st[2][0]], Si[st[2][1]], Si[st[2][2]], Si[st[2][3]]],
        [Si[st[3][0]], Si[st[3][1]], Si[st[3][2]], Si[st[3][3]]]]

    assert is_state(r)
    return r

def ShiftRows(st):
    r = [[st[0][0], st[1][1], st[2][2], st[3][3]],
         [st[1][0], st[2][1], st[3][2], st[0][3]],
         [st[2][0], st[3][1], st[0][2], st[1][3]],
         [st[3][0], st[0][1], st[1][2], st[2][3]]]
    assert is_state(r)
    return r

def InvShiftRows(st):
    r =  [[st[0][0], st[3][1], st[2][2], st[1][3]],
          [st[1][0], st[0][1], st[3][2], st[2][3]],
          [st[2][0], st[1][1], st[0][2], st[3][3]],
          [st[3][0], st[2][1], st[1][2], st[0][3]]]
    assert is_state(r)
    return r


def MixColumns(st):
    r = [[xor(xor(xor(mul(2, st[0][0]) , mul(3, st[0][1])),st[0][2]),st[0][3]),
          xor(xor(xor(st[0][0], mul(2, st[0][1])), mul(3, st[0][2])),st[0][3]),
          xor(xor(xor(st[0][0],st[0][1]),mul(2, st[0][2])),mul(3, st[0][3])),
          xor(xor(xor(mul(3, st[0][0]),st[0][1]),st[0][2]),mul(2, st[0][3]))],
         
         [xor(xor(xor(mul(2, st[1][0]), mul(3, st[1][1])),st[1][2]),st[1][3]),
          xor(xor(xor(st[1][0],mul(2, st[1][1])), mul(3, st[1][2])),st[1][3]),
          xor(xor(xor(st[1][0],st[1][1]),mul(2, st[1][2])),mul(3, st[1][3])),
          xor(xor(xor(mul(3, st[1][0]),st[1][1]),st[1][2]),mul(2, st[1][3]))],

         [xor(xor(xor(mul(2, st[2][0]),mul(3, st[2][1])),st[2][2]),st[2][3]),
          xor(xor(xor(st[2][0],mul(2, st[2][1])), mul(3, st[2][2])),st[2][3]),
          xor(xor(xor(st[2][0], st[2][1]), mul(2, st[2][2])),mul(3, st[2][3])),
          xor(xor(xor(mul(3, st[2][0]),st[2][1]), st[2][2]), mul(2, st[2][3]))],

         [xor(xor(xor(mul(2, st[3][0]), mul(3, st[3][1])), st[3][2]), st[3][3]),
          xor(xor(xor(st[3][0], mul(2, st[3][1])), mul(3, st[3][2])), st[3][3]),
          xor(xor(xor(st[3][0],st[3][1]), mul(2, st[3][2])), mul(3, st[3][3])),
          xor(xor(xor(mul(3, st[3][0]), st[3][1]), st[3][2]), mul(2, st[3][3]))]
        ]
    assert is_state(r)
    return r



def InvMixColumns(st):

    r = [
        [xor(xor(xor(mul(14, st[0][0]), mul(11, st[0][1])),mul(13, st[0][2])),mul(9, st[0][3])),
         xor(xor(xor(mul(9, st[0][0]), mul(14, st[0][1])), mul(11, st[0][2])), mul(13, st[0][3])),
         xor(xor(xor(mul(13, st[0][0]), mul(9, st[0][1])), mul(14, st[0][2])), mul(11, st[0][3])),
         xor(xor(xor(mul(11, st[0][0]), mul(13, st[0][1])), mul(9, st[0][2])), mul(14, st[0][3]))],
        
        [xor(xor(xor(mul(14, st[1][0]), mul(11, st[1][1])), mul(13, st[1][2])), mul(9, st[1][3])),
         xor(xor(xor(mul(9, st[1][0]), mul(14, st[1][1])), mul(11, st[1][2])), mul(13, st[1][3])),
         xor(xor(xor(mul(13, st[1][0]), mul(9, st[1][1])), mul(14, st[1][2])), mul(11, st[1][3])),
         xor(xor(xor(mul(11, st[1][0]), mul(13, st[1][1])), mul(9, st[1][2])), mul(14, st[1][3]))],

        [xor(xor(xor(mul(14, st[2][0]), mul(11, st[2][1])), mul(13, st[2][2])), mul( 9, st[2][3])),
         xor(xor(xor(mul( 9, st[2][0]), mul(14, st[2][1])), mul(11, st[2][2])), mul(13, st[2][3])),
         xor(xor(xor(mul(13, st[2][0]), mul(9,  st[2][1])), mul(14, st[2][2])), mul(11, st[2][3])),
         xor(xor(xor(mul(11, st[2][0]), mul(13, st[2][1])), mul( 9, st[2][2])), mul(14, st[2][3]))],
            
        [xor(xor(xor(mul(14, st[3][0]), mul(11, st[3][1])), mul(13, st[3][2])), mul( 9, st[3][3])),
         xor(xor(xor(mul( 9, st[3][0]), mul(14, st[3][1])), mul(11, st[3][2])), mul(13, st[3][3])),
         xor(xor(xor(mul(13, st[3][0]), mul( 9, st[3][1])), mul(14, st[3][2])), mul(11, st[3][3])),
         xor(xor(xor(mul(11, st[3][0]), mul(13, st[3][1])), mul( 9, st[3][2])), mul(14, st[3][3]))]
        ]

    assert is_state(r)
    return r
    
def AddRoundKey(st, rk0, rk1, rk2, rk3):
    assert is_word(rk0) and is_word(rk1) and is_word(rk2) and is_word(rk3)
    r = [
        [xor(st[0][0], rk0[0]), xor(st[0][1], rk0[1]), xor(st[0][2], rk0[2]), xor(st[0][3], rk0[3])],
        [xor(st[1][0], rk1[0]), xor(st[1][1], rk1[1]), xor(st[1][2], rk1[2]), xor(st[1][3], rk1[3])],
        [xor(st[2][0], rk2[0]), xor(st[2][1], rk2[1]), xor(st[2][2], rk2[2]), xor(st[2][3], rk2[3])],
        [xor(st[3][0], rk3[0]), xor(st[3][1], rk3[1]), xor(st[3][2], rk3[2]), xor(st[3][3], rk3[3])]
        ]
    assert is_state(r)
    return r

def KeySetupEnc4(cipherKey):# return key_schedule
    assert is_key(cipherKey)

    #print 'ck:'
    #print cipherKey

    #rk = key_schedule'(others => [0, 0, 0, 0])
    rk = [[0,0,0,0]]*roundkey_index  #create an array of roundkey_index empty words
    for i in range(4):
        rk[i] = [cipherKey[4*i], cipherKey[4*i+1], cipherKey[4*i+2], cipherKey[4*i+3]]



    #--# assert 0 <= i and i <= 3 and
    #--#        (for all p in Integer range 0 .. i =>
    #--#          (rk(p) = [cipherKey(4*p), cipherKey(4*p+1), cipherKey(4*p+2), cipherKey(4*p+3))))


    for i in range(4,44):
         if i % 4 == 0:
             rk[i] = word_xor_xor(rk[i-4], SubWord(RotWord(rk[i-1])), rcon[i/4-1])
         else:
             rk[i] = word_xor(rk[i-4], rk[i-1])

    # assert 4 <= i and i <= 43 and
    # (for all p in Integer range 0 .. 3 =>
    #          (rk(p) = [cipherKey(4*p), cipherKey(4*p+1), cipherKey(4*p+2), cipherKey(4*p+3)))) and
    #        (for all p in Integer range 4 .. i =>
    #          ((p mod 4 = 0 and rk(p) = word_xor_xor(rk(p-4), SubWord(RotWord(rk(p-1))), rcon(p/4-1))) or
    #          (p mod 4 /= 0 and rk(p) = word_xor(rk(p-4), rk(p-1)))))


    assert is_key_schedule(rk)
    return rk


def KeySetupEnc6(cipherKey):# return key_schedule
    assert is_key(cipherKey)

    rk = [[0,0,0,0]]*roundkey_index  #create an array of roundkey_index empty words

    for i in range(6):
        rk[i]= [cipherKey[4*i], cipherKey[4*i+1], cipherKey[4*i+2], cipherKey[4*i+3]]
        # assert 0 <= i and i <= 5 and
        #        (for all p in Integer range 0 .. i =>
        #          (rk(p) = [cipherKey(4*p), cipherKey(4*p+1), cipherKey(4*p+2), cipherKey(4*p+3))))


    for i in range(6,52):
        if (i % 6 == 0):
            rk[i] = word_xor_xor(rk[i-6], SubWord(RotWord(rk[i-1])), rcon[i/6-1])
        else:
            rk[i] = word_xor(rk[i-6], rk[i-1])
        # assert 6 <= i and i <= 51 and
        #        (for all p in Integer range 0 .. 5 =>
        #          (rk(p) = [cipherKey(4*p), cipherKey(4*p+1), cipherKey(4*p+2), cipherKey(4*p+3)))) and
        #        (for all p in Integer range 6 .. i =>
        #          ((p mod 6 = 0 and rk(p) = word_xor_xor(rk(p-6), SubWord(RotWord(rk(p-1))), rcon(p/6-1))) or
        #          (p mod 6 /= 0 and rk(p) = word_xor(rk(p-6), rk(p-1)))))


    assert is_key_schedule(rk)
    return rk


def KeySetupEnc8(cipherKey):# return key_schedule
    assert is_key(cipherKey)

    rk = [[0,0,0,0]]*roundkey_index  #create an array of roundkey_index empty words


    for i in range(8):
        rk[i] = [cipherKey[4*i], cipherKey[4*i+1], cipherKey[4*i+2], cipherKey[4*i+3]]
        # assert 0 <= i and i <= 7 and
        #        (for all p in Integer range 0 .. i =>
        #          (rk(p) = [cipherKey(4*p), cipherKey(4*p+1), cipherKey(4*p+2), cipherKey(4*p+3))))
        

    for i in range(8,60):
        if (i % 8 == 0):
            rk[i] = word_xor_xor(rk[i-8], SubWord(RotWord(rk[i-1])), rcon[i/8-1])
        elif (i % 4 == 0):
            rk[i] = word_xor(rk[i-8], SubWord(rk[i-1]))
        else:
            rk[i] = word_xor(rk[i-8], rk[i-1])

        # assert 8 <= i and i <= 59 and
        #        (for all p in Integer range 0 .. 7 =>
        #          (rk(p) = [cipherKey(4*p), cipherKey(4*p+1), cipherKey(4*p+2), cipherKey(4*p+3)))) and
        #        (for all p in Integer range 8 .. i =>
        #          ((p % 8 = 0 and                  rk(p) = word_xor_xor(rk(p-8), SubWord(RotWord(rk(p-1))), rcon(p/8-1))) or
        #          (p % 8 /= 0 and p % 4 = 0 and  rk(p) = word_xor(rk(p-8), SubWord(rk(p-1)))) or
        #          (p % 8 /= 0 and p % 4 /= 0 and rk(p) = word_xor(rk(p-8), rk(p-1)))))


    assert is_key_schedule(rk)
    return rk


def KeySetupEnc(cipherKey, Nk): #return key_schedule
    assert is_key(cipherKey)
    rk = [[0,0,0,0]]*roundkey_index  #create an array of roundkey_index empty words
    if (Nk == 4):
         rk = KeySetupEnc4(cipherKey)
    if (Nk == 6):
        rk = KeySetupEnc6(cipherKey)
    if (Nk == 8):
        rk = KeySetupEnc8(cipherKey)

    assert is_key_schedule(rk)
    return rk


def KeyScheduleMod1(W, Nr): #return key_schedule
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

    assert is_key_schedule(rk)
    return rk


def KeyScheduleMod2(W, Nr):# return key_schedule
    assert is_key_schedule(W)

    st = None
    rk = deepcopy(W)
    for i in range(1,Nr):
         st = [W[4*i], W[4*i+1], W[4*i+2], W[4*i+3]]
         assert is_state(st)
         st = InvMixColumns(st)
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


def KeySetupDec(cipherKey, Nk): # return key_schedule
    assert is_key(cipherKey)
    r =  KeyScheduleMod2(KeyScheduleMod1(KeySetupEnc(cipherKey, Nk), Nk + 6), Nk + 6)
    assert is_key_schedule(r)
    return r


def AesKeySetupEnc(cipherKey, keyBits):
    assert is_key(cipherKey)
    Nr = keyBits/32 + 6
    rk = KeySetupEnc(cipherKey, keyBits/32)

    assert is_key_schedule(rk)

    return Nr,rk

def AesKeySetupDec(cipherKey, keyBits):
    assert is_key(cipherKey)

    Nr =keyBits/32 + 6
    rk =KeySetupDec(cipherKey, keyBits/32)

    assert is_key_schedule(rk)

    return Nr,rk


def AesEncrypt(rk,Nr,pt):
    assert is_key_schedule(rk)
    assert is_block(pt)
    st =AddRoundKey(Block2State(pt), rk[0], rk[1], rk[2], rk[3])
    # assert st = encrypt_round(Block2State(pt), rk, Nr, 0)

    for r in range(1,Nr):
        st = AddRoundKey(MixColumns(ShiftRows(SubBytes(st))), rk[4*r], rk[4*r+1], rk[4*r+2], rk[4*r+3])
        # assert 1 <= r and r <= Nr-1 and Nr = Nr% and
        #        st = encrypt_round(Block2State(pt), rk, Nr, r)


    st =AddRoundKey(ShiftRows(SubBytes(st)), rk[4*Nr], rk[4*Nr+1], rk[4*Nr+2], rk[4*Nr+3])
    # assert st = encrypt_round(Block2State(pt), rk, Nr, Nr)

    ct =State2Block(st)
    assert is_block(ct)
    return ct

def AesDecrypt(rk, Nr, ct):
    assert is_key_schedule(rk)
    assert is_block(ct)
    st = AddRoundKey(Block2State(ct), rk[0], rk[1], rk[2], rk[3])
    # assert st = decrypt_round(Block2State(ct), rk, Nr, 0)


    for r in range(1,Nr):
        st =AddRoundKey(InvMixColumns(InvShiftRows(InvSubBytes(st))), rk[4*r], rk[4*r+1], rk[4*r+2], rk[4*r+3])
        # assert 1 <= r and r <= Nr-1 and Nr = Nr% and
        #        st = decrypt_round(Block2State(ct), rk, Nr, r)


    st =AddRoundKey(InvShiftRows(InvSubBytes(st)), rk[4*Nr], rk[4*Nr+1], rk[4*Nr+2], rk[4*Nr+3])
    # assert st = decrypt_round(Block2State(ct), rk, Nr, Nr)

    pt =State2Block(st)
    assert is_block(pt)
    return pt





def Driver():
    # print("AES mul")
    # print mul(8,3)
    # print mul(50,50)
    # print mul(8,0)

    # print("AES word_xor")
    # print word_xor([0,1,9,1],[0,0,2,245])
    # print word_xor([0,0,99,1],[100,0,2,145])

    # print("AES word_xor_xor")
    # print word_xor_xor([0,1,0,0],[1,0,1,1],[1,1,1,1])
   
    # print word_xor_xor([0,1,0,89],[124,0,1,1],[0,1,241,1])
    
    # print 'subword'
    #print SubWord([1,1,1,255])
     #print SubWord([231,189,0,255])
     #print SubWord([0,0,7,75])

    # print 'RodWord'
    # print RotWord([1,3,4,255]);
    # print RotWord([89,0,43,24]);
    # print RotWord([41,38,67,8]);

    # print 'Block2State'
    # print Block2State([1,3,4,255,
    #                    1,2,3,4,
    #                    7,8,10,52,
    #                    0,1,2,15])
   
    # print("AES State2Block");
    # print State2Block([
    #         [1,3,4,255],
    #         [1,2,3,4],
    #         [7,8,10,52],
    #         [0,1,2,15]])
    
    
    
    # print("AES SubBytes")
    # print SubBytes([
    #         [1,3,4,255],
    #         [1,2,3,4],
    #         [7,8,10,52],
    #         [0,1,2,15]])
    
    
    
    # print("AES InvSubBytes")
    # print InvSubBytes([
    #         [1,3,4,255],
    #         [1,2,3,4],
    #         [7,8,10,52],
    #         [0,1,2,15]])
    
    
    
    
    # print InvSubBytes([
    #         [0,13,89,132],
    #         [12,82,10,97],
    #         [40,88,42,80],
    #         [0,111,102,105]])
    
    
    
    
    # print("AES ShiftRows")
    # print ShiftRows([
    #         [1,3,4,255],
    #         [1,2,3,4],
    #         [7,8,10,52],
    #         [0,1,2,15]])
    
    
    
    
    # print("AES InvShiftRows")
    # print InvShiftRows([
    #         [1,3,4,255],
    #         [1,2,3,4],
    #         [7,8,10,52],
    #         [0,1,2,15]])
    
    
   
    # print("AES MixColumns")
    # print MixColumns([
    #         [1,3,4,255],
    #         [1,2,3,4],
    #         [7,8,10,52],
    #         [0,1,2,15]])
    
    
   
    # print("AES AddRoundKey")
    # print AddRoundKey([[1,3,4,255],[1,2,3,4],[7,8,10,52],[0,1,2,15]],
    #                   [1,3,4,255],
    #                   [1,3,4,255],
    #                   [1,3,4,255],
    #                   [1,3,4,255])
                      
   
   
   
    Key1 = [1,3,4,255,1,2,3,4,7,8,10,52,0,1,2,15,
            1,3,4,255,1,2,3,4,7,8,10,52,0,1,2,15]


    #Key2 = [89,32,4,90,1,213,16,4,34,8,80,13,0,1,0,132,
    #82,28,76,21,132,48,89,123,90,80,12,12,10,8,40,65]
   
    #print("AES KeySetup4")
    #print(KeySetupEnc4(Key1))
    #print(KeySetupEnc4(Key2))
   
    # print("AES KeySetup6")
    # print(KeySetupEnc6(Key1))
    # print(KeySetupEnc6(Key2))
   
   
    # print("AES KeySetup8")
    # print(KeySetupEnc8(Key1))
    # print(KeySetupEnc8(Key2))
   
   
    # print("AES KeySetupEnc")
    # print(KeySetupEnc(Key1,8)) #4,6, or 8
    # print(KeySetupEnc(Key2,4)) #4,6, or 8
   
    # # ----------
    # print("AES KeyScheduleMod1")
    # print(KeyScheduleMod1(KeySetupEnc(Key1,4),10)) # 10, 12, 14
    # print(KeyScheduleMod1(KeySetupEnc(Key2,6),14)) # 10, 12, 14
    
    
    # print("AES KeyScheduleMod2")
    # print(KeyScheduleMod1(KeySetupEnc(Key1,6),14)) # 10, 12, 14
    # print(KeyScheduleMod1(KeySetupEnc(Key2,8),12)) # 10, 12, 14
    
   
    # print("AES KeySetupDec")
    # print(KeySetupDec(Key1,8)) #4,6,8
    # print(KeySetupDec(Key2,4)) #4,6,8



    # print("AES aesKeySetupEnc")
    # Nr,Rk = AesKeySetupEnc(Key1,#--cipherKey
    #                        192, #--keyBits 128,192, 256
    #                        )
   
    # print(Rk)
    # print(Nr)


    # Nr,Rk = AesKeySetupEnc(Key2,#--cipherKey
    #                        128, #--keyBits 128,192, 256
    #                        )
   
    # print(Rk)
    # print(Nr)
   
   
   
    # #-------
    # print("AES aesKeySetupDec")
    # Nr, Rk = AesKeySetupDec(Key1,#--cipherKey
    #                         192, #--keyBits 128,192, 256
    #                         )
    
    # print(Rk)
    # print(Nr)

    # Nr, Rk = AesKeySetupDec(Key2,#--cipherKey
    #                         256, #--keyBits 128,192, 256
    #                         )
    
    # print(Rk)
    # print(Nr)

   
    # #-------
    # print("AES AesEncrypt")
    # Rk = [[0,0,0,0]]*roundkey_index#Init_Key_Schedule(Rk)
    # Nr = 14
    # Block1 = [255,0,0,0, 1,0,0,0, 0,0,0,0, 0,0,0,1]
    # Block2 = AesEncrypt(Rk,Nr,Block1)
    # print(Block2)
   
   
   
    # print("AES AesDecrypt")
    # Rk = [[0,0,0,0]]*roundkey_index#Init_Key_Schedule(Rk)
    # Block1 = AesDecrypt(Rk,Nr,Block2)
    # print(Block1)



    # print("AES AesEncrypt")
    # Rk = [[0,0,0,0]]*roundkey_index#Init_Key_Schedule(Rk)
    # Nr = 10
    # Block1 = [255,0,28,0, 1,0,0,0, 0,0,0,92, 5,0,11,7]
    # Block2 = AesEncrypt(Rk,Nr,Block1)
    # print(Block2)
   
   
   
    # print("AES AesDecrypt")
    # Rk = [[0,0,0,0]]*roundkey_index#Init_Key_Schedule(Rk)
    # Block1 = AesDecrypt(Rk,Nr,Block2)
    # print(Block1)

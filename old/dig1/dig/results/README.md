Log file recording published experimental results 


* mpp(icse14),thesis (ran on Prime Linux)
DIG results for NLA: icse2013_nla.txt (important, #gen, #tgen is the ***sum*** of all locs)
DIG results for Disj: icse2013_mpp.txt (important, #gen, #tgen is the ***sum*** of all locs)

KIP results for NLA: icse2013_nla_ktp.txt
KIP results for Disj: icse2013_mpp_ktp.txt


* tosem2012 (ran on Macbook)
DIG results for NLA: tosem_results_all.txt
DIG results for AES/Array, also used in thesis: tosem_results_all.txt




$ grep "nlocs" icse2013_nla_ktp.txt

* nlocs 2 'cohendiv LI0, cohendiv LI1', invs 152 (p 7 (k>0 14, lem>0 4, assumes>0 0 redun 7), d 135, u 3 e 1), k 2, time 8.2
* nlocs 2 'divbin LI0, divbin LI1', invs 96 (p 8 (k>0 15, lem>0 5, assumes>0 30 redun 9), d 72, u 4 e 3), k 1, time 8.7
* nlocs 1 'mannadiv LI0', invs 49 (p 3 (k>0 2, lem>0 0, assumes>0 0 redun 4), d 37, u 5 e 0), k 1, time 5.6
* nlocs 2 'hard LI0, hard LI1', invs 107 (p 11 (k>0 4, lem>0 10, assumes>0 53 redun 17), d 78, u 1 e 0), k 1, time 9.2
* nlocs 1 'sqrt1 LI0', invs 27 (p 3 (k>0 1, lem>0 2, assumes>0 0 redun 6), d 15, u 2 e 1), k 1, time 4.3
* nlocs 2 'dijkstra LI0, dijkstra LI1', invs 62 (p 8 (k>0 6, lem>0 2, assumes>0 24 redun 10), d 36, u 7 e 1), k 1, time 10.9
* nlocs 1 'freire1 LI0', invs 25 (p 2 (k>0 0, lem>0 0, assumes>0 0 redun 1), d 20, u 2 e 0), k 0, time 2.2
* nlocs 1 'freire2 LI0', invs 35 (p 3 (k>0 1, lem>0 4, assumes>0 0 redun 5), d 23, u 1 e 3), k 1, time 5.1
* nlocs 1 'cohencu LI0', invs 31 (p 4 (k>0 1, lem>0 4, assumes>0 0 redun 7), d 19, u 1 e 0), k 1, time 4.2
* nlocs 1 'euclidex1 LI0', invs 108 (p 1 (k>0 8, lem>0 0, assumes>0 0 redun 0), d 94, u 13 e 0), k 1, time 12.8
* nlocs 2 'euclidex2 LI1, euclidex2 LI1', invs 209 (p 8 (k>0 12, lem>0 0, assumes>0 0 redun 4), d 192, u 4 e 1), k 1, time 14.6
* nlocs 3 'euclidex3 LI2, euclidex3 LI1, euclidex3 LI0', invs 475 (p 14 (k>0 25, lem>0 2, assumes>0 0 redun 9), d 443, u 4 e 5), k 1, time 23.4
* nlocs 3 'lcm1 LI0, lcm1 LI1, lcm1 LI2', invs 203 (p 12 (k>0 0, lem>0 0, assumes>0 0 redun 10), d 180, u 0 e 1), k 0, time 14.2
* nlocs 1 'lcm2 LI0', invs 52 (p 1 (k>0 10, lem>0 0, assumes>0 0 redun 0), d 51, u 0 e 0), k 1, time 0.9
* nlocs 1 'prodbin LI0', invs 61 (p 3 (k>0 10, lem>0 0, assumes>0 0 redun 0), d 57, u 0 e 1), k 2, time 1.1
* nlocs 1 'prod4br LI0', invs 42 (p 4 (k>0 7, lem>0 2, assumes>0 0 redun 2), d 34, u 0 e 2), k 1, time 8.6
* nlocs 3 'fermat1 LI1, fermat1 LI2, fermat1 LI0', invs 217 (p 6 (k>0 1, lem>0 0, assumes>0 0 redun 4), d 198, u 0 e 9), k 1, time 6.2
* nlocs 1 'fermat2 LI0', invs 70 (p 2 (k>0 0, lem>0 0, assumes>0 0 redun 2), d 64, u 0 e 2), k 0, time 5.2
* nlocs 1 'knuth LI0', invs 113 (p 4 (k>0 6, lem>0 0, assumes>0 0 redun 2), d 98, u 1 e 8), k 2, time 24.6
* nlocs 1 'geo1 LI0', invs 25 (p 2 (k>0 4, lem>0 0, assumes>0 0 redun 0), d 20, u 0 e 3), k 3, time 1.5
* nlocs 1 'geo2 LI0', invs 45 (p 1 (k>0 10, lem>0 0, assumes>0 0 redun 0), d 42, u 0 e 2), k 3, time 2.1
* nlocs 1 'geo3 LI0', invs 65 (p 1 (k>0 12, lem>0 0, assumes>0 0 redun 0), d 62, u 0 e 2), k 1, time 2.7
* nlocs 1 'ps2 LI0', invs 25 (p 2 (k>0 0, lem>0 2, assumes>0 0 redun 3), d 16, u 2 e 2), k 0, time 4.0
* nlocs 1 'ps3 LI0', invs 25 (p 2 (k>0 0, lem>0 0, assumes>0 0 redun 3), d 16, u 2 e 2), k 0, time 4.2
* nlocs 1 'ps4 LI0', invs 25 (p 2 (k>0 0, lem>0 2, assumes>0 0 redun 3), d 16, u 2 e 2), k 0, time 4.9
* nlocs 1 'ps5 LI0', invs 24 (p 2 (k>0 0, lem>0 0, assumes>0 0 redun 3), d 18, u 1 e 0), k 0, time 7.4
* nlocs 1 'ps6 LI0', invs 25 (p 2 (k>0 0, lem>0 0, assumes>0 0 redun 1), d 10, u 4 e 8), k 0, time 69.5




$ grep "nlocs" icse2013_mpp_ktp.txt
* nlocs 1 'cavf1a LI0', invs 15 (p 3 (k>0 0, lem>0 4, assumes>0 0 redun 4), d 5, u 3 e 0), k 0, time 2.3
* nlocs 1 'vumemcopy_abstract LI0', invs 69 (p 4 (k>0 3, lem>0 2, assumes>0 0 redun 6), d 43, u 16 e 0), k 1, time 7.7
* nlocs 1 'oddeven3', invs 286 (p 8 (k>0 0, lem>0 0, assumes>0 0 redun 77), d 201, u 0 e 0), k 0, time 16.0
* nlocs 1 'oddeven4', invs 867 (p 22 (k>0 0, lem>0 0, assumes>0 0 redun 206), d 639, u 0 e 0), k 0, time 46.0
* nlocs 1 'oddeven5', invs 2334 (p 52 (k>0 0, lem>0 0, assumes>0 0 redun 510), d 1772, u 0 e 0), k 0, time 1319.4
* nlocs 1 'bubble3', invs 249 (p 8 (k>0 0, lem>0 0, assumes>0 0 redun 76), d 165, u 0 e 0), k 0, time 4.9
* nlocs 1 'bubble4', invs 832 (p 22 (k>0 0, lem>0 0, assumes>0 0 redun 203), d 607, u 0 e 0), k 0, time 47.6
* nlocs 1 'bubble5', invs 2198 (p 52 (k>0 0, lem>0 0, assumes>0 0 redun 509), d 1637, u 0 e 0), k 0, time 938.2
* nlocs 4 'partial_decr3 LI0, partial_decr3 LI1, partial_decr3 LI2, partial_decr3 LP', invs 479 (p 10 (k>0 0, lem>0 0, assumes>0 0 redun 96), d 363, u 10 e 0), k 0, time 50.8
* nlocs 5 'partial_decr4 LI0, partial_decr4 LI1, partial_decr4 LI2, partial_decr4 LI3, partial_decr4 LP', invs 1217 (p 15 (k>0 0, lem>0 0, assumes>0 0 redun 238), d 946, u 18 e 0), k 0, time 181.1
* nlocs 6 'partial_decr5 LI0, partial_decr5 LI1, partial_decr5 LI2, partial_decr5 LI3, partial_decr5 LI4, partial_decr5 LP', invs 2943 (p 21 (k>0 0, lem>0 0, assumes>0 0 redun 485), d 2380, u 57 e 0), k 0, time 418.1
* nlocs 4 'partial_incr3 LI0, partial_incr3 LI1, partial_incr3 LI2, partial_incr3 LP', invs 464 (p 10 (k>0 0, lem>0 0, assumes>0 0 redun 98), d 351, u 5 e 0), k 0, time 45.5
* nlocs 5 'partial_incr4 LI0, partial_incr4 LI1, partial_incr4 LI2, partial_incr4 LI3, partial_incr4 LP', invs 1148 (p 15 (k>0 0, lem>0 0, assumes>0 0 redun 214), d 895, u 24 e 0), k 0, time 165.1
* nlocs 6 'partial_incr5 LI0, partial_incr5 LI1, partial_incr5 LI2, partial_incr5 LI3, partial_incr5 LI4, partial_incr5 LP', invs 2954 (p 21 (k>0 0, lem>0 0, assumes>0 0 redun 456), d 2406, u 71 e 0), k 0, time 405.6


$ grep "TIME AVG" tosem_results_all.txt 
TIME AVG 39.5 (../invgen/Traces/NLA_tosem/multilocs/l0/cohencu.l0.tcs)
TIME AVG 8.5 (../invgen/Traces/NLA_tosem/multilocs/l0/cohendiv.l0.tcs)
TIME AVG 31.4 (../invgen/Traces/NLA_tosem/multilocs/l0/dijkstra.l0.tcs)
TIME AVG 27.0 (../invgen/Traces/NLA_tosem/multilocs/l0/divbin.l0.tcs)
TIME AVG 53.9 (../invgen/Traces/NLA_tosem/multilocs/l0/euclidex1.l0.tcs)
TIME AVG 4.2 (../invgen/Traces/NLA_tosem/multilocs/l0/euclidex2.l0.tcs)
TIME AVG 8.2 (../invgen/Traces/NLA_tosem/multilocs/l0/euclidex3.l0.tcs)
TIME AVG 31.6 (../invgen/Traces/NLA_tosem/multilocs/l0/fermat1_new.l0.tcs)
TIME AVG 31.6 (../invgen/Traces/NLA_tosem/multilocs/l0/fermat2.l0.tcs)
TIME AVG 33.9 (../invgen/Traces/NLA_tosem/multilocs/l0/freire1.l0.tcs)
TIME AVG 45.1 (../invgen/Traces/NLA_tosem/multilocs/l0/freire2_comb.l0.tcs)
TIME AVG 14.8 (../invgen/Traces/NLA_tosem/multilocs/l0/geo1.l0.tcs)
TIME AVG 24.4 (../invgen/Traces/NLA_tosem/multilocs/l0/geo2.l0.tcs)
TIME AVG 23.4 (../invgen/Traces/NLA_tosem/multilocs/l0/geo3.l0.tcs)
TIME AVG 9.2 (../invgen/Traces/NLA_tosem/multilocs/l0/hard.l0.tcs)
TIME AVG 61.3 (../invgen/Traces/NLA_tosem/multilocs/l0/knuth.l0.tcs)
TIME AVG 8.7 (../invgen/Traces/NLA_tosem/multilocs/l0/lcm1.l0.tcs)
TIME AVG 11.5 (../invgen/Traces/NLA_tosem/multilocs/l0/lcm2.l0.tcs)
TIME AVG 23.1 (../invgen/Traces/NLA_tosem/multilocs/l0/mannadiv.l0.tcs)
TIME AVG 8.2 (../invgen/Traces/NLA_tosem/multilocs/l0/prod4br.l0.tcs)
TIME AVG 32.5 (../invgen/Traces/NLA_tosem/multilocs/l0/prodbin.l0.tcs)
TIME AVG 29.2 (../invgen/Traces/NLA_tosem/multilocs/l0/ps2.l0.tcs)
TIME AVG 27.9 (../invgen/Traces/NLA_tosem/multilocs/l0/ps3.l0.tcs)
TIME AVG 29.7 (../invgen/Traces/NLA_tosem/multilocs/l0/ps4.l0.tcs)
TIME AVG 30.2 (../invgen/Traces/NLA_tosem/multilocs/l0/ps5.l0.tcs)
TIME AVG 28.2 (../invgen/Traces/NLA_tosem/multilocs/l0/ps6.l0.tcs)
TIME AVG 39.6 (../invgen/Traces/NLA_tosem/multilocs/l0/sqrt1.l0.tcs)
TIME AVG 39.5 (../invgen/Traces/NLA_tosem/multilocs/l0/cohencu.l0.tcs)
TIME AVG 8.5 (../invgen/Traces/NLA_tosem/multilocs/l0/cohendiv.l0.tcs)
TIME AVG 31.4 (../invgen/Traces/NLA_tosem/multilocs/l0/dijkstra.l0.tcs)
TIME AVG 27.0 (../invgen/Traces/NLA_tosem/multilocs/l0/divbin.l0.tcs)
TIME AVG 53.9 (../invgen/Traces/NLA_tosem/multilocs/l0/euclidex1.l0.tcs)
TIME AVG 4.2 (../invgen/Traces/NLA_tosem/multilocs/l0/euclidex2.l0.tcs)
TIME AVG 8.2 (../invgen/Traces/NLA_tosem/multilocs/l0/euclidex3.l0.tcs)
TIME AVG 31.6 (../invgen/Traces/NLA_tosem/multilocs/l0/fermat1_new.l0.tcs)
TIME AVG 31.6 (../invgen/Traces/NLA_tosem/multilocs/l0/fermat2.l0.tcs)
TIME AVG 33.9 (../invgen/Traces/NLA_tosem/multilocs/l0/freire1.l0.tcs)
TIME AVG 45.1 (../invgen/Traces/NLA_tosem/multilocs/l0/freire2_comb.l0.tcs)
TIME AVG 14.8 (../invgen/Traces/NLA_tosem/multilocs/l0/geo1.l0.tcs)
TIME AVG 24.4 (../invgen/Traces/NLA_tosem/multilocs/l0/geo2.l0.tcs)
TIME AVG 23.4 (../invgen/Traces/NLA_tosem/multilocs/l0/geo3.l0.tcs)
TIME AVG 9.2 (../invgen/Traces/NLA_tosem/multilocs/l0/hard.l0.tcs)
TIME AVG 61.3 (../invgen/Traces/NLA_tosem/multilocs/l0/knuth.l0.tcs)
TIME AVG 8.7 (../invgen/Traces/NLA_tosem/multilocs/l0/lcm1.l0.tcs)
TIME AVG 11.5 (../invgen/Traces/NLA_tosem/multilocs/l0/lcm2.l0.tcs)
TIME AVG 23.1 (../invgen/Traces/NLA_tosem/multilocs/l0/mannadiv.l0.tcs)
TIME AVG 8.2 (../invgen/Traces/NLA_tosem/multilocs/l0/prod4br.l0.tcs)
TIME AVG 32.5 (../invgen/Traces/NLA_tosem/multilocs/l0/prodbin.l0.tcs)
TIME AVG 29.2 (../invgen/Traces/NLA_tosem/multilocs/l0/ps2.l0.tcs)
TIME AVG 27.9 (../invgen/Traces/NLA_tosem/multilocs/l0/ps3.l0.tcs)
TIME AVG 29.7 (../invgen/Traces/NLA_tosem/multilocs/l0/ps4.l0.tcs)
TIME AVG 30.2 (../invgen/Traces/NLA_tosem/multilocs/l0/ps5.l0.tcs)
TIME AVG 28.2 (../invgen/Traces/NLA_tosem/multilocs/l0/ps6.l0.tcs)
TIME AVG 39.6 (../invgen/Traces/NLA_tosem/multilocs/l0/sqrt1.l0.tcs)
TIME AVG 73.8 (../invgen/Traces/AES_tosem/multilocs/l0/AesDecrypt.l0.tcs)
TIME AVG 70.5 (../invgen/Traces/AES_tosem/multilocs/l0/AesEncrypt.l0.tcs)
TIME AVG 73.6 (../invgen/Traces/AES_tosem/multilocs/l0/AesKeySetupDec.l0.tcs)
TIME AVG 76.2 (../invgen/Traces/AES_tosem/multilocs/l0/AesKeySetupEnc.l0.tcs)
TIME AVG 4.1 (../invgen/Traces/AES_tosem/multilocs/l0/Block2State.l0.tcs)
TIME AVG 1.0 (../invgen/Traces/AES_tosem/multilocs/l0/InvMixColumns.l0.tcs)
TIME AVG 3.6 (../invgen/Traces/AES_tosem/multilocs/l0/InvShiftRows.l0.tcs)
TIME AVG 3.3 (../invgen/Traces/AES_tosem/multilocs/l0/InvSubBytes.l0.tcs)
TIME AVG 77.9 (../invgen/Traces/AES_tosem/multilocs/l0/KeyScheduleMod1.l0.tcs)
TIME AVG 79.5 (../invgen/Traces/AES_tosem/multilocs/l0/KeyScheduleMod2.l0.tcs)
TIME AVG 73.0 (../invgen/Traces/AES_tosem/multilocs/l0/KeySetupDec.l0.tcs)
TIME AVG 76.3 (../invgen/Traces/AES_tosem/multilocs/l0/KeySetupEnc.l0.tcs)
TIME AVG 76.4 (../invgen/Traces/AES_tosem/multilocs/l0/KeySetupEnc4.l0.tcs)
TIME AVG 78.8 (../invgen/Traces/AES_tosem/multilocs/l0/KeySetupEnc6.l0.tcs)
TIME AVG 79.3 (../invgen/Traces/AES_tosem/multilocs/l0/KeySetupEnc8.l0.tcs)
TIME AVG 1.0 (../invgen/Traces/AES_tosem/multilocs/l0/MixColumns.l0.tcs)
TIME AVG 0.5 (../invgen/Traces/AES_tosem/multilocs/l0/RotWord.l0.tcs)
TIME AVG 3.7 (../invgen/Traces/AES_tosem/multilocs/l0/ShiftRows.l0.tcs)
TIME AVG 4.2 (../invgen/Traces/AES_tosem/multilocs/l0/State2Block.l0.tcs)
TIME AVG 3.2 (../invgen/Traces/AES_tosem/multilocs/l0/SubBytes.l0.tcs)
TIME AVG 1.3 (../invgen/Traces/AES_tosem/multilocs/l0/SubWord.l0.tcs)
TIME AVG 3.2 (../invgen/Traces/AES_tosem/multilocs/l0/addroundkey.l0.tcs)
TIME AVG 3.5 (../invgen/Traces/AES_tosem/multilocs/l0/addroundkey_vn.l0.tcs)
TIME AVG 11.0 (../invgen/Traces/AES_tosem/multilocs/l0/mul.l0.tcs)
TIME AVG 0.8 (../invgen/Traces/AES_tosem/multilocs/l0/word_xor.l0.tcs)
TIME AVG 2.0 (../invgen/Traces/AES_tosem/multilocs/l0/word_xor_xor.l0.tcs)
TIME AVG 73.8 (../invgen/Traces/AES_tosem/multilocs/l0/AesDecrypt.l0.tcs)
TIME AVG 70.5 (../invgen/Traces/AES_tosem/multilocs/l0/AesEncrypt.l0.tcs)
TIME AVG 73.6 (../invgen/Traces/AES_tosem/multilocs/l0/AesKeySetupDec.l0.tcs)
TIME AVG 76.2 (../invgen/Traces/AES_tosem/multilocs/l0/AesKeySetupEnc.l0.tcs)
TIME AVG 4.1 (../invgen/Traces/AES_tosem/multilocs/l0/Block2State.l0.tcs)
TIME AVG 1.0 (../invgen/Traces/AES_tosem/multilocs/l0/InvMixColumns.l0.tcs)
TIME AVG 3.6 (../invgen/Traces/AES_tosem/multilocs/l0/InvShiftRows.l0.tcs)
TIME AVG 3.3 (../invgen/Traces/AES_tosem/multilocs/l0/InvSubBytes.l0.tcs)
TIME AVG 77.9 (../invgen/Traces/AES_tosem/multilocs/l0/KeyScheduleMod1.l0.tcs)
TIME AVG 79.5 (../invgen/Traces/AES_tosem/multilocs/l0/KeyScheduleMod2.l0.tcs)
TIME AVG 73.0 (../invgen/Traces/AES_tosem/multilocs/l0/KeySetupDec.l0.tcs)
TIME AVG 76.3 (../invgen/Traces/AES_tosem/multilocs/l0/KeySetupEnc.l0.tcs)
TIME AVG 76.4 (../invgen/Traces/AES_tosem/multilocs/l0/KeySetupEnc4.l0.tcs)
TIME AVG 78.8 (../invgen/Traces/AES_tosem/multilocs/l0/KeySetupEnc6.l0.tcs)
TIME AVG 79.3 (../invgen/Traces/AES_tosem/multilocs/l0/KeySetupEnc8.l0.tcs)
TIME AVG 1.0 (../invgen/Traces/AES_tosem/multilocs/l0/MixColumns.l0.tcs)
TIME AVG 0.5 (../invgen/Traces/AES_tosem/multilocs/l0/RotWord.l0.tcs)
TIME AVG 3.7 (../invgen/Traces/AES_tosem/multilocs/l0/ShiftRows.l0.tcs)
TIME AVG 4.2 (../invgen/Traces/AES_tosem/multilocs/l0/State2Block.l0.tcs)
TIME AVG 3.2 (../invgen/Traces/AES_tosem/multilocs/l0/SubBytes.l0.tcs)
TIME AVG 1.3 (../invgen/Traces/AES_tosem/multilocs/l0/SubWord.l0.tcs)
TIME AVG 3.2 (../invgen/Traces/AES_tosem/multilocs/l0/addroundkey.l0.tcs)
TIME AVG 3.5 (../invgen/Traces/AES_tosem/multilocs/l0/addroundkey_vn.l0.tcs)
TIME AVG 11.0 (../invgen/Traces/AES_tosem/multilocs/l0/mul.l0.tcs)
TIME AVG 0.8 (../invgen/Traces/AES_tosem/multilocs/l0/word_xor.l0.tcs)
TIME AVG 2.0 (../invgen/Traces/AES_tosem/multilocs/l0/word_xor_xor.l0.tcs)
TIME AVG 53.8 (../../git/invgen/Traces/NLA_tosem/multilocs/l0/knuth.l0.tcs)
TIME AVG 53.8 (../../git/invgen/Traces/NLA_tosem/multilocs/l0/knuth.l0.tcs)
Fermat-2 Sun Jul 06:10:51:55 (20992) ~/Dropbox/git/dig/results 

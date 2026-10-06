/*
 * Purpose: Compute a row of binomial coefficients using the multiplicative recurrence.
 * Sources: NIST Digital Library of Mathematical Functions, equation 26.3.6.
 * https://dlmf.nist.gov/26.3#E6
 * Provenance: C benchmark adaptation created for the DIG NLA-mosaic suite.
 *
 * Expected invariants at every vtrace1 call (mathematical notation):
 *   k*c-(N-k+1)*prev == 0 (degree 2 search cap).
 *   ** denotes exponentiation, not C syntax.
 * Domain: mainQ arguments, in order, range over [[0, 20]].
 * Arithmetic: bounded C integers.
 * Notes: Start (k,c,prev)=(0,1,0). c=binomial(N,k); prev holds the preceding coefficient.
 * Division is exact on reachable states and follows multiplication.
 */
#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int N, int k, int c, int prev){}

int mainQ(int N){
    vassume(N >= 0 && N <= 20);
    if (N < 0 || N > 20) return 0;
    int k = 0, c = 1, prev = 0;
    while (1){
        // assert(k*c-(N-k+1)*prev == 0);
        vtrace1(N, k, c, prev);
        if (!(k < N)) break;
        prev = c;
        k++;
        c = prev*(N-k+1)/k;
    }
    return 0;
}

int main(int argc, char **argv){
    if (argc != 2) return 1;
    return mainQ(atoi(argv[1]));
}

/*
 * Purpose: Evaluate first-kind T_n(t) together with second-kind U_(n-1)(t).
 * Sources: NIST Digital Library of Mathematical Functions, section 18.5. https://dlmf.nist.gov/18.5
 * Provenance: C benchmark adaptation created for the DIG NLA-mosaic suite.
 *
 * Expected invariants at every vtrace1 call (mathematical notation):
 *   T**2-(t**2-1)*U**2-1 == 0 (degree 4 search cap).
 *   ** denotes exponentiation, not C syntax.
 * Domain: mainQ arguments, in order, range over [[0, 8], [-3, 3]].
 * Arithmetic: bounded C integers.
 * Notes: Start (T,U)=(1,0), interpreting U_-1=0. t is an immutable input, so the conserved
 * relation has degree 4. Our paired update and identity are derived from the definitions.
 */
#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int T, int U, int t){}

int mainQ(int n, int t){
    vassume(n >= 0 && n <= 8);
    vassume(t >= -3 && t <= 3);
    if (n < 0 || n > 8 || t < -3 || t > 3) return 0;
    int T = 1, U = 0, i = 0;
    while (1){
        // assert(T*T-(t*t-1)*U*U == 1);
        vtrace1(T, U, t);
        if (!(i < n)) break;
        int nextT = t*T + (t*t-1)*U;
        int nextU = T + t*U;
        T = nextT;
        U = nextU;
        i++;
    }
    return 0;
}

int main(int argc, char **argv){
    if (argc != 3) return 1;
    return mainQ(atoi(argv[1]), atoi(argv[2]));
}

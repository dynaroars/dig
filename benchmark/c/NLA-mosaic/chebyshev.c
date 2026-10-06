/*
 * Purpose: Evaluate consecutive first-kind Chebyshev polynomials by their three-term recurrence.
 * Sources: NIST Digital Library of Mathematical Functions, sections 18.5 and 18.9.
 * https://dlmf.nist.gov/18.5 ; https://dlmf.nist.gov/18.9
 * Provenance: C benchmark adaptation created for the DIG NLA-mosaic suite.
 *
 * Expected invariants at every vtrace1 call (mathematical notation):
 *   a**2+b**2-2*t*a*b-1+t**2 == 0 (degree 3 search cap).
 *   ** denotes exponentiation, not C syntax.
 * Domain: mainQ arguments, in order, range over [[0, 8], [-3, 3]].
 * Arithmetic: bounded C integers.
 * Notes: Start (a,b)=(1,t). t is an immutable input, so the conserved relation has degree 3. The
 * displayed identity is derived from the recurrence.
 */
#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int a, int b, int t){}

int mainQ(int n, int t){
    vassume(n >= 0 && n <= 8);
    vassume(t >= -3 && t <= 3);
    if (n < 0 || n > 8 || t < -3 || t > 3) return 0;
    int a = 1, b = t, i = 0;
    while (1){
        // assert(a*a+b*b-2*t*a*b-1+t*t == 0);
        vtrace1(a, b, t);
        if (!(i < n)) break;
        int nb = 2*t*b - a;
        a = b;
        b = nb;
        i++;
    }
    return 0;
}

int main(int argc, char **argv){
    if (argc != 3) return 1;
    return mainQ(atoi(argv[1]), atoi(argv[2]));
}

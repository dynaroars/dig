/*
 * Purpose: Generate consecutive Fibonacci numbers, exposing Cassini's alternating determinant.
 * Sources: Polar documentation, Fibonacci loop and quartic invariant.
 * https://github.com/probing-lab/polar#introduction
 * Provenance: C benchmark adaptation created for the DIG NLA-mosaic suite.
 *
 * Expected invariants at every vtrace1 call (mathematical notation):
 *   (a**2+a*b-b**2)**2-1 == 0 (degree 4 search cap).
 *   ** denotes exponentiation, not C syntax.
 * Domain: mainQ arguments, in order, range over [[0, 30]].
 * Arithmetic: bounded C integers.
 * Notes: Initialize (a,b)=(0,1). The quadratic a^2+a*b-b^2 alternates signs; its square is
 * constant.
 */
#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int a, int b){}

int mainQ(int n){
    vassume(n >= 0 && n <= 30);
    if (n < 0 || n > 30) return 0;
    int a = 0, b = 1, i = 0;
    while (1){
        // assert((a*a + a*b - b*b)*(a*a + a*b - b*b) == 1);
        vtrace1(a, b);
        if (!(i < n)) break;
        int next = a + b;
        a = b;
        b = next;
        i++;
    }
    return 0;
}

int main(int argc, char **argv){
    if (argc != 2) return 1;
    return mainQ(atoi(argv[1]));
}

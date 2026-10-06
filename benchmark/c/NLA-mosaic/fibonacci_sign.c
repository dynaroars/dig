/*
 * Purpose: Generate consecutive Fibonacci numbers and explicitly track Cassini's sign.
 * Sources: Polar documentation, Fibonacci loop and quartic invariant; this sign-variable variant
 * is our adaptation. https://github.com/probing-lab/polar#introduction
 * Provenance: C benchmark adaptation created for the DIG NLA-mosaic suite.
 *
 * Expected invariants at every vtrace1 call (mathematical notation):
 *   a**2+a*b-b**2-sign == 0 (degree 2 search cap).
 *   ** denotes exponentiation, not C syntax.
 * Domain: mainQ arguments, in order, range over [[0, 30]].
 * Arithmetic: bounded C integers.
 * Notes: Initialize (a,b,sign)=(0,1,-1); negate sign each iteration. Also sign^2=1.
 */
#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int a, int b, int sign){}

int mainQ(int n){
    vassume(n >= 0 && n <= 30);
    if (n < 0 || n > 30) return 0;
    int a = 0, b = 1, sign = -1, i = 0;
    while (1){
        // assert(a*a + a*b - b*b == sign);
        vtrace1(a, b, sign);
        if (!(i < n)) break;
        int next = a + b;
        a = b;
        b = next;
        sign = -sign;
        i++;
    }
    return 0;
}

int main(int argc, char **argv){
    if (argc != 2) return 1;
    return mainQ(atoi(argv[1]));
}

/*
 * Purpose: Generate successive positive Pell-equation solutions by multiplication by 3+2*sqrt(2).
 * Sources: Keith Conrad, Pell's Equation I, section 4, New Solutions from Old Solutions.
 * https://kconrad.math.uconn.edu/blurbs/ugradnumthy/pelleqn1.pdf
 * Provenance: C benchmark adaptation created for the DIG NLA-mosaic suite.
 *
 * Expected invariants at every vtrace1 call (mathematical notation):
 *   x**2-2*y**2-1 == 0 (degree 2 search cap).
 *   ** denotes exponentiation, not C syntax.
 * Domain: mainQ arguments, in order, range over [[0, 10]].
 * Arithmetic: bounded C integers.
 * Notes: Initialize (x,y)=(1,0). All updates use the old state.
 */
#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int x, int y){}

int mainQ(int n){
    vassume(n >= 0 && n <= 10);
    if (n < 0 || n > 10) return 0;
    int x = 1, y = 0, i = 0;
    while (1){
        // assert(x*x - 2*y*y == 1);
        vtrace1(x, y);
        if (!(i < n)) break;
        int nx = 3*x + 4*y;
        int ny = 2*x + 3*y;
        x = nx;
        y = ny;
        i++;
    }
    return 0;
}

int main(int argc, char **argv){
    if (argc != 2) return 1;
    return mainQ(atoi(argv[1]));
}

/*
 * Purpose: Generate Pythagorean triples by following the three Berggren matrix branches.
 * Sources: Keith Conrad, Pythagorean Descent, equation (1.1).
 * https://kconrad.math.uconn.edu/blurbs/linmultialg/descentPythag.pdf
 * Provenance: C benchmark adaptation created for the DIG NLA-mosaic suite.
 *
 * Expected invariants at every vtrace1 call (mathematical notation):
 *   a**2+b**2-c**2 == 0 (degree 2 search cap).
 *   ** denotes exponentiation, not C syntax.
 * Domain: mainQ arguments, in order, range over [[0, 8], [0, 6560]].
 * Arithmetic: bounded C integers.
 * Notes: Start at (3,4,5). Our input path encodes branch choices as base-3 digits; each branch
 * uses old-state temporaries.
 */
#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int a, int b, int c){}

int mainQ(int n, int path){
    vassume(n >= 0 && n <= 8);
    vassume(path >= 0 && path <= 6560);
    if (n < 0 || n > 8 || path < 0 || path > 6560) return 0;
    int a = 3, b = 4, c = 5, i = 0;
    while (1){
        // assert(a*a + b*b == c*c);
        vtrace1(a, b, c);
        if (!(i < n)) break;
        int choice = path % 3;
        int na, nb, nc;
        path = path / 3;
        if (choice == 0){
            na = a - 2*b + 2*c;
            nb = 2*a - b + 2*c;
            nc = 2*a - 2*b + 3*c;
        } else if (choice == 1){
            na = -a + 2*b + 2*c;
            nb = -2*a + b + 2*c;
            nc = -2*a + 2*b + 3*c;
        } else {
            na = a + 2*b + 2*c;
            nb = 2*a + b + 2*c;
            nc = 2*a + 2*b + 3*c;
        }
        a = na;
        b = nb;
        c = nc;
        i++;
    }
    return 0;
}

int main(int argc, char **argv){
    if (argc != 3) return 1;
    return mainQ(atoi(argv[1]), atoi(argv[2]));
}

/*
 * Purpose: Iterate the Nagata polynomial automorphism, whose expanded x update has degree 5.
 * Sources: (Un)Solvable Loop Analysis (2024), Example 43, nagata.
 * https://doi.org/10.1007/s10703-024-00455-0
 * Provenance: C benchmark adaptation created for the DIG NLA-mosaic suite.
 *
 * Expected invariants at every vtrace1 call (mathematical notation):
 *   x*z+y**2-constant == 0 (degree 2 search cap).
 *   ** denotes exponentiation, not C syntax.
 * Domain: mainQ arguments, in order, range over [[0, 6], [-2, 2], [-2, 2], [-2, 2]].
 * Arithmetic: bounded C integers.
 * Notes: Our adaptation accepts bounded initial coordinates and stores x0*z0+y0^2 as constant. z
 * is unchanged, but z0 is not part of vtrace1.
 */
#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int x, int y, int z, int constant){}

int mainQ(int n, int x0, int y0, int z0){
    vassume(n >= 0 && n <= 6);
    vassume(x0 >= -2 && x0 <= 2);
    vassume(y0 >= -2 && y0 <= 2);
    vassume(z0 >= -2 && z0 <= 2);
    if (n < 0 || n > 6 || x0 < -2 || x0 > 2 || y0 < -2 || y0 > 2 || z0 < -2 || z0 > 2) return 0;
    int x = x0, y = y0, z = z0, i = 0;
    int constant = x0*z0 + y0*y0;
    while (1){
        // assert(x*z+y*y == constant);
        vtrace1(x, y, z, constant);
        if (!(i < n)) break;
        int d = x*z + y*y;
        int nx = x - 2*y*d - z*d*d;
        int ny = y + z*d;
        x = nx;
        y = ny;
        i++;
    }
    return 0;
}

int main(int argc, char **argv){
    if (argc != 5) return 1;
    return mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]), atoi(argv[4]));
}

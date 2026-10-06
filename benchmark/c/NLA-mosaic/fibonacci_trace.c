/*
 * Purpose: Iterate the Fibonacci trace map (x,y,z) -> (y,z,2*y*z-x).
 * Sources: (Un)Solvable Loop Analysis (2024), Example 36, fib1.
 * https://doi.org/10.1007/s10703-024-00455-0
 * Provenance: C benchmark adaptation created for the DIG NLA-mosaic suite.
 *
 * Expected invariants at every vtrace1 call (mathematical notation):
 *   x**2+y**2+z**2-2*x*y*z-constant == 0 (degree 3 search cap).
 *   ** denotes exponentiation, not C syntax.
 * Domain: mainQ arguments, in order, range over [[0, 5], [-2, 2], [-2, 2], [-2, 2]].
 * Arithmetic: bounded C integers.
 * Notes: Our adaptation accepts bounded initial coordinates and stores their initial conserved
 * polynomial as constant.
 */
#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int x, int y, int z, int constant){}

int mainQ(int n, int x0, int y0, int z0){
    vassume(n >= 0 && n <= 5);
    vassume(x0 >= -2 && x0 <= 2);
    vassume(y0 >= -2 && y0 <= 2);
    vassume(z0 >= -2 && z0 <= 2);
    if (n < 0 || n > 5 || x0 < -2 || x0 > 2 || y0 < -2 || y0 > 2 || z0 < -2 || z0 > 2) return 0;
    int x = x0, y = y0, z = z0, i = 0;
    int constant = x0*x0 + y0*y0 + z0*z0 - 2*x0*y0*z0;
    while (1){
        // assert(x*x + y*y + z*z - 2*x*y*z == constant);
        vtrace1(x, y, z, constant);
        if (!(i < n)) break;
        int nz = 2*y*z - x;
        x = y;
        y = z;
        z = nz;
        i++;
    }
    return 0;
}

int main(int argc, char **argv){
    if (argc != 5) return 1;
    return mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]), atoi(argv[4]));
}

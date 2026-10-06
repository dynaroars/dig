/*
 * Purpose: Walk the Markov-triple tree by alternating two mutation/permutation branches.
 * Sources: (Un)Solvable Loop Analysis, Formal Methods in System Design (2024), Example 39,
 * markov-triples-toggle. https://doi.org/10.1007/s10703-024-00455-0
 * Provenance: C benchmark adaptation created for the DIG NLA-mosaic suite.
 *
 * Expected invariants at every vtrace1 call (mathematical notation):
 *   x**2+y**2+z**2-3*x*y*z == 0 (degree 3 search cap).
 *   ** denotes exponentiation, not C syntax.
 * Domain: mainQ arguments, in order, range over [[0, 12], [0, 3], [0, 1]].
 * Arithmetic: bounded C integers.
 * Notes: Our adaptation accepts four valid initial triples and either starting branch. A
 * coordinate guard stops growth before C updates overflow.
 */
#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int x, int y, int z){}

int mainQ(int n, int seed, int branch){
    vassume(n >= 0 && n <= 12);
    vassume(seed >= 0 && seed <= 3);
    vassume(branch >= 0 && branch <= 1);
    if (n < 0 || n > 12 || seed < 0 || seed > 3 || branch < 0 || branch > 1) return 0;
    int x = 1, y = 1, z = 2, i = 0;
    if (seed == 1){ y = 2; z = 5; }
    else if (seed == 2){ x = 2; y = 5; z = 29; }
    else if (seed == 3){ y = 5; z = 13; }
    while (1){
        // assert(x*x + y*y + z*z - 3*x*y*z == 0);
        vtrace1(x, y, z);
        if (!(i < n)) break;
        /* Each product in the next update is at most 3*10000*10000. */
        if (x > 10000 || y > 10000 || z > 10000) break;
        if (branch == 0){
            int ny = 3*x*y - z;
            z = y;
            y = ny;
            branch = 1;
        } else {
            int ny = 3*y*z - x;
            x = y;
            y = ny;
            branch = 0;
        }
        i++;
    }
    return 0;
}

int main(int argc, char **argv){
    if (argc != 4) return 1;
    return mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]));
}

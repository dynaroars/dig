/*
 * Purpose: Compute continued-fraction convergents with changing partial quotients.
 * Sources: F. Al-Faisal, Elementary Number Theory, Proposition 30.7.
 * https://math.uwaterloo.ca/~f2alfais/notes/pm340-notes.pdf
 * Provenance: C benchmark adaptation created for the DIG NLA-mosaic suite.
 *
 * Expected invariants at every vtrace1 call (mathematical notation):
 *   (p*s-r*q)**2-1 == 0 (degree 4 search cap).
 *   ** denotes exponentiation, not C syntax.
 * Domain: mainQ arguments, in order, range over [[0, 8], [0, 6560]].
 * Arithmetic: bounded C integers.
 * Notes: Start (p,r,q,s)=(1,0,0,1). Our path digits select partial quotients 1,2,3. p*s-r*q
 * alternates +1/-1.
 */
#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int p, int r, int q, int s){}

int mainQ(int n, int path){
    vassume(n >= 0 && n <= 8);
    vassume(path >= 0 && path <= 6560);
    if (n < 0 || n > 8 || path < 0 || path > 6560) return 0;
    int p = 1, r = 0, q = 0, s = 1, i = 0;
    while (1){
        // assert((p*s-r*q)*(p*s-r*q) == 1);
        vtrace1(p, r, q, s);
        if (!(i < n)) break;
        int t = path % 3 + 1;
        int np = t*p + r;
        int nq = t*q + s;
        path = path / 3;
        r = p;
        s = q;
        p = np;
        q = nq;
        i++;
    }
    return 0;
}

int main(int argc, char **argv){
    if (argc != 3) return 1;
    return mainQ(atoi(argv[1]), atoi(argv[2]));
}

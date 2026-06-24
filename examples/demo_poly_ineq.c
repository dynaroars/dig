/*
 * Demo: Polynomial Inequality Invariants
 *
 * The loop splits N into two complementary parts x and y (x + y == N).
 * The invariant  x * y <= N * N / 4  holds by AM-GM, but DIG can also
 * discover the tighter empirical bound  x * y <= POLY_IUPPER  directly
 * from traces as a degree-2 polynomial inequality.
 *
 * Run:
 *   python3 -O dig.py examples/demo_poly_ineq.c
 *
 * Expected new invariants (in addition to the standard ones):
 *   x*y <= <bound>           (PolyIneq)
 *   x*N <= <bound>           (PolyIneq)
 */
#include <stdio.h>
#include <stdlib.h>

void vassume(int b) {}
void vtrace1(int x, int y, int N) {}

int mainQ(int N) {
    vassume(N >= 2 && N <= 100);

    int x = 0;
    int y = N;

    while (1) {
        vtrace1(x, y, N);
        if (!(x <= y))
            break;
        x++;
        y--;
    }
    return x;
}

void main(int argc, char **argv) {
    mainQ(atoi(argv[1]));
}

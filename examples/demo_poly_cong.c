/*
 * Demo: Polynomial Congruence Invariants
 *
 * The variable `a` is always a power of 2 (doubles each iteration):
 *   1, 2, 4, 8, 16, ...
 *
 * Since 2^k mod 3 cycles 1, 2, 1, 2, ..., we get a^2 mod 3 == 1 always
 * (because 1^2 ≡ 1 and 2^2 ≡ 1 mod 3).  Also a*s has a modular pattern.
 *
 * DIG discovers these as degree-2 polynomial congruences:
 *   a**2 === 1 (mod 3)
 *   a**2 === 0 (mod 4)    for a >= 2
 *   a*s  === 0 (mod ...)
 *
 * Run:
 *   python3 -O dig.py examples/demo_poly_cong.c
 *
 * Expected new invariants (PolyCong):
 *   a**2 === 1 (mod 3)
 *   a**2 === 0 (mod 4)    (once a >= 2)
 *   s*a  === 0 (mod <n>)
 */
#include <stdio.h>
#include <stdlib.h>

void vassume(int b) {}
void vtrace1(int a, int s, int k) {}

int mainQ(int n) {
    vassume(n >= 1 && n <= 30);

    int a = 1;   /* always a power of 2 */
    int s = 0;   /* sum of powers of 2  */
    int k = 0;

    while (1) {
        vtrace1(a, s, k);
        if (!(k < n))
            break;
        s = s + a;
        a = a + a;   /* double a */
        k++;
    }
    return s;
}

void main(int argc, char **argv) {
    mainQ(atoi(argv[1]));
}

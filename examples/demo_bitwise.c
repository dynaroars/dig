/*
 * Demo: Bitwise Invariants
 *
 * The loop counts up in steps of 4, so x is always a multiple of 4.
 * y accumulates x values, so y is also always a multiple of 4.
 * DIG discovers:
 *   x & 3 == 0    (x is always divisible by 4)
 *   y & 3 == 0    (y is always divisible by 4)
 *
 * Additionally, s holds partial sums of powers-of-2-aligned values;
 * the bitwise pattern is captured exactly by the mask invariant.
 *
 * Run:
 *   python3 -O dig.py examples/demo_bitwise.c
 *
 * Expected new invariants:
 *   x & <mask> == 0      (PolyIneq / Bitwise)
 *   y & <mask> == 0      (Bitwise)
 */
#include <stdio.h>
#include <stdlib.h>

void vassume(int b) {}
void vtrace1(int x, int y, int n) {}

int mainQ(int n) {
    vassume(n >= 1 && n <= 50);

    int x = 0;
    int y = 0;

    while (1) {
        vtrace1(x, y, n);
        if (!(x < n * 4))
            break;
        x += 4;
        y += x;
    }
    return y;
}

void main(int argc, char **argv) {
    mainQ(atoi(argv[1]));
}

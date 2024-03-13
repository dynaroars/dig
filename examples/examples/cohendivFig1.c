#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

void vassume(int b){}
void vtrace1(int q, int r, int a, int b, int x, int y){}
void vtrace2(int q, int r, int a, int b, int x, int y){}

int cohendiv (int x, int y) {
    assert(x >= 0 && y >= 1);
    int q = 0;
    int r = x;
    int a;
    int b;
    while (r >= y) {
        a=1;
        b=y;
        vtrace1(x, y, q, r, a, b);
        while (r >= 2*b) {
            a = 2*a;
            b = 2*b;
        }
        r = r-b;
        q = q+a;
        }

        vtrace2(x, y, q, r, a, b);
        return q;
    }

void main(int argc, char **argv){
    cohendiv(atoi(argv[1]), atoi(argv[2]));
}


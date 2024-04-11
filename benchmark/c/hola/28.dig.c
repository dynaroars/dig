#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace(int y, int n){}


void mainQ(int u) {
    vassume(u > 0);
    int x = 0;
    int y = 0;
    int n = 0;
    int i0 = 0;

    while (i0 < u) {
	x++;
	y++;
	i0++;
    }

    while (x != n) {
	x--;
	y--;
    }
    vtrace(y, n);
    //assert(y == n);
}

void main(int argc, char *argv[]) {
    mainQ(atoi(argv[1]));
}

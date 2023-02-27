#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace(int x, int y, int z){}


void mainQ(int u1) {
    vassume(u1 > 0);
    int x = 0;
    int y = 0;
    int z = 0;
    int k = 0;
    int i0 = 0;

    while (i0 < u1) {
	i0++;
	if (k % 3 == 0) x++;
	y++;
	z++;
	k = x + y + z;
    }

    vtrace(x, y, z);
    //assert(x == y);
    //assert(y == z);
}

void main(int argc, char *argv[]) {
    mainQ(atoi(argv[1]));
}

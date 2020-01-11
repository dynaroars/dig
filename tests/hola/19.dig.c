#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace(int y, int n){}


void mainQ(int m, int n) {
    vassume(n >= 0);
    vassume(m >= 0);
    vassume(m < n);

    int x = 0;
    int y = m;

    while (x < n) {
	x++;
	if (x > m) y++;
    }

    vtrace(y, n);
    //assert(y == n);
}

void main(int argc, char *argv[]) {
    mainQ(atoi(argv[1]), atoi(argv[2]));
}

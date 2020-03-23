#include <stdio.h>
#include <stdlib.h>
void vassume(int b){}
void vtrace(int i, int j){}


void mainQ(int flag, int n) {
    vassume(n > 0);
    int j = 0;
    int i = 0;
    int x = 0;
    int y = 0;
    int u = 0;

    while (u < n) {
	u++;
	x++;
	y++;
	i += x;
	j += y;
	if (flag != 0) j += 1;
    }
    vtrace(i,j);
    //assert(j >= i);
}

void main(int argc, char *argv[]) {
    mainQ(atoi(argv[1]), atoi(argv[2]));
}

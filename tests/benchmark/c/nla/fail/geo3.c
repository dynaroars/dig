#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}

void vtrace1(int x, int y, int z, int a, int k){}

int mainQ(int z, int a, int k){
    vassume(z >= 0);
    vassume(z <= 10);
    vassume(k > 0);
    vassume(k <= 10); 

    int x = a; int y = 1;  int c = 1;

    while (1){
	//assert(z*x-x+a-a*z*y == 0);
	vtrace1(x, y, z, a, k);

	if (!(c < k)) break;
	c = c + 1;
	x = x*z + a;
	y = y*z;

    }
    return x;
}


void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]));
}


#include <stdio.h>
#include <stdlib.h>

void vtrace1(int a, int n, int x, int y, int z){}

int mainQ(int a){
    int n,x,y,z;

    n=0; x=0; y=1; z=6;

    while(1){
	//assert(z == 6*n + 6);
	//assert(y == 3*n*n + 3*n + 1);
	//assert(x == n*n*n);
	vtrace1(a, n, x, y, z);
       
	if(!(n<=a)) break;
	//write_int(x);
       
	n=n+1;
	x=x+y;
	y=y+z;
	z=z+6;
    }
    return x;
}


void main(int argc, char **argv){
    mainQ(atoi(argv[1]));
}


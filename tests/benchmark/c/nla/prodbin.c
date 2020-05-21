#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int a, int b, int x, int y, int z){}
void vtrace2(int a, int b, int x, int z){}

int mainQ(int a, int b){
    vassume(a >= 0);
    vassume(b >= 0);

    int x,y,z;
    x = a;
    y = b;
    z = 0;

    while(1) { 
	//assert(z+x*y==a*b);
	//%%%traces: int a, int b, int x, int y, int z
	vtrace1(a, b, x, y, z);
	if(!(y!=0)) break;
	  
	if (y%2 ==1 ){
	    z = z+x;
	    y = y-1;
	}
	x = 2*x;
	y = y/2;

    }
    vtrace2(a, b, x, z);
    //assert(z == a*b);
    return z; 

}


void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}


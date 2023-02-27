#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int x, int y, int z, int k){}
void vtrace2(int x, int y, int z, int k){}

int mainQ(int z, int k){
    vassume(z >= 0);
    vassume(z <= 10);
    vassume(k >= 0);
    vassume(k <= 10);
	    
    int x = 1; int y = z; int c = 1;

    while (1){
	//assert(x*z - x - y + 1 == 0);
	//%%%traces: int x, int y, int z, int k
	vtrace1(x, y, z, k);
	if(!(c < k)) break;
	  
	c = c + 1;
	x = x*z + 1;
	y = y*z;

    }//geo1

    x = x *(z - 1);
    vtrace2(x, y, z, k);
    return x;
}


void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));

}


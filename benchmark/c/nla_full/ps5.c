#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int x, int y, int k){}
void vtrace2(int x, int y, int k){}

int mainQ(int k){
    vassume(k <= 30); //if too large then will cause overflow
    
    int y = 0;
    int x = 0;
    int c = 0;

    while(1){
	//assert(6*y*y*y*y*y + 15*y*y*y*y+ 10*y*y*y - 30*x - y == 0);
	vtrace1(x, y, k);
	if (!(c < k)) break;
	c = c +1 ;
	y=y +1;
	x=y*y*y*y+x;
    }
    vtrace2(x, y, k);
    return x;
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]));
}


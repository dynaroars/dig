#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int x, int y, int k){}

int mainQ(int k){
    //vassume(k>=0);
    //vassume(k<=30);
     
    int y = 0;
    int x = 0;
    int c = 0;


    while(1){
	//assert(6*x-2*y*y*y-3*y*y-y == 0);	  
	vtrace1(x, y, k);

	if (!(c < k)) break;    
	c = c +1 ;
	y=y +1;
	x=y*y+x;
    }
    return x;
}



void main(int argc, char **argv){
    mainQ(atoi(argv[1]));
}


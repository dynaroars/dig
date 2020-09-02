#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int x, int y, int k){}

int mainQ(int k){
    vassume(k >= 0);
    vassume(k< = 30); //if too large then overflow
     
    int y = 0;
    int x = 0;
    int c = 0;


    while(1){
	//assert(-2*pow(y,6) - 6*pow(y,5) - 5*pow(y,4) + pow(y,2) + 12*x == 0.0); //DIG Generated  (but don't uncomment, assertion will fail because of int overflow)	  

	vtrace1(x, y, k);

	if (!(c < k)) break;
	c = c + 1 ;
	y = y + 1;
	x=y*y*y*y*y+x;
    }
    return x;
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]));
}


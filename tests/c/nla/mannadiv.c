#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int q, int a, int b, int x, int y){}  
void vtrace2(int q, int a, int x, int y){}

int mainQ(int x, int y){
     
    vassume(x >= 0);
    vassume(y != 0);
     
    int q, a, b; 
    q = 0;
    a = 0;
    b = x;

    while(1) {
	//assert(q* y + a + b == x);
	vtrace1(q, a, b, x, y);
	if(!(b != 0)) break;
	  
	if (a + 1 == y) {
	    q = q + 1;
	    a = 0;
	    b = b - 1;
	}
	else {
	    a = a + 1;
	    b = b - 1;
	}
    }
    vtrace2(q, a, x, y); 
    //assert(q == x / y);
    return q;
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}


#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int A, int B, int q, int b, int r){}
void vtrace2(int A, int B, int q, int b, int r){}

int mainQ(int A, int B){
    vassume(B >= 1);
    //vassume(A > 0 && B > 0);
 
    int q = 0;
    int r = A;
    int b = B;

    while(1){
	vtrace1(A, B, q, b, r);
	if (!(r>=b)) break;
	b=2*b;
    }


    while(1){
	//assert(A == q*b + r && r >= 0);
	vtrace2(A, B, q, b, r);
	if (!(b!=B)) break;
	  
	q = 2*q;
	b = b/2;
	if (r >= b) {
	    q = q + 1;
	    r = r - b;
	}
    }
    //vtrace3(A, B, q, b, r);
    return q;
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}


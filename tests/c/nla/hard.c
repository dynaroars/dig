#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int A, int B, int q, int r, int d, int p){}
void vtrace2(int A, int B, int q, int r, int d, int p){}
void vtrace3(int A, int B, int q, int r, int d){}

int mainQ(int A, int B){
    vassume(B >= 1);

    int r,d,p,q;

    r=A;
    d=B;
    p=1;
    q=0;

    while(1){
	//%%%traces: int A, int B, int q, int r, int d, int p
	vtrace1(A, B, q, r, d, p);
	if (!(r >= d)) break;
	//assert(A >= 0 && B > 0 && q == 0 && r == A && d == B*p);
	d = 2 * d;
	p  = 2 * p;
    }

    while(1){
	// assert(A == q*B+r && d==B*p);
	vtrace2(A, B, q, r, d, p);
	if (!(p!=1)) break;
    
	d = d / 2;
	p = p / 2;
	if(r >= d){
	    r = r - d;
	    q = q + p;
	}
    }

    vtrace3(A, B, q, r, d);
    return q;
}


void  main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}


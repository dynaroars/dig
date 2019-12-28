#include <stdio.h>
#include <assert.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int a, int b, int p, int q, int r, int s, int x, int y){}
void vtrace2(int a, int b, int p, int q, int r, int s, int x, int y){}
void vtrace3(int a, int b, int p, int q, int r, int s, int x, int y){}

int mainQ(int x, int y){
    vassume(x >= 1);
    vassume(y >= 1);
     
    int a,b,p,q,r,s;

    a=x;
    b=y;
    p=1;
    q=0;
    r=0; 
    s=1;

    while(1) {
	vtrace1(a, b, p, q, r, s, x, y);
	if(!(b!=0)) break;
	int c,k;
	c=a;
	k=0;

	while(1){
	    //assert(a == k*b+c);
	    //assert(a == y*r+x*p);
	    //assert(b == x*q+y*s);
	    vtrace2(a, b, p, q, r, s, x, y);
	    if(!( c>=b )) break;
	    c=c-b;
	    k=k+1;
	}

	a=b;
	b=c;

	int temp;
	temp=p;
	p=q;
	q=temp-q*k;
	temp=r;
	r=s;
	s=temp-s*k;
    }
    
    vtrace3(a, b, p, q, r, s, x, y);
    return a;
}


void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}


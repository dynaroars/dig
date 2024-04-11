#include <stdio.h>
#include <stdlib.h> 

void vassume(int b){}
void vtrace1(int r, int p, int n, int q, int h){}
void vtrace2(int r, int p, int n, int q, int h){}
void vtrace3(int r, int p, int n, int h){}

int mainQ(int n){
    vassume(n >= 0);
    int p,q,r,h;
    p = 0;
    q = 1;
    r = n;
    h = 0;
    while (1){
	vtrace1(r, p, n, q, h);
	if(!(q<=n)) break;
	q=4*q;
	//assert(   n >= 0   &&   p == 0   &&   r==n );
    }
    //q = 4^n
     
    while (1){
	vtrace2(r, p, n, q, h);	
	//assert(r < 2*p + q);
	//assert(p*p + r*q == n*q);
	//assert((h*h*h) - 12*h*n*q + 16*n*p*q - h*(q*q) - 4*p*(q*q) + 12*h*q*r - 16*p*q*r == 0);
	//assert((h*h)*n - 4*h*n*p + 4*(n*n)*q - n*(q*q) - (h*h)*r + 4*h*p*r - 8*n*q*r + (q*q)*r + 4*q*(r*r) == 0);
	//assert((h*h)*p - 4*h*n*q + 4*n*p*q - p*(q*q) + 4*h*q*r - 4*p*q*r == 0 u, (p*p) - n*q + q*r == 0);
	if(!(q!=1)) break;
			   
	q=q/4;
	h=p+q;
	p=p/2;
	if (r>=h){
	    p=p+q;
	    r=r-h;
	} 
    }
    vtrace3(r, p, n, h);	
    return p;
}


void main(int argc, char **argv){
    mainQ(atoi(argv[1]));
}


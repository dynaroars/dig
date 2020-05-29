#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int x, int y, int a, int b, int p, int r, int q, int s){}

int mainQ(int x, int y){
    vassume(x >= 1);
    vassume(y >= 1);
    
    int a,b,p,q,r,s;
    
    a = x;
    b = y;
    p = 1;
    q = 0;
    r = 0;
    s = 1;

    while(1){
	/* assert(1 == p*s - r*q); */
	/* assert(a == y*r + x*p); */
	/* assert(b == x*q + y*s); */
	  
	vtrace1(x, y, a, b, p, r, q, s);
	
	if(!(a!=b)) break;
	  
	if (a > b) {
	    a = a - b; 
	    p = p - q; 
	    r = r - s;
	}
	else {
	    b = b - a; 
	    q = q - p; 
	    s = s - r;}
    }
    return a;
}


void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}


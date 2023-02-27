#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int x, int y, int a, int b, int p, int q){}    
void vtrace2(int x, int y, int a, int b, int p, int q){}

int mainQ(int x, int y){
    vassume(x>=1);
    vassume(y>=1); 

    int a,b,p,q;

    a = x;
    b = y;
    p = 1;
    q = 0;

    while(1) { 
	//assert(q+a*b*p==x*y);
	vtrace1(x, y, a, b, p, q);
	 
	if(!(a!=0 && b!=0)) break;
	  
	if (a % 2 ==0 && b % 2 ==0 ){
	    a = a/2;
	    b = b/2;
	    p = 4*p;
	}
	else if (a % 2 ==1 && b % 2 ==0 ){
	    a = a-1;
	    q = q+b*p;
	}
	else if (a % 2 ==0 && b % 2 ==1 ){
	    b = b-1;
	    q = q+a*p;
	}
	else {
	    a = a-1;
	    b = b-1;
	    q = q+(a+b+1)*p;
	}
    }

    //assert(q == x*y);
    vtrace2(x, y, a, b, p, q);	
    return q; 
}


void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}


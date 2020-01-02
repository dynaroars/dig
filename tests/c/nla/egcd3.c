#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtraces1(int a, int b, int y, int r, int x, int p, int q, int s){}
void vtraces2(int a, int b, int y, int r, int x, int p, int q, int s, int k, int c){}
void vtraces3(int a, int b, int y, int r, int x, int p, int q, int s, int d, int v, int k, int c){}
void vtraces4(int a, int b, int y, int r, int x, int p, int q, int s){}

int mainQ(int x, int y){
    vassume(x >= 1);
    vassume(y >= 1);
     
    int a,b,p,q,r,s;

    a=x; b=y;  p=1;  q=0;  r=0;   s=1;

    //assert(a==y*r+x*p); 
    //assert(b==x*q+y*s);

    while(1) {
	vtraces1(a, b, y, r, x, p, q, s);
	  
	if(!(b!=0)) break;
	int c,k;
	c=a;
	k=0;
	  
	while(1){
	    vtraces2(a, b, y, r, x, p, q, s, k, c);
	    
	    if(!(c>=b)) break;
	    int d,v;
	    d=1;
	    v=b;

	    while (1) {

		// assert(a == y*r+x*p); 
		// assert(b == x*q+y*s); 
		// assert(a == k*b+c); 
		// assert(v == b*d); 
		vtraces3(a, b, y, r, x, p, q, s, d, v, k, c);
		    
		if(!( c>= 2*v )) break;
		d = 2*d;
		v = 2*v;

	    }
	    c=c-v;
	    k=k+d;
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

    vtraces4(a, b, y, r, x, p, q, s);
    return a;
}


void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}


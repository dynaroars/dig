#include <stdio.h>
#include <assert.h>

int mainQ(int x, int y){
     assert(x >= 1);
     assert(y >= 1);
     
     int a,b,p,q,r,s;

     a=x; b=y;  p=1;  q=0;  r=0;   s=1;

     //assert(a==y*r+x*p); 
     //assert(b==x*q+y*s);

     while(1) {
	  //%%%traces: int a, int b, int y, int r, int x, int p, int q, int s
	  
	  if(!(b!=0)) break;
	  int c,k;
	  c=a;
	  k=0;
	  
	  while(1){
	       //%%%traces: int a, int b, int y, int r, int x, int p, int q, int s, int k, int c
	       if(!(c>=b)) break;
	       int d,v;
	       d=1;
	       v=b;

	       while (1) {

		    // assert(a == y*r+x*p); 
		    // assert(b == x*q+y*s); 
		    // assert(a == k*b+c); 
		    // assert(v == b*d); 
		    //%%%traces: int a, int b, int y, int r, int x, int p, int q, int s, int d, int v, int k, int c
		    
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
     return a;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}


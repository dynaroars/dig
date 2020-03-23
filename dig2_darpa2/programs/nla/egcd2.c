#include <stdio.h>
#include <assert.h>

int mainQ(int x, int y){
     assert(x>=1);
     assert(y>=1);
     
     int a,b,p,q,r,s;

     a=x;
     b=y;
     p=1;
     q=0;
     r=0; 
     s=1;

     while(1) {
	  //%%%traces: int a, int b, int p, int q, int r, int s, int x, int y
	  if(!(b!=0)) break;
	  int c,k;
	  c=a;
	  k=0;

	  while(1){
	       //assert(a == k*b+c);
	       //assert(a == y*r+x*p);
	       //assert(b == x*q+y*s);
	       //%%%traces: int a, int b, int c, int p, int q, int r, int s, int x, int y, int k
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

     return a;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}


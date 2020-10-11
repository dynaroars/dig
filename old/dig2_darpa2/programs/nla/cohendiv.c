#include <stdio.h>
#include <assert.h>
#include <stdlib.h>  //required for afloat to work

//http://www.cs.upc.edu/~erodri/webpage/polynomial_invariants/cohendiv.htm

int mainQ(int x, int y){
     //Cohen's integer division
     //returns x % y

     assert(x>0 && y>0);
  
     int q=0;
     int r=x;
     int a=0;
     int b=0;
     while(1) {
	  ////%%%traces: int x, int y, int q, int r
	  if(!(r>=y)) break;
	  a=1;
	  b=y;
	  
	  while (1){
	       //assert(r>=2*y*a && b==y*a && x==q*y+r && r>=0);
	       //%%%traces: int x, int y, int q, int a, int b, int r
	       if(!(r >= 2*b)) break;
	       
	       a = 2*a;
	       b = 2*b;
	  }
	  r=r-b;
	  q=q+a;
     }
     //assert(r == x % y);
     //assert(q == x / y);
     //assert(x == q*y+r);
     //%%%traces: int x, int y, int r, int q, int a, int b
     return q;
}

int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}


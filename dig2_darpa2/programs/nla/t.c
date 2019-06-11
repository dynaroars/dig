#include <stdio.h>
#include <assert.h>
#include <stdlib.h>  //required for afloat to work



int mainQ(int x, int y){
     assert(x>0 && y>0);
  
     int q=0;
     int r=x;

     while(1) {
	  ////%%%traces: int x, int y, int q, int r
	  if(!(r>=y)) break;
	  int a=1;
	  int b=y;
	  
	  while (1){
	       //assert(r>=2*y*a && b==y*a && x==q*y+r && r>=0);
	       ////%%%traces: int x, int y, int q, int a, int b, int r
	       if(!(r >= 2*b)) break;
	       
	       a = 2*a;
	       b = 2*b;
	  }
	  r=r-b;
	  q=q+a;
     }

     
     //%%%traces: int x, int y, int r, int q
     //// c1*x^k1 + c2*y^k2 + c3*r^k3  + c4*q^k4 + c5*x^k1'*y^*     .... + c0 = 0

     return q;
}

int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}


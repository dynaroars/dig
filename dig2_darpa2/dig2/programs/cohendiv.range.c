#include <stdio.h>
#include <assert.h>
#include <stdlib.h>  //required for afloat to work

int mainQ(int x, int y){
     //Cohen's integer division
     //returns x % y

     assert(x>0 && y>0);
  
     int q=0;
     int r=x;

     while(r>=y) {
	  int a=1;
	  int b=y;

	  while (r >= 2*b){
	       //assert(r>=2*y*a && b==y*a && x==q*y+r && r>=0);
	       //%%%traces: int a, int b, int r
	       a = 2*a;
	       b = 2*b;
	  }
	  r=r-b;
	  q=q+a;
     }
     return q;
}

int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}


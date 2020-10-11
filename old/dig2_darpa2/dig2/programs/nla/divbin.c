#include <stdio.h>
#include <assert.h>

int mainQ(int A, int B){
     assert(A > 0 && B > 0);
 
     int q = 0;
     int r = A;
     int b = B;

     while(1){
	  //%%%traces: int A, int B, int q, int b, int r
	  if (!(r>=b)) break;
	  b=2*b;
     }


     while(1){
	  //assert(A == q*b + r && r >= 0);
	  //%%%traces: int A, int B, int q, int b, int r
	  if (!(b!=B)) break;
	  
	  q = 2*q;
	  b = b/2;
	  if (r >= b) {
	       q = q + 1;
	       r = r - b;
	  }
     }
     return q;
}

int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}


#include <stdio.h>
#include <assert.h>
#include <stdlib.h>  //required for afloat to work


int mainQ(int A, int B){
  //hardware integer division program, by Manna
  //returns q==A//B

  assert(A >= 0);
  assert(B >= 1);

  int r,d,p,q;

  r=A;
  d=B;
  p=1;
  q=0;

  while(1){
    if (!(r >= d)) break;
    //%%%traces: int A, int B, int q, int r, int d, int p
    // A >= 0 && B > 0 && q == 0 && r == A && d == B*p
    d = 2 * d;
    p  = 2 * p;
  }

  while(1){
    if (!(p!=1)) break;
    //%%%traces: int A, int B, int q, int r, int d, int p    
    // A == q*B+r
    // d == B*p
    d=d/2;
    p=p/2;

    if(r>=d){
      r=r-d;
      q=q+p;
    }
  }

  ///%%%traces: int A, int r
  //, int q, int r, int d, int p
  // r == A % B
  // q == A / B
  return q;
}


int main(int argc, char **argv){
  mainQ(atoi(argv[1]), atoi(argv[2]));
  return 0;
}


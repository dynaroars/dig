#include <stdio.h>
#include <assert.h>
#include <math.h>
#include <stdlib.h>  //required for afloat to work

int mainQ(int n, int a){
  //algorithm searching for a divisor for factorization, by Knuth

  //%%%traces: int n, int a
  assert(a > 2);
  int r,k,q,d,s,t;
  d=a;
  r= n % d;
  t = 0;

  k=n % (d-2);
  q=4*(n/(d-2) - n/d);
  s=sqrt(n);

  while(1){
    //%%%traces: int n, int a, int r, int k, int q, int d, int s, int t
    if (!((s>=d)&&(r!=0))) break;

    if (2*r-k+q<0){
      t=r;
      r=2*r-k+q+d+2;
      k=t;
      q=q+4;
      d=d+2;
    } 
    else if ((2*r-k+q>=0)&&(2*r-k+q<d+2)){
      t=r;
      r=2*r-k+q;
      k=t;
      d=d+2;
    }
    else if ((2*r-k+q>=0)&&(2*r-k+q>=d+2)&&(2*r-k+q<2*d+4)){
      t=r;
      r=2*r-k+q-d-2;
      k=t;
      q=q-4;
      d=d+2;
    }
    else {/* ((2*r-k+q>=0)&&(2*r-k+q>=2*d+4)) */
      t=r;
      r=2*r-k+q-2*d-4;
      k=t;
      q=q-8;
      d=d+2;
    }

  }
  //%%%traces: int n, int a, int r, int k, int q, int d, int s, int t
  return d;
}


int main(int argc, char **argv){
  mainQ(atoi(argv[1]), atoi(argv[2]));
  return 0;
}


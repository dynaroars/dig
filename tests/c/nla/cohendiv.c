#include <stdio.h>
#include <assert.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int x, int y, int r, int q){}
void vtrace2(int x, int y, int r, int q, int a, int b){}
void vtrace3(int x, int y, int r, int q){}

int mainQ(int x, int y){
  vassume(x>0 && y>0);
  
  int q=0;
  int r=x;

  while(1) {
    vtrace1(x,y,q,r);
    if(!(r>=y)) break;
    int a=1;
    int b=y;
	  
    while (1){
      //assert(r>=2*y*a && b==y*a && x==q*y+r && r>=0);
      //%%%traces: int x, int y, int q, int a, int b, int r
      vtrace2(x,y,q,a,b,r);
      if(!(r >= 2*b))
	break;
	       
      a = 2*a;
      b = 2*b;
    }
    r=r-b;
    q=q+a;
  }
  //%%%traces: int x, int y, int r, int q
  vtrace3(x, y, r, q);
  return q;
}

void main(int argc, char **argv){
  mainQ(atoi(argv[1]), atoi(argv[2]));
}


#include <stdlib.h>
#include <stdio.h>

void vtrace2(float a, float x, float r){}
void vtrace1(float a, float x, float r){}


void mainQ(float a) {
  float x = a/2.0f;
  float r = 0;

  while(1){
      vtrace1(a,x,r);
      //assert((float)a == 2*x + r*r - r);
      if (!(x>r)) break;
      x = x - r;
      r = r + 1;
  }

  vtrace2(a,x,r);
  //assert((float)a == 2*x + r*r - r);
  //return r;
    }


void main(int argc, char *argv[]) {
    mainQ(atof(argv[1]));
}

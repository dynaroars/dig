#include <stdio.h>
#include <assert.h>
#include <stdlib.h>  //required for afloat to work

int mainQ(float a){

  float x = x=a/2.0;
  int r = 0;
  while(1){
    //%%%traces: float a, float x, int r
    if (!(x>r)) break;
    x = x - r; r = r + 1;
  }

  //assert(r==(int)round(sqrt(a)));
  return r;
}


int main(int argc, char **argv){
  mainQ(atof(argv[1]));
  return 0;
}


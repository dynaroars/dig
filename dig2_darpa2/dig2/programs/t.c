#include <stdio.h>
#include <assert.h>
#include <stdlib.h>  //required for afloat to work

void mainQ(int ix, int iy){
  int x = ix;
  int y = iy;
  if (x >= 7){
    //%%%traces: int x, int y
  }


  if(0){
    //%%%traces: int x, int y
  }
}

int main(int argc, char **argv){
  int ix=100 ;
  assert(-10000 <= ix && ix <= 10000);
  mainQ(atoi(argv[1]), atoi(argv[2]));
  return 0;
}


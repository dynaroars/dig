#include <stdio.h>
#include <assert.h>
#include <stdlib.h>  //required for afloat to work


int mainQ(int k){
  int y = 0;
  int x = 0;
  int c = 0;

  while(1){
    if (!(c < k)) break;
    //%%%traces: int x, int y, int k
    c = c +1 ;
    y=y +1;
    x=y*y+x;
  }
  return x;
}



int main(int argc, char **argv){
  mainQ(atoi(argv[1]));
  return 0;
}


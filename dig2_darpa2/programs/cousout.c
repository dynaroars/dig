#include <stdio.h>
#include <assert.h>
#include <stdlib.h>  //required for afloat to work

void mainQ(int iy){

  int x = 0;
  
  while (x < 10002){
    //%%%traces: int x
    x = x + 1;
  }
}

int main(int argc, char **argv){
  mainQ(atoi(argv[1]));
  return 0;
}


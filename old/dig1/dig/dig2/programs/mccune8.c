#include <stdio.h>
#include <assert.h>
#include <stdlib.h>  //required for afloat to work

void mainQ(int fake){

  int x = 0;
  while(1){
    //0 <= x <= 1
    //%%%traces: int x
    if (!((x <= 10))) break;
    x = 1-x;
  }
}

int main(int argc, char **argv){
  mainQ(atoi(argv[1]));
  return 0;
}


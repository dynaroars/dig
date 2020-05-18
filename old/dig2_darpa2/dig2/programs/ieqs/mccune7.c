#include <stdio.h>
#include <assert.h>
#include <stdlib.h>  //required for afloat to work

void mainQ(int fake){
  int x = 4; int y = 6;
  while (1){
    //−10 <= x − y <= 10
    //−11 <= x + y <= 10
    //−5 <= x <= 5
    //−5 <= y <= 6

    //%%%traces: int x, int y
    if(!(x+y >= 0)) break;
    if (y >= 6){x = -x; y = y-1;}
    else{x = -x; y = -y;}
  }
}

int main(int argc, char **argv){
  mainQ(atoi(argv[1]));
  return 0;
}


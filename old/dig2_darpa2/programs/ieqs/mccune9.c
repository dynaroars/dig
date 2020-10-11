#include <stdio.h>
#include <assert.h>
#include <stdlib.h>  //required for afloat to work

void mainQ(int fake){
  /*
    infinite loop

    loop invs:
    -5 <= x - y <= 10
    5 <= x + y <= 15
    0 <= x <= 10
    0 <= y <= 5 
   */
  int x = 0; int y = 5;
  while (1){
    if (x < 10 && y == 5){x = x+1;}
    else if (x = 10 && y > 0) {y = y-1;}
    else{
      while (y < 5){
	x = x-1; y = y+1;
      }
    }
  }
}

int main(int argc, char **argv){
  mainQ(atoi(argv[1]));
  return 0;
}


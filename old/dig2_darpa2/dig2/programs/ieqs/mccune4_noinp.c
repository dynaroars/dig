#include <stdio.h>
#include <assert.h>
#include <stdlib.h>  //required for afloat to work

void mainQ(){

  int x = 2 ; int y = 3 ;
  while (1){
    /*
      inv (from Mccune paper):  -5  <= x + y <= 7
     */
    //%%%traces: int x, int y      
    if (!(x+y >= 0)){
      break;
    }

    if (y >= 2) {
      y = -y + 4;
      x = -x + 3;
    }
    else{
      x = -x-3;
      y = -y+5;
    }
  }
}

int main(int argc, char **argv){
  mainQ();
  return 0;
}


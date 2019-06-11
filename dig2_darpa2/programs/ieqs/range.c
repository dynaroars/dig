#include <stdio.h>
#include <assert.h>
#include <stdlib.h>  //required for afloat to work

void mainQ(int ix, int iy){
  assert(ix >= 7);
  
  int x = ix;
  int y = iy;


  if (x == 4*y){
    //%%%traces: int y, int x
  }
  if(x >= 100){
    //%%%traces: int y, int x
    if (x == 3*y){
     //%%%traces: int y, int x
    }
    if (x <= 9913){
      //%%%traces: int y, int x
    }
    if (x >= 10002){
      //%%%traces: int y, int x
    }
    
  }

  if (0){
    //%%%traces: int y, int x
  }
}

int main(int argc, char **argv){
  mainQ(atoi(argv[1]), atoi(argv[2]));
  return 0;
}

